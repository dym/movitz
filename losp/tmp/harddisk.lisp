;;;; $Id: harddisk.lisp,v 1.1 2004/04/19 22:55:55 ffjeld Exp $

(require :lib/named-integers)

(provide :x86-pc/harddisk)

(in-package muerte.x86-pc)

;;;
;;; constants
;;;
(defconstant +hd-default-first-irq+ 14)
(defconstant +hd-default-second-irq+ 15)
(defconstant +hd-default-first-command-base+ #x1F0)
(defconstant +hd-default-second-command-base+ #x170)
(defconstant +hd-default-first-control-base+ #x3F6)
(defconstant +hd-default-second-control-base+ #x376)

;;;
;;; structures
;;;

(defstruct hd-controller             
  (number 0 :type integer)              ;for error messages
  (command-base +hd-default-first-command-base+ :type (integer 0 *))
  (control-base +hd-default-first-control-base+ :type (integer 0 *))
  (active-hd 0 :type hd)                ;hd with pending task
  (master nil :type hd)
  (slave nil :type hd))

(defstruct hd
  ;; hd info
  (place 0 :type bit)                   ;0=master,1=slave
  (cylinders 0 :type (integer 0 *))
  (heads 0 :type (integer 0 *))
  (spt 0 :type (integer 0 *))
  (sector-1-lba 0 :type (integer 0 *))
  ;; task stuff
  (tasks (make-hash-table) :type hash-table)
  (pending-tasks '() :type list)
  (pending-last-cons '() :type cons)    ;speeds append up
  (active-task nil :type hd-task)
  (done-tasks '() :type list))

(deftype hd-data-vector ()
  '(vector (unsigned-byte 8)))

(defstruct hd-read-sectors-task
  (start-sector 0 :type (unsigned-byte 28))
  (count 1 :type (integer 1 256))
  (data #() :type data-vector)
  (offset 0 :type (integer 0 *)))

(defstruct hd-write-sectors-task
  (start-sector 0 :type (unsigned-byte 28))
  (count 1 :type (integer 1 256))
  (data #() :type data-vector)
  (offset 0 :type (integer 0 *)))

;;;
;;; low level code
;;;

(define-named-integer hd-register-offset 
    (:only-constants t :export-constants t)
  (0 data)
  (1 error)                            
  (1 features)
  (2 sector-count)
  (3 lba-byte-1)                        ;bits 0-7
  (4 lba-byte-2)                        ;bits 8-15
  (5 lba-byte-3)                        ;bits 16-23
  (6 lba-byte-4)                        ;bits 24-27
  (7 status)
  (7 command))

(define-named-integer hd-commands
    (:only-constants t :export-constants t)
  (#x20 read-sectors-with-retry)
  (#x30 write-sectors-with-retry))

(defun hd-controller-command-register (hdc name type)
  (+ (named-integer 'hd-register-offset name)
     (hd-controller-command-base hdc)))

(define-named-integer hd-status-bits
    (:only-constants t :export-constants t)
  (0 error)
  (1 index)
  (2 corrected-data)
  (3 data-request)
  (4 drive-seek-complete)
  (5 drive-write-fault)
  (6 drive-ready)
  (7 busy))

(defun hd-controller-busy (hdc)
  ;; use control base, not command base, to avoid side effects
  (/= 0 (logand (io-port (hd-controller-control-base hdc)
                         :unsigned-byte8)
                #x80)))

(defun hd-controller-wait-for-ready (hdc)    ;wait for BSY=0
  (do () ((not (hd-controller-busy))) ()))

(defun hd-controller-status (hdc code)
  (named-integer 'hd-status-bits code))

(defmacro define-hd-controller-interrupt-handler (hdc irq)
  (let ((name (gensym "hdc-irq-handler-")))
    `(progn
      (defun ,name (number int-frame)
        (declare (ignore (number int-frame)))
        (let ((hdc ,hdc))
          (if (hd-controller-handle-task-signal hdc)
            (hd-controller-queue-next-task hdc))))
      (setf (interrupt-handler ,irq) ,name))))

(defgeneric hd-controller-handle-task-signal (hdc task))

(defmethod hd-controller-handle-task-signal :before (hdc task)
  (hd-controller-wait-for-ready hdc))   ;just in case

(defmethod hd-controller-handle-task-signal (hdc (task hd-read-sectors-task))
  (with-slots (count data offset) task
    (let ((status (io-port (hd-controller-command-register hdc 'status)
                           :unsigned-byte8))
          (read-data (io-port (hd-controller-command-register hdc 'status)
                              :unsigned-byte16)))
      ;; by now the drive is getting the next piece, if necessary,
      ;; so I hope this code is reentrant
      (if (= 0 (logand (power 2 (hd-controller-status 'error))
                       status))
        (progn 
          ;; read 512 bytes
          (dotimes (i 256)
            (setf (aref data offset) (logand read-data #xFF))
            (setf (aref data (1+ offset)) (logand read-data #xFF00))              
            (incf offset 2))
          (= offset (1- (* count 512)))) ;return value, are we done or not?
        (error "Harddrive read-sectors returned error. Controller nr ~A, HD number:
~A, error register: ~A." 
               (hd-controller-number hdc)
               (hd-controller-active-hd hdc)
               (io-port (hd-controller-command-register hdc 'error)
                        :unsigned-byte8))))))

(defmethod hd-controller-handle-task-signal (hdc (task hd-write-sectors-task))
  (with-slots (count data offset) task
    (let ((status (io-port (hd-controller-command-register hdc 'status)
                           :unsigned-byte8))
          (write-data nil))
      (if (= 0 (logand (power 2 (hd-controller-status 'error))
                       status))
        (if (= 0 (logand (power 2 (hd-controller-status 'data-request))
                       status))
          ;; write 512 bytes
          (progn
            (dotimes (i 256)
              ;; hope the byte order is correct
              (setf write-data (aref data offset))
              (incf write-data (* #xFF (aref data (1+ offset))))
              (incf offset 2)
              (setf (io-port (hd-controller-command-register hdc 'data)
                             :unsigned-byte16)
                      write-data))
            nil)                        ;not done yet
          t)                            ;no data requested, so done
        (error "Harddrive read-sectors returned error. Controller nr ~A, HD number:
~A, error register: ~A." 
               (hd-controller-number hdc)
               (hd-controller-active-hd hdc)
               (io-port (hd-controller-command-register hdc 'error)
                        :unsigned-byte8))))))


(defmethod hd-controller-feed-task :before (hdc task)
  (hd-controller-wait-for-ready hdc)
  ;; we always use LBA mode
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-4)
                 :unsigned-byte8)
          (logior (io-port (hd-controller-command-register hdc 'lba-byte-4)
                           :unsigned-byte8)
                  #b01000000)))

(defmethod hd-controller-feed-task (hdc (task hd-read-sectors-task))
  (with-slots (drive count start-sector) task
    ;; set drive
    (hd-controller-feed-drive hdc drive)
    ;; set count
    (setf (io-port (hd-controller-command-register hdc 'sector-count)
                   :unsigned-byte8)
            count)
    ;; set address
    (hd-controller-feed-lba-address start-sector)
    ;; get going
    (setf (io-port (hd-controller-command-register hdc 'command)
                   :unsigned-byte8)
            (named-integer 'hd-commands 'read-sectors-with-retry))))

(defmethod hd-controller-feed-task (hdc (task hd-write-sectors-task))
  (with-slots (count start-sector offset data) task
    ;; set drive
    (hd-controller-feed-drive hdc)
    ;; set count
    (setf (io-port (hd-controller-command-register hdc 'sector-count)
                   :unsigned-byte8)
            count)
    ;; set address
    (hd-controller-feed-lba-address start-sector)
    ;; get going
    (setf (io-port (hd-controller-command-register hdc 'command)
                   :unsigned-byte8)
            (named-integer 'hd-commands 'read-sectors-with-retry))))
  

(defun hd-controller-feed-drive (hdc)
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-4)
                 :unsigned-byte8)
          (logior (* #b00010000 (hd-controller-active-hd hdc))
                  (logand (io-port (hd-controller-command-register hdc 'lba-byte-4)
                                   :unsigned-byte8)
                          #b11101111))))

(defun hd-controller-feed-lba-address (hdc lba)
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-1)
                 :unsigned-byte8)
          (logand lba #x000000FF))
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-2)
                 :unsigned-byte8)
          (logand lba #x0000FF00))
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-3)
                               :unsigned-byte8)
          (logand lba #x00FF0000))
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-3)
                 :unsigned-byte8)
          (logior (io-port (hd-controller-command-register hdc 'lba-byte-4)
                           :unsigned-byte8)
                  (logand lba #x000F0000))))

;;;
;;; scheduler code
;;;
(defun hd-queue-next-task (hdc)
  ;; very dumb scheduler, FIFO and master before slave
  (labels ((queue (hd)
             (let ((task (first (hd-pending-tasks hd))))
               (setf (hd-active-task hd) task)
               (unless (rest (hd-pending-tasks hd))
                 (setf (hd-pending-last-cons hd)
                         (hd-pending-tasks hd)))
               (hd-controller-feed-task hdc task))))
    (let ((master (hd-controller-master hdc))
          (slave (hd-controller-slave hdc)))
      (cond ((> 0 (length (hd-pending-tasks master)))
              (queue master)
              (setf (hd-controller-active-hd hdc) 0))
            ((> 0 (length (hd-pending-tasks slave)))
              (queue slave)
              (setf (hd-controller-active-hd hdc) 1))))))


(defun hd-add-read-sectors-task (hd start-sector count)
  "Add a task to read count sectors, starting at start-sector. Count
must be between 1 and 256 inclusive."
  (let* ((task (make-hd-read-sectors-task :start-sector start-sector
                                          :count (mod (count 256))))
                         
         (pending-cons (cons task nil)))
    (rplacd (hd-pending-last-cons hd) pending-cons)
    (setf (hd-pending-last-cons hd) pending-cons)))

(defun hd-add-write-sectors-task (hd start-sector count data)
  "Add a task to write count sectors of data, starting at
start-sector. Count must be between 1 and 256 inclusive."
  (let* ((task (make-hd-read-sectors-task :start-sector start-sector
                                          :count (mod (count 256))
                                          :data data))
         (pending-cons (cons task nil)))
    (rplacd (hd-pending-last-cons hd) pending-cons)
    (setf (hd-pending-last-cons hd) pending-cons)))