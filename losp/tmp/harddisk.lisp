;;;; $Id: harddisk.lisp,v 1.2 2004/04/24 15:13:26 ffjeld Exp $

(require :lib/named-integers)
(provide :tmp/harddisk)

(defpackage muerte.x86-pc.harddisk
  (:use muerte.cl muerte muerte.lib muerte.x86-pc)
  (:export make-512-vector
           hd-read-sectors
           hd-write-sectors
           hd-commands
	   ))

(in-package muerte.x86-pc.harddisk)

;;;
;;; global variables
;;;
(defvar *hd-controllers* (vector (make-instance 'hd-controller))
  "A vector of harddisk controllers.")

;;;
;;; constants
;;;
(defconstant +hd-default-first-irq+ 14)
(defconstant +hd-default-second-irq+ 15)
(defconstant +hd-default-first-command-base+ #x1F0)
(defconstant +hd-default-second-command-base+ #x170)
(defconstant +hd-default-first-control-base+ #x3F6)
(defconstant +hd-default-second-control-base+ #x376)

(define-named-integer hd-register-offset 
    (:only-constants t)
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
    (:only-constants t)
  (#x20 read-sectors-with-retry)
  (#x30 write-sectors-with-retry))

(define-named-integer hd-status-bits
    (:only-constants t)
  (0 error)
  (1 index)
  (2 corrected-data)
  (3 data-request)
  (4 drive-seek-complete)
  (5 drive-write-fault)
  (6 drive-ready)
  (7 busy))

;;;
;;; classes
;;;
(defclass hd-controller ()
  ((command-base :initform +hd-default-first-command-base+
                 :initarg :command-base
                 :type integer)
   (control-base :initform +hd-default-first-control-base+
                 :initarg :command-base
                 :type integer)))

;;;
;;; waiters
;;;
(defun hd-controller-wait-for-drive-ready (hdc) ;wait for DRDY=1
  (with-slots (control-base) hdc
    (loop until (/= 0 (logand (io-port control-base :unsigned-byte8)
                              #x40)))))  

(defun hd-controller-wait-for-ready (hdc) ;wait for BSY=0
  (with-slots (control-base) hdc
    (loop until (= 0 (logand (io-port control-base :unsigned-byte8)
                             #x80)))))

(defun hd-controller-wait-for-data-request (hdc) ;wait for DRQ=1
  (with-slots (control-base) hdc
    (loop until (/= 0 (logand (io-port control-base :unsigned-byte8)
                              #x08)))))

;;;
;;; feeders
;;;
(defun hd-controller-feed-lba-mode (hdc)
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-4)
                 :unsigned-byte8)
          (logior (io-port (hd-controller-command-register hdc 'lba-byte-4)
                           :unsigned-byte8)
                  #b01000000)))

(defun hd-controller-feed-drive (hdc drive)
  (setf (io-port (hd-controller-command-register hdc 'lba-byte-4)
                 :unsigned-byte8)
          (logior (* #b00010000 drive)
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
;;; misc
;;;
(defmacro while (test &body body)
  `(do () ((not ,test))
    ,@body))

(defun div (a b)
  "Floored integer division, the painful way."
  (let ((r 0)
        (x a))
    (while (>= x 0)
      (decf x b)
      (incf r))
    (1- r)))

(defun log2 (n)
  (cond ((= n 256) 8)
        ((= n 128) 7)
        ((= n 64) 6)
        ((= n 32) 5)
        ((= n 16) 4)
        ((= n 8) 3)
        ((= n 4) 2)
        ((= n 2) 1)
        ((= n 1) 0)))
        
(defmacro with-hd-info ((hdc drive-number) hd-number &body body)
  (let ((gs-hdnr (gensym "hd-number-")))
    `(let* ((,gs-hdnr ,hd-number)
            (,hdc (aref *hd-controllers* (div ,hd-number 2)))
            (,drive-number (mod ,gs-hdnr 2)))
      ,@body)))

(defun hd-controller-command-register (hdc name)
  ;; use a case statement for now, until I learn how to use
  ;; named-integer right
  (+ (case name
       ('data 0)
       ('error 1)
       ('features 1)
       ('sector-count 2)
       ('lba-byte-1 3)
       ('lba-byte-2 4)
       ('lba-byte-3 5)
       ('lba-byte-4 6)
       ('status 7)
       ('command 7)
       (else (error "HD command register not found ~A" name)))
     (slot-value hdc 'command-base)))

(defun error-code-meaning (code)
  (nth (log2 code)
       '("Address Mark Not Found"
         "Track 0 Not Found"
         "Media Change Requested"
         "Aborted Command"
         "ID Not Found"
         "Media Changed"
         "Uncorrectable Data Error"
         "Bad Block Detected")))
    
    
(defun hd-check-error (hdc command-name hdnr)
  "Check and when found signal an error in task."
  (when (/= 0 (logand (io-port (slot-value hdc 'control-base)
                               :unsigned-byte8)
                      #x01))
    (error "Harddrive command ~A returned error. HD number: ~A. Error message: '~A'." 
           command-name hdnr 
           (error-code-meaning 
            (io-port (hd-controller-command-register hdc 'error)
                     :unsigned-byte8)))))

;;;
;;; hd operations
;;;
(defun hd-read-sectors (hdnr start-sector count)
  (let ((data (make-array 512 :element-type :unsigned-byte8))
        (offset 0)
        (read-data nil))
    (with-hd-info (hdc drive) hdnr
      ;; set drive
      (hd-controller-feed-drive hdc drive)
      ;; set count
      (setf (io-port (hd-controller-command-register hdc 'sector-count)
                     :unsigned-byte8)
              count)
      ;; set LBA and address
      (hd-controller-feed-lba-mode hdc)
      (hd-controller-feed-lba-address hdc start-sector)
      ;; get going
      (setf (io-port (hd-controller-command-register hdc 'command)
                     :unsigned-byte8)
              +hd-commands-read-sectors-with-retry+)
      ;; data handling
      (while (<= offset (* count 512))
        (hd-controller-wait-for-drive-ready hdc)
        (hd-controller-wait-for-ready hdc)
        (hd-check-error hdc "read-sectors" hdnr)
        (hd-controller-wait-for-data-request hdc)
        (dotimes (i 256)
          (setf read-data (io-port (hd-controller-command-register hdc 'status)
                                   :unsigned-byte16)))
          (setf (aref data offset) (logand read-data #xFF))
          (setf (aref data (1+ offset)) (logand read-data #xFF00))              
          (incf offset 2))
      ;; done
      data)))

(defun hd-write-sectors (hdnr start-sector data)
  (let ((offset 0)
        (write-data nil)
        (count (div (length data) 512)))
    (with-hd-info (hdc drive) hdnr
      ;; set drive
      (hd-controller-feed-drive hdc drive)
      ;; set count
      (setf (io-port (hd-controller-command-register hdc 'sector-count)
                     :unsigned-byte8)
              count)
      ;; set LBA and address
      (hd-controller-feed-lba-mode hdc)
      (hd-controller-feed-lba-address hdc start-sector)
      ;; get going
      (setf (io-port (hd-controller-command-register hdc 'command)
                     :unsigned-byte8)
              +hd-commands-write-sectors-with-retry+)
      ;; data handling
      (while (<= offset (* count 512))
        (hd-controller-wait-for-drive-ready hdc)
        (hd-controller-wait-for-ready hdc)
        (hd-check-error hdc "write-sectors" hdnr)
        (hd-controller-wait-for-data-request hdc)
        (dotimes (i 256)
          (setf write-data (aref data offset))
          (incf write-data (* #xFF (aref data (1+ offset))))
          (setf (io-port (hd-controller-command-register hdc 'data)
                         :unsigned-byte16)
                  write-data)
          (incf offset 2))))))