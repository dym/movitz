;;;; $Id: harddisk.lisp,v 1.4 2004/05/11 15:05:25 ffjeld Exp $

(require :lib/named-integers)

(provide :tmp/harddisk)

(defpackage muerte.x86-pc.harddisk
  (:use muerte.cl muerte muerte.lib muerte.x86-pc)
  (:export hdc-reset
           hd-identify-device
           hd-read-sectors
           hd-write-sectors))

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
;;; accessors
;;;

(defmacro data-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 0) :unsigned-byte16))

(defmacro features-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 1) :unsigned-byte8))

(defmacro error-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 1) :unsigned-byte8))

(defmacro sector-count-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 2) :unsigned-byte8))

(defmacro lba-low-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 3) :unsigned-byte8))

(defmacro lba-mid-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 4) :unsigned-byte8))

(defmacro lba-high-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 5) :unsigned-byte8))

(defmacro device-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 6) :unsigned-byte8))

(defmacro command-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 7) :unsigned-byte8))

(defmacro status-register (hdc)
  `(io-port (+ (slot-value ,hdc 'command-base) 7) :unsigned-byte8))

(defmacro alt-status-register (hdc)
  `(io-port (slot-value ,hdc 'control-base) :unsigned-byte8))

;;;
;;; getters
;;;
(defun reg-bsy (hdc)
  (get-bit 7 (status-register hdc)))

(defun reg-drdy (hdc)
  (get-bit 6 (status-register hdc)))

(defun reg-drq (hdc)
  (get-bit 3 (status-register hdc)))

(defun reg-err (hdc)
  (get-bit 0 (status-register hdc)))

(defun reg-alt-bsy (hdc)
  (get-bit 7 (alt-status-register hdc)))

(defun reg-alt-drdy (hdc)
  (get-bit 6 (alt-status-register hdc)))

(defun reg-alt-drq (hdc)
  (get-bit 3 (alt-status-register hdc)))

(defun reg-alt-err (hdc)
  (get-bit 3 (alt-status-register hdc)))

;;;
;;; setters
;;;
(defun set-drive-number (hdc drive)
  (set-bit 4 (/= drive 0) (device-register hdc)))

(defun set-intrq-mode (hdc mode)
  (set-bit 1 (not mode) (device-register hdc)))

(defun set-lba-mode (hdc mode)
  (set-bit 6 mode (device-register hdc)))

(defun set-lba-address (hdc lba)
  (setf (lba-low-register hdc) (ldb (byte 8 0) lba))
  (setf (lba-mid-register hdc) (ldb (byte 8 8) lba))
  (setf (lba-high-register hdc) (ldb (byte 8 16) lba))
  (setf (device-register hdc) (dpb (ldb (byte 4 24) lba)
                                   (byte 4 0)
                                   (device-register hdc))))

(defun set-lba-address-ext (hdc lba)
  (setf (lba-low-register hdc) (ldb (byte 8 0) lba))
  (setf (lba-mid-register hdc) (ldb (byte 8 8) lba))
  (setf (lba-high-register hdc) (ldb (byte 8 16) lba))

  ;; movitz byte function has a restriction, the location must be <= 30
  ;; therefore this workaround
  (setf (lba-low-register hdc) (ldb (byte 8 0) (ash lba -24)))
  (setf (lba-mid-register hdc) (ldb (byte 8 8) (ash lba -24)))
  (setf (lba-high-register hdc) (ldb (byte 8 16) (ash lba -24))))

(defun set-sector-count (hdc count)
  (setf (sector-count-register hdc) count))

(defun set-sector-count-ext (hdc count)
  (setf (sector-count-register hdc) (ldb (byte 8 0) count))
  (setf (sector-count-register hdc) (ldb (byte 8 8) count)))

(defun set-command (hdc command)
  (setf (command-register hdc) (case command
                                 ('identify-drive #xEC)
                                 ('read-sectors #x20)
                                 ('read-sectors-ext #x24)
                                 ('write-sectors #x30)
                                 ('write-sectors-ext #x34))))
          
;;;
;;; misc
;;;
(defun get-bit (number place)
  (/= 0 (ldb (byte 1 number) place)))

(defmacro set-bit (number value place)
  `(setf ,place (dpb (if ,value 1 0) (byte 1 ,number) ,place)))

(defmacro while (test &body body)
  `(do () ((not ,test))
    ,@body))

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
            (,hdc (aref *hd-controllers* (truncate ,hd-number 2)))
            (,drive-number (mod ,gs-hdnr 2)))
      ,@body)))

(defun error-code-meaning (code)
  (if (< 0 code 257)
      (nth (log2 code)
           '("Address Mark Not Found"
             "Track 0 Not Found"
             "Media Change Requested"
             "Aborted Command"
             "ID Not Found"
             "Media Changed"
             "Uncorrectable Data Error"
             "Bad Block Detected"))
      "No error"))
    
(defun hdc-error (hdc command-name hdnr)
  (puts "In HDC error")
  (error "Harddrive command ~A returned error. HD number: ~A. Error message: '~A'." 
         command-name hdnr 
         (error-code-meaning 
          (io-port (error-register hdc) :unsigned-byte8))))

(defun puts (s)
  (fresh-line)
  (format t s)
  (terpri))

;;;
;;; hd operations
;;;
(defun hdc-reset (hdcnr)
  "Reset the harddisk controller. Must be done at startup to
initialize the harddisk controller."
  ;; set SRST
  ;; wait > 2ms
  ;; continue when BSY=0
  (let ((hdc (aref *hd-controllers* hdcnr)))
    (setf (device-register hdc) #x04)
    (loop for x from 1 to 2500)
    (loop while (reg-bsy hdc))))

(defun hd-identify-device (hdnr)
  "Get device information of hdnr. Returns a (vector 256 (unsigned-byte 16))."
  (let ((data (make-array 256 :element-type :unsigned-byte16))
        (offset 0))
    (with-hd-info (hdc drive) hdnr
      (tagbody
        ;; drive must be ready
        ;; drive number must be set
        ;; intrq's must not be used
        ;; LBA mode must be on
        ;; LBA must be set
        ;; sector-count must be set
        ;; command must be entered
        ;; 400 nsec must be waited before checking BSY
        (loop until (reg-drdy hdc))
        (loop while (reg-alt-bsy hdc))
        (set-drive-number hdc drive)
        (set-intrq-mode hdc nil)
        (set-command hdc 'identify-drive)
        (dotimes (x 500))              ;aught to be enough waiting
        (go :check-status)
        ;;;;;;;;;;;;;;;;;;
        :check-status
        ;; if BSY=0 and DRQ=0 then error
        ;; if BSY=0 and DRQ=1 then go transfer-data
        ;; if BSY=1 then go check-state
        (let ((status (status-register hdc)))
          (if (get-bit 7 status)       ;if BSY = 1
              (go :check-status)
              (if (get-bit 3 status)   ;if DRQ = 1
                  (go :transfer-data)
                  (progn
                    (hdc-error hdc "identify-device" hdnr)))))
        ;;;;;;;;;;;;;;;;;;
        :transfer-data
        ;; read the data register
        (setf (aref data offset) (data-register hdc))
        (incf offset)
        ;; read the status register to determine if we're done
        (if (reg-drq hdc)
            (if (< offset 256)
                (go :transfer-data)     ;data block not completely transfered
                (go :check-status))
            (return-from hd-identify-device data))))))

(defun hd-read-sectors (hdnr start-sector count)
  "Read count sectors from hdnr, starting at start-sector. Returns a (vector (* count 512) (unsigned-byte 8)). If start-sector doesn't fit into 28 bits or count doesn't fit into 8 bits an attempt is made to use 48 bits addressing."
  (let ((data (make-array (* count 512) :element-type :unsigned-byte8))
        (offset 0)
        (ext-mode (or (>= start-sector #xFFFFFFF)
                      (>= count #xFF)))
        input)
    (with-hd-info (hdc drive) hdnr
      (tagbody
;        (puts "in entry")
        ;; drive must be ready
        ;; drive number must be set
        ;; intrq's must not be used
        ;; LBA mode must be on
        ;; LBA must be set
        ;; sector-count must be set
        ;; command must be entered
        ;; 400 nsec must be waited before checking BSY
        (loop until (reg-drdy hdc))
        (loop while (reg-alt-bsy hdc))
        (set-drive-number hdc drive)
        (set-intrq-mode hdc nil)
        (set-lba-mode hdc t)
        (if ext-mode
           (progn
             (puts "using 48 bits addressing")
             (set-lba-address-ext hdc start-sector)
             (set-sector-count-ext hdc count)
             (set-command hdc 'read-sectors-ext))
           (progn
             (puts "using 28 bits addressing")
             (set-lba-address hdc start-sector)
             (set-sector-count hdc count)
             (set-command hdc 'read-sectors)))
        (set-lba-address hdc start-sector)
        (set-sector-count hdc count)
        (set-command hdc 'read-sectors)
        (dotimes (x 500))              ;aught to be enough waiting
        (go :check-status)
        ;;;;;;;;;;;;;;;;;;
        :check-status
;        (puts "in check-status")
        ;; if BSY=0 and DRQ=0 then error
        ;; if BSY=0 and DRQ=1 then go transfer-data
        ;; if BSY=1 then go check-state
        (let ((status (status-register hdc)))
          (if (get-bit 7 status)       ;if BSY = 1
              (go :check-status)
              (if (get-bit 3 status)   ;if DRQ = 1
                  (go :transfer-data)
                  (progn
                    (hdc-error hdc "read-sectors" hdnr)))))
        ;;;;;;;;;;;;;;;;;;
        :transfer-data
;        (puts "in transfer-data")        
        ;; read the data register
        (setf input (data-register hdc))
        (setf (aref data offset) (ldb (byte 8 0) input))
        (incf offset)
        (setf (aref data offset) (ldb (byte 8 8) input))
        (incf offset)
        ;; read the status register to determine if we're done
        (if (reg-drq hdc)
            (if (/= 0 (mod offset 512))
                (go :transfer-data)     ;data block not completely transfered
                (progn
                  (alt-status-register hdc) ;read and ignore
                  (go :check-status)))
            (return-from hd-read-sectors data))))))

(defun hd-write-sectors (hdnr start-sector data)
  (check-type hdnr (integer 0 *))
  (check-type start-sector (integer 0 *))
  (check-type data vector)
  (let* ((count (truncate (length data) 512))
         (ext-mode (or (>= start-sector #xFFFFFFF)
                       (>= count #xFF)))
         (offset 0))
    (with-hd-info (hdc drive) hdnr
      (tagbody
;        (puts "in entry")
        ;; drive must be ready
        ;; drive number must be set
        ;; intrq's must not be used
        ;; LBA mode must be on
        ;; LBA must be set
        ;; sector-count must be set
        ;; command must be entered
        ;; 400 nsec must be waited before checking BSY
        (loop until (reg-drdy hdc))
        (loop while (reg-alt-bsy hdc))
        (set-drive-number hdc drive)
        (set-intrq-mode hdc nil)
        (set-lba-mode hdc t)
        (if ext-mode                    
            (progn
              (puts "using 48 bits addressing")
              (set-lba-address-ext hdc start-sector)
              (set-sector-count-ext hdc count)
              (set-command hdc 'write-sectors-ext))
            (progn
              (puts "using 28 bits addressing")
              (set-lba-address hdc start-sector)
              (set-sector-count hdc count)
              (set-command hdc 'write-sectors)))
        (set-lba-address hdc start-sector)
        (set-sector-count hdc count)
        (set-command hdc 'write-sectors)
        (dotimes (x 500))              ;aught to be enough waiting
        (go :check-status)
        ;;;;;;;;;;;;;;;;;;
        :check-status
;        (puts "in check-status")
        ;; if BSY=0 and DRQ=0 then error
        ;; if BSY=0 and DRQ=1 then go transfer-data
        ;; if BSY=1 then go 
        (let ((status (status-register hdc)))
          (if (get-bit 7 status)       ;if BSY = 1
              (go :check-status)
              (if (get-bit 3 status)   ;if DRQ = 1
                  (go :transfer-data)
                  (hdc-error hdc "write-sectors" hdnr))))
        ;;;;;;;;;;;;;;;;;;
        :transfer-data
;        (puts "in transfer-data")
        ;; read the data register
        (setf (data-register hdc) (+ (aref data offset)
                                     (ash (aref data (1+ offset)) 8)))
        (incf offset 2)
        ;; read the status register to determine if we're done
        (if (reg-drq hdc)
            (if (/= 0 (mod offset 512))
                (go :transfer-data)     ;data block not completely transfered
                (progn
                  (alt-status-register hdc) ;read and ignore
                  (go :check-status)))
            (return-from hd-write-sectors nil))))))