;;;
;;; floppy.lisp
;;;
;;; First-cut floppy driver
;;;

(provide :x86-pc/floppy)

(in-package muerte.x86-pc)

;;;
;;; At this time, this driver is only capable of spinning up the drive motor
;;; and seeking to different tracks on a 1.44M 3.5" HD disk.
;;;
;;; In order to use the driver, do:
;;;
;;; (setf *package* (find-package "X86-PC.FLOPPY")) to switch to this package.
;;;
;;; (fd-start-disk) to initialize the controller and spin the drive up.
;;;
;;; (fd-seek 70) to seek to track 70.
;;;
;;; (setf (fd-motor) nil) to turn the drive and controller off.
;;;
;;; Variations on this theme include: seeking to different tracks.
;;;

;; I/O port locations

(defconstant +fd-main-status-register+ #x3f4)
(defconstant +fd-data-register+ #x3f5)
(defconstant +fd-digital-output-register+ #x3f2)
(defconstant +fd-that-other-register+ #x3f7)


;; Basic accessors

(defun fd-status ()
  (io-port +fd-main-status-register+ :unsigned-byte8))

(defun fd-data ()
  (io-port +fd-data-register+ :unsigned-byte8))

(defun (setf fd-data) (value)
  (setf (io-port +fd-data-register+ :unsigned-byte8) value))

(defun (setf fd-dor) (value)
  (setf (io-port +fd-digital-output-register+ :unsigned-byte8) value))


;; Fundamental operations

(defun (setf fd-motor) (value)
  (if (null value)
      (setf (fd-dor) 0)
    (progn
      ;; FIXME: Should delay after this setf for motor to come up to speed.
      (setf (fd-dor) #x1c))))

(defun fd-wait-ready ()
  "Returns #x40 if fdc is expecting a read next."
  (loop for status = (fd-status)
      when (not (zerop (logand #x80 status)))
      return (logand #x40 status)))

(defun fd-write-data (value)
  (unless (zerop (fd-wait-ready))
    (error "FDC expecting read when we want to write."))
  (setf (fd-data) value))

(defun fd-read-data ()
  (when (zerop (fd-wait-ready))
    (error "FDC expecting write when we want to read."))
  (fd-data))


;; Basic commands

(defun fd-cmd-specify (byte1 byte2)
  (fd-write-data #x03)
  (fd-write-data byte1)
  (fd-write-data byte2))

(defun fd-cmd-sense-interrupt-status ()
  (let ((dsr0)
	(cylinder)
	(status))
    (loop doing (fd-write-data 8)
	  (setf dsr0 (fd-read-data))
	  (setf status (fd-wait-ready))
	  until (not (zerop status)))
    (setf cylinder (fd-read-data))
    (values dsr0 cylinder)))

(defun fd-cmd-recalibrate ()
  (fd-write-data 7)
  (fd-write-data 0)
  (fd-cmd-sense-interrupt-status))

(defun fd-cmd-seek (cylinder)
  (fd-write-data #xf)
  (fd-write-data 0)
  (fd-write-data cylinder)
  (fd-cmd-sense-interrupt-status))

(defun fd-initialize-controller ()
  (setf (fd-motor) nil)
  (setf (io-port +fd-that-other-register+ :unsigned-byte8) 0)
  (setf (fd-dor) #xc)
  (fd-cmd-specify #xdf #x02))

(defun fd-start-disk ()
  (fd-initialize-controller)
  (dotimes (i 4)
    (fd-cmd-sense-interrupt-status))
  (setf (fd-motor) t)
  (fd-cmd-recalibrate))

;;; EOF
