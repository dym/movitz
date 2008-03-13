;;;; Movitz ATA Hard Drive Driver
;;;; --------------------------------------------------------------------------
;;;; [13 Mar 2008]  Martin Bealby
;;;;   Moved into muerte.x86-pc.ata package
;;;;   'ata' prefix removed from function names
;;;; [23 Feb 2008]  Martin Bealby
;;;;   Partition reading and parsing functions added
;;;;   Read / write sector functions converted to work with lists of bytes
;;;; [25 Oct 2007]  Martin Bealby
;;;;   Rewritten from scratch based on http://www.osdever.net/tutorials/lba.php
;;;; --------------------------------------------------------------------------


;;;; --------------------------------------------------------------------------
;;;; Package Setup
;;;; --------------------------------------------------------------------------
(require :x86-pc/package)

(defpackage muerte.x86-pc.ata
  (:use muerte.cl muerte.lib muerte)
  (:export #:read-partition-table
		   #:get-partition-data
		   #:partition-active-p
		   #:partition-type
		   #:partition-start-offset
		   #:partition-size
		   #:lba-read-sector
		   #:lba-write-sector))

(provide :x86-pc/ata)

(in-package muerte.x86-pc.ata)


;;;; --------------------------------------------------------------------------
;;;; Constants
;;;; --------------------------------------------------------------------------
(defconstant +controller0+ #x1F0)
(defconstant +controller1+ #x170)

(defconstant +offset-data+ 0)
(defconstant +offset-error-precomp+ 1)
(defconstant +offset-sector-count+ 2)
(defconstant +offset-lba1+ 3)
(defconstant +offset-lba2+ 4)
(defconstant +offset-lba3+ 5)
(defconstant +offset-drive-head+ 6)
(defconstant +offset-status-command+ 7)


(defconstant +command-read+ #x20)
(defconstant +command-write+ #x30)
(defconstant +bitflag-busy+ 7)


(defparameter *partitions* '((nil nil nil nil) ; controller 1 disc 1
								 (nil nil nil nil) ; controller 1 disc 2
								 (nil nil nil nil) ; controller 2 disc 1
								 (nil nil nil nil))) ; controller 2 disc 2


;;;; --------------------------------------------------------------------------
;;;; Drive Functions
;;;; --------------------------------------------------------------------------
(defun busy-wait (controller)
  "ATA Driver busy spin loop."
  (loop while (logbitp +bitflag-busy+
					   (io-port (+ controller
								   +offset-status-command+)
								:unsigned-byte8))))

(defun send-command (controller command)
  "Send a command to an IDE controller."
  (setf (io-port (+ controller +offset-status-command+) :unsigned-byte8)
		command))

(defun lba-read-write-common (controller drive-number block-address)
  (if (= 0 block-address)
	  (error "Sector zero is not a valid index for LBA addressing."))
  ;; send a null
  (setf (io-port (+ controller
					+offset-error-precomp+) :unsigned-byte8) 0)
  ;; send a sector count 
  (setf (io-port (+ controller
					+offset-sector-count+):unsigned-byte8) 1)
  ;; send the lowest 8 bits of the lba
  (setf (io-port (+ controller +offset-lba1+) :unsigned-byte8)
		(logand block-address #xFF))
  ;; send the next 8 bits
  (setf (io-port (+ controller +offset-lba2+) :unsigned-byte8)
		(ash (logand block-address #xFF00)
			 -8))
  ;; send the next 8 bits
  (setf (io-port (+ controller +offset-lba3+) :unsigned-byte8)
		(ash (logand block-address #xFF0000)
			 -16))
  ;; send the last 4 bits and some magic bits
  (setf (io-port (+ controller +offset-drive-head+) :unsigned-byte8)
		(logand
		 (logior (ash (logand block-address #xF000000)
					  -24)
				 #xE0  ;; magic 
				 (ash drive-number 4))
		 #x0F)))


(defun lba-read-sector (controller drive-number block-address)
  "Reads a specified sector of data from the disk."
  ;; Call common initialisation
  (lba-read-write-common controller drive-number block-address)
  ;; send read command
  (send-command controller +command-read+)
  ;; wait for the drive
  (busy-wait controller)
  ;; read the data
  (loop for position from 0 to 255
	 for data = (io-port (+ controller +offset-data+)
						   :unsigned-byte16)
     collect (logand #x00FF data)
	 collect (ash (logand #xFF00 data) -8)))


(defun lba-write-sector (controller drive-number block-address data)
  "Writes data to a sector of the disk."
  ;; data must be a list of 512 unsigned-byte8's
  ;; based upon lba-read-sector-above
  (lba-read-write-common controller drive-number block-address)
  (send-command controller +command-write+)
  (busy-wait controller)
  (loop for position from 0 to 511 by 2
	 do (setf (io-port (+ controller +offset-data+) :unsigned-byte16)
			  (+ (ash (nth position data) 8)
				 (nth (+ 1 position) data)))))


;;;; --------------------------------------------------------------------------
;;;; Partition Functions
;;;; --------------------------------------------------------------------------
(defun read-partition-table (controller drive-number)
  "Reads and stores the partition table from the specified disk."
  (cond ((> controller 1)			; assume 2 controllers for now
		 (error "Invalid controller number.")))
  (cond ((> drive-number 1)				; assume 2 drives per controller for now
		 (error "Invalid driver number.")))

  (let ((sector
		  (cond ((= 0 controller)
				 (lba-read-sector +controller0+ drive-number 1))
				((= 1 controller)
				 (lba-read-sector +controller1+ drive-number 1)))))
	(setf (nth (+ controller drive-number) *partitions*)
		  (list (loop for offset from 446 to 461
				   collect (nth offset sector))
				(loop for offset from 462 to 477
				   collect (nth offset sector))
				(loop for offset from 478 to 493
				   collect (nth offset sector))
				(loop for offset from 494 to 509
				   collect (nth offset sector))))))

(defun get-partition-data (controller drive-number partition)
  "Returns the partition data for the specified controller and drive from the local cache.
   The data can be supplied to:
      partition-active-p
      partition-type
      partition-start-offset
      partition-size"
  (cond ((> controller 1)			; assume 2 controllers for now
		 (error "Invalid controller number.")))
  (cond ((> drive-number 1)				; assume 2 drives per controller for now
		 (error "Invalid driver number.")))
  (cond ((> partition 3)				; max 4 partitions per drive (no extended partitions for now)
		 (error "Invalid partition number.")))
  (nth partition
	   (nth (+ controller drive-number) *partitions*)))

(defun partition-active-p (partition-data)
  "Returns the state of the active flag for the partition."
  (cond ((= #x80 (nth 0 partition-data))
		 t)
		(t nil)))

(defun partition-type (partition-data)
  "Returns the partition type for the partition."
  (let ((id (nth 4 partition-data)))
	(cond ((= #x00 id)
		   "EMPTY")
		  ((= #x06 id)
		   "FAT16")
		  ((= #x07 id)
		   "NTFS")
		  ((= #x0b id)
		   "FAT32")
		  ((= #x0c id)
		   "FAT32-LBA")
		  ((= #x0e id)
		   "FAT16-LBA")
		  ((= #x82 id)
		   "LINUX-SWAP")
		  ((= #x83 id)
		   "LINUX")
		  ((= #xA5 id)
		   "FREEBSD")
		  ((= #xA6 id)
		   "OPENBSD")
		  ((= #xA9 id)
		   "NETBSD")
		  ((= #xE8 id)
		   "LUKS")
		  (t
		   "UNKNOWN"))))

(defun partition-start-offset (partition-data)
  "Returns the starting offset (LBA) for the partition."
  (+ (nth 8 partition-data)
	 (ash (nth 9 partition-data)
		  8)
	 (ash (nth 10 partition-data)
		  16)
	 (ash (nth 11 partition-data)
		  24)))

(defun partition-size (partition-data)
  "Returns the size of the partition."
  (+ (nth 12 partition-data)
	 (ash (nth 13 partition-data)
		  8)
	 (ash (nth 14 partition-data)
		  16)
	 (ash (nth 15 partition-data)
		  24)))

