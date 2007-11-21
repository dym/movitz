;;;; Movitz ATA Hard Drive Driver
;;;; --------------------------------------------------------------------------
;;;; [25 Oct 2007]  Martin Bealby
;;;;   Rewritten from scratch based on http://www.osdever.net/tutorials/lba.php
;;;; --------------------------------------------------------------------------


;;;; --------------------------------------------------------------------------
;;;; Package Setup
;;;; --------------------------------------------------------------------------
(require :x86-pc/package)
(provide :x86-pc/ata)

(in-package muerte.x86-pc)


;;;; --------------------------------------------------------------------------
;;;; Constants
;;;; --------------------------------------------------------------------------
(defconstant +ata-controller0+ #x1F0)
(defconstant +ata-controller1+ #x170)

(defconstant +ata-offset-data+ 0)
(defconstant +ata-offset-error-precomp+ 1)
(defconstant +ata-offset-sector-count+ 2)
(defconstant +ata-offset-lba1+ 3)
(defconstant +ata-offset-lba2+ 4)
(defconstant +ata-offset-lba3+ 5)
(defconstant +ata-offset-drive-head+ 6)
(defconstant +ata-offset-status-command+ 7)


(defconstant +ata-command-read+ #x20)
(defconstant +ata-command-write+ #x30)
(defconstant +ata-bitflag-busy+ 7)


;;;; --------------------------------------------------------------------------
;;;; Functions
;;;; --------------------------------------------------------------------------
(defun ata-busy-wait (ata-controller)
  "ATA Driver busy spin loop."
  (loop while (logbitp +ata-bitflag-busy+
					   (io-port (+ ata-controller
								   +ata-offset-status-command+)
								:unsigned-byte8))))

(defun ata-send-command (ata-controller command)
  "Send a command to an IDE controller."
  (setf (io-port (+ ata-controller +ata-offset-status-command+) :unsigned-byte8)
		command))

(defun ata-lba-read-write-common (ata-controller drive-number block-address)
  ;; send a null
  (setf (io-port (+ ata-controller
					+ata-offset-error-precomp+) :unsigned-byte8) 0)
  ;; send a sector count 
  (setf (io-port (+ ata-controller
					+ata-offset-sector-count+):unsigned-byte8) 1)
  ;; send the lowest 8 bits of the lba
  (setf (io-port (+ ata-controller +ata-offset-lba1+) :unsigned-byte8)
		(logand block-address #xFF))
  ;; send the next 8 bits
  (setf (io-port (+ ata-controller +ata-offset-lba2+) :unsigned-byte8)
		(ash (logand block-address #xFF00)
			 -8))
  ;; send the next 8 bits
  (setf (io-port (+ ata-controller +ata-offset-lba3+) :unsigned-byte8)
		(ash (logand block-address #xFF0000)
			 -16))
  ;; send the last 4 bits and some magic bits
  (setf (io-port (+ ata-controller +ata-offset-drive-head+) :unsigned-byte8)
		(logand
		 (logior (ash (logand block-address #xF000000)
					  -24)
				 #xE0  ;; magic 
				 (ash drive-number 4))
		 #x0F)))

(defun ata-lba-read-sector (ata-controller drive-number block-address)
  "Reads a specified sector of data from the disk."
  ;; Call common initialisation
  (ata-lba-read-write-common ata-controller drive-number block-address)
  ;; send read command
  (ata-send-command ata-controller +ata-command-read+)
  ;; wait for the drive
  (ata-busy-wait ata-controller)
  ;; read the data
  (loop for position from 0 to 255
	   for data = (io-port (+ ata-controller +ata-offset-data+)
						   :unsigned-byte16)
	   collect data))


(defun ata-lba-write-sector (ata-controller drive-number block-address data)
  "Writes data to a sector of the disk."
  ;; data must be a list of 256 unsigned-byte16's
  ;; based upon ata-lba-read-sector-above
  (ata-lba-read-write-common ata-controller drive-number block-address)
  (ata-send-command ata-controller +ata-command-write+)
  (ata-busy-wait ata-controller)
  (loop for position from 0 to 255
	 do (setf (io-port (+ ata-controller +ata-offset-data+) :unsigned-byte16)
			  (nth position data))))