;;;; bochs-vbe.lisp
;;;; Support for the bochs/qemu video bios extensions

;;;; Martin Bealby 2007

(require :x86-pc/package)
(provide :x86-pc/bochs-vbe)

(in-package muerte.x86-pc)

;;
;; Port constants
;;
(defconstant +bochs-vbe-ioport-index+ #x01ce)
(defconstant +bochs-vbe-ioport-data+ #x01cf)

;;
;; Register constants
;;
(defconstant +bochs-vbe-index-id+ #x0)
(defconstant +bochs-vbe-index-width+ #x1)
(defconstant +bochs-vbe-index-height+ #x2)
(defconstant +bochs-vbe-index-bits-per-pixel+ #x3)
(defconstant +bochs-vbe-index-enable+ #x4)
(defconstant +bochs-vbe-index-bank+ #x5)
(defconstant +bochs-vbe-index-virtual-width+ #x6)
(defconstant +bochs-vbe-index-virtual-height+ #x7)
(defconstant +bochs-vbe-index-x-offset+ #x8)
(defconstant +bochs-vbe-index-y-offset+ #x9)

;;
;; Command constants
;;
(defconstant +bochs-vbe-command-disable+ #x00)
(defconstant +bochs-vbe-command-enable+ #x01)
(defconstant +bochs-vbe-command-getcaps+ #x02)
(defconstant +bochs-vbe-command-8bit-dac+ #x20)
(defconstant +bochs-vbe-command-linear-framebuffer+ #x40)
(defconstant +bochs-vbe-command-noclearmem+ #x80)


;;
;; Parameters
;;
(defvar *bochs-vbe-framebuffer-width* 0)
(defvar *bochs-vbe-framebuffer-height* 0)
(defvar *bochs-vbe-framebuffer-bits-per-pixel* 0)

;;
;; Support functions
;;
(defun bochs-vbe-write-to-ports (index value)
  "Writes to the Bochs VBE ports."
  (setf (io-port +bochs-vbe-ioport-index+ :unsigned-byte16) index)
  (setf (io-port +bochs-vbe-ioport-data+ :unsigned-byte16) value))


;;
;; Interface functions
;;
(defun bochs-vbe-set-video-mode (width height bits-per-pixel)
  "Sets the video mode to the specified parameters."
  (bochs-vbe-write-to-ports +bochs-vbe-index-enable+
			    +bochs-vbe-command-disable+)
  (bochs-vbe-write-to-ports +bochs-vbe-index-width+
			    width)
  (bochs-vbe-write-to-ports +bochs-vbe-index-height+
			    height)
  (bochs-vbe-write-to-ports +bochs-vbe-index-bits-per-pixel+
			    bits-per-pixel)
  (bochs-vbe-write-to-ports +bochs-vbe-index-enable+
			    (logior +bochs-vbe-command-enable+
				    +bochs-vbe-command-linear-framebuffer+))
  (setf *bochs-vbe-framebuffer-width* width)
  (setf *bochs-vbe-framebuffer-height* height)
  (setf *bochs-vbe-framebuffer-bits-per-pixel* bits-per-pixel))

(defun bochs-vbe-get-framebuffer-address ()
  "Returns the address of the framebuffer."
  #xe0000000)
