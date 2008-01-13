;;;; Movitz Common Graphics Functions
;;;; --------------------------------------------------------------------------
;;;; [26 Nov 2007]  Martin Bealby
;;;;   Uncomment code
;;;; [25 Nov 2007]  Martin Bealby
;;;;   Package modifications
;;;; [23 Nov 2007]  Martin Bealby
;;;;   Code refactoring.  Integration with lib/graphics
;;;; [XX Jul 2007]  Martin Bealby
;;;;   Initial Version
;;;; --------------------------------------------------------------------------

;;;; --------------------------------------------------------------------------
;;;; Package Setup
;;;; --------------------------------------------------------------------------
(require :x86-pc/package)
(require :lib/graphics)


(defpackage muerte.x86-pc.bochs-vbe
  (:use muerte.cl muerte.lib muerte muerte.graphics)
  (:export #:set-video-mode
		   #:get-surface))


(provide :x86-pc/bochs-vbe)

(in-package muerte.x86-pc.bochs-vbe)


;;;; --------------------------------------------------------------------------
;;;; Port constants
;;;; --------------------------------------------------------------------------
(defconstant +bochs-vbe-ioport-index+ #x01ce)
(defconstant +bochs-vbe-ioport-data+ #x01cf)


;;;; --------------------------------------------------------------------------
;;;; Register constants
;;;; --------------------------------------------------------------------------
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

;;;; --------------------------------------------------------------------------
;;;; Command constants
;;;; --------------------------------------------------------------------------
(defconstant +bochs-vbe-command-disable+ #x00)
(defconstant +bochs-vbe-command-enable+ #x01)
(defconstant +bochs-vbe-command-getcaps+ #x02)
(defconstant +bochs-vbe-command-8bit-dac+ #x20)
(defconstant +bochs-vbe-command-linear-framebuffer+ #x40)
(defconstant +bochs-vbe-command-noclearmem+ #x80)


;;;; --------------------------------------------------------------------------
;;;; Parameters
;;;; --------------------------------------------------------------------------
(defvar *bochs-vbe-surface* 0)


;;;; --------------------------------------------------------------------------
;;;; Support functions
;;;; --------------------------------------------------------------------------
(defun write-to-ports (index value)
  "Writes to the Bochs VBE ports."
  (setf (io-port +bochs-vbe-ioport-index+ :unsigned-byte16) index)
  (setf (io-port +bochs-vbe-ioport-data+ :unsigned-byte16) value))


;;;; --------------------------------------------------------------------------
;;;; Interface functions
;;;; --------------------------------------------------------------------------
(defun set-video-mode (width height bits-per-pixel)
  "Sets the video mode to the specified parameters."
  (write-to-ports +bochs-vbe-index-enable+
				  +bochs-vbe-command-disable+)
  (write-to-ports +bochs-vbe-index-width+
				  width)
  (write-to-ports +bochs-vbe-index-height+
				  height)
  (write-to-ports +bochs-vbe-index-bits-per-pixel+
				  bits-per-pixel)
  (write-to-ports +bochs-vbe-index-enable+
				  (logior +bochs-vbe-command-enable+
						  +bochs-vbe-command-linear-framebuffer+))
  (setf *bochs-vbe-surface*
		(muerte.graphics:make-graphics-surface :width width
											   :height height
											   :bit-depth bits-per-pixel
											   :memory-pointer #xe0000000)))

(defun get-surface ()
  "Returns the framebuffer surface."
  *bochs-vbe-surface*)
