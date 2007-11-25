;;;; Movitz Common Graphics Functions
;;;; --------------------------------------------------------------------------
;;;; [25 Nov 2007]  Martin Bealby
;;;;   Package modifications
;;;; [24 Nov 2007]  Martin Bealby
;;;;   Initial Version
;;;; --------------------------------------------------------------------------


;;;; --------------------------------------------------------------------------
;;;; Package Setup
;;;; --------------------------------------------------------------------------
(require :lib/package)

(defpackage #:muerte.graphics
  (:use #:common-lisp #:muerte)
  (:export #:color-pack
		   #:graphics-surface
		   #:make-graphics-surface
		   #:copy-graphics-surface))

(provide :lib/graphics)

(in-package muerte.graphics)


;;;; --------------------------------------------------------------------------
;;;; Structures
;;;; --------------------------------------------------------------------------
(defstruct graphics-surface width height bit-depth memory-pointer)


;;;; --------------------------------------------------------------------------
;;;; Functions
;;;; --------------------------------------------------------------------------
(defun color-pack (bpp red green blue alpha)
  (cond ((= 8 bpp)
		 (error "Color packing not supported in palletised modes."))
		((= 16 bpp)
		 ; Is actually 15bpp, but is packed into a 2 byte value
		 ; 15 bpp ignores the 3 least significant bits of each color
		 (return-from color-pack (+ (ash (logand red 248) 11)
									(ash (logand green 248) 5)
									(logand blue 248))))
		
		((= 24 bpp)
		 (return-from color-pack (+ (ash red 16)
									(ash green 8)
									blue)))
		((= 32 bpp)
		 (return-from color-pack (+ (ash red 24)
									(ash green 16)
									(ash blue 8)
									alpha)))))