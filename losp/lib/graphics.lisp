;;;; Movitz Common Graphics Functions
;;;; --------------------------------------------------------------------------
;;;; [26 Nov 2007]  Martin Bealby
;;;;   Generalised fallback software rendering functions added
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
		   #:copy-graphics-surface
		   #:pixel
		   #:line
		   #:circle))

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


;;;;---------------------------------------------------------------------------
;;;; Fallback software rendering functions
;;;;---------------------------------------------------------------------------
(defun (setf pixel) (color surface x y)
  "Fallback software pixel set routine."
  (cond
	((>= 0 x)
	 (error "X co-ordinate below zero."))
	((>= 0 y)
	 (error "Y co-ordinate below zero."))
	((>= x (graphics-surface-width surface))
	 (error "X co-ordinate too large for surface."))
	((>= y (graphics-surface-width surface))
	 (error "Y co-ordinate too large for surface."))
	(t (cond ((= 8 (graphics-surface-bit-depth surface))
			  (setf (memref-int (graphics-surface-memory-pointer surface)
								:index (+ x
										  (* (graphics-surface-width surface)
											 y))
								:type :unsigned-byte8)
					color))
			 (( = 16 (graphics-surface-bit-depth surface))
			  (setf (memref-int (graphics-surface-memory-pointer surface)
								:index (+ (* 2 x)
										  (* 2 (graphics-surface-width surface)
											 y))
								:type :unsigned-byte16)
					color))
			 ((= 24 (graphics-surface-bit-depth surface))
			  (setf (memref-int (graphics-surface-memory-pointer surface)
								:index (+ (* 3 x)
										  (* 3 (graphics-surface-width surface)
											 y))

								:type :unsigned-byte24);:unsigned-byte24 doesn't exist
					color))
			 ((= 32 (graphics-surface-bit-depth surface))
			  (setf (memref-int (graphics-surface-memory-pointer surface)
								:index (+ (* 4 x)
										  (* 4 (graphics-surface-width surface)
											 y))
								:type :unsigned-byte32)
					color))))))


(defun pixel (surface x y)
  "Fallback software pixel read routine."
  (cond
	((>= 0 x)
	 (error "X co-ordinate below zero."))
	((>= 0 y)
	 (error "Y co-ordinate below zero."))
	((>= x (graphics-surface-width surface))
	 (error "X co-ordinate too large for surface."))
	((>= y (graphics-surface-width surface))
	 (error "Y co-ordinate too large for surface."))
	(t (cond ((= 8 (graphics-surface-bit-depth surface))
			  (return-from pixel (memref-int (graphics-surface-memory-pointer surface)
											 :index (+ x
													   (* (graphics-surface-width surface)
														  y))
											 :type :unsigned-byte8)))
			 ((= 16 (graphics-surface-bit-depth surface))
			  (return-from pixel (memref-int (graphics-surface-memory-pointer surface)
											 :index (+ (* 2 x)
													   (* 2 (graphics-surface-width surface)
														  y))
											 :type :unsigned-byte16)))
			 ((= 24 (graphics-surface-bit-depth surface))
			  (return-from pixel (memref-int (graphics-surface-memory-pointer surface)
											 :index (+ (* 3 x)
													   (* 3 (graphics-surface-width surface)
														  y))
											 :type :unsigned-byte24)))
			 ((= 32 (graphics-surface-bit-depth surface))
			  (return-from pixel (memref-int (graphics-surface-memory-pointer surface)
											 :index (+ (* 4 x)
													   (* 4 (graphics-surface-width surface)
														  y))
											 :type :unsigned-byte32)))))))

