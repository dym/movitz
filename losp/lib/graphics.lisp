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
	((>= 0 x))
	((>= 0 y))
	((<= x (width surface)))
	((<= y (width surface)))
	(t (cond ((= 8 (bit-depth surface))
			  (setf (memref-int (memory-pointer surface)
								:index (+ x
										  (* (width surface)
											 y))
								:type :unsigned-byte8)
					color))
			 (( = 16 (bit-depth surface))
			  (setf (memref-int (memory-pointer surface)
								:index (+ (* 2 x)
										  (* 2 (width surface)
											 y))
								:type :unsigned-byte16)
					color))
			 ((= 24 (bit-depth surface))
			  (setf (memref-int (memory-pointer surface)
								:index (+ (* 3 x)
										  (* 3 (width surface)
											 y))
								:type :unsigned-byte24)
					color))
			 ((= 32 (bit-depth surface))
			  (setf (memref-int (memory-pointer surface)
								:index (+ (* 4 x)
										  (* 4 (width surface)
											 y))
								:type :unsigned-byte32)
					color))))))


(defun pixel (surface x y)
  "Fallback software pixel read routine."
  (cond
	((>= 0 x))
	((>= 0 y))
	((<= x (width surface)))
	((<= y (width surface)))
	(t (cond ((= 8 (bit-depth surface))
			  (return-from pixel (memref-int (memory-pointer surface)
											 :index (+ x
													   (* (width surface)
														  y))
											 :type :unsigned-byte8)))
			 ((= 16 (bit-depth surface))
			  (return-from pixel (memref-int (memory-pointer surface)
											 :index (+ (* 2 x)
													   (* 2 (width surface)
														  y))
											 :type :unsigned-byte16)))
			 ((= 24 (bit-depth surface))
			  (return-from pixel (memref-int (memory-pointer surface)
											 :index (+ (* 3 x)
													   (* 3 (width surface)
														  y))
											 :type :unsigned-byte24)))
			 ((= 32 (bit-depth surface))
			  (return-from pixel (memref-int (memory-pointer surface)
											 :index (+ (* 4 x)
													   (* 4 (width surface)
														  y))
											 :type :unsigned-byte32)))))))



;; draw-line from ch-image
;; originally written by Cyrus Harmon
;; modified for movitz by Martin Bealby
(defun line (surface x0 y0 x1 y1 color)
  (let ((dx (- x1 x0))
        (dy (- y1 y0)))
    (declare (type fixnum dx dy))
    (let ((absdx (abs dx))
          (absdy (abs dy)))
      (declare (type fixnum absdx absdy))
      (let ((xstep (if (minusp dx) -1 1))
            (ystep (if (minusp dy) -1 1)))
        (if (>= absdx absdy)
            (let ((d (- (* 2 absdy) absdx))
                  (incr-e (* 2 absdy))
                  (incr-ne (* 2 (- absdy absdx)))
                  (x x0)
                  (y y0))
              (declare (type fixnum d incr-e incr-ne x y))
              (setf (pixel surface y x) color)
              (dotimes (i absdx)
                (cond
                  ((<= d 0)
                   (incf d incr-e)
                   (incf x xstep))
                  (t
                   (incf d incr-ne)
                   (incf x xstep)
                   (incf y ystep)))
                (setf (pixel surface y x) color)))
            (let ((d (- (* 2 absdy) absdx))
                  (incr-n (* 2 absdx))
                  (incr-ne (* 2 (- absdx absdy)))
                  (x x0)
                  (y y0))
              (declare (type fixnum d incr-n incr-ne x y))
              (setf (pixel surface y x) color)
              (dotimes (i absdy)
                (cond
                  ((<= d 0)
                   (incf d incr-n)
                   (incf y ystep))
                  (t
                   (incf d incr-ne)
                   (incf y ystep)
                   (incf x xstep)))
                (setf (pixel surface y x) color))))))))


;; draw-circle from ch-image
;; originally written by Cyrus Harmon
;; modified for movitz by Martin Bealby
(defmethod circle (surface center-y center-x radius color)
  (declare (type fixnum center-y center-x radius))
  (flet ((circle-points (y x color)
           (setf (pixel surface (+ center-y y) (+ center-x x)) color) 
           (setf (pixel surface (+ center-y x) (+ center-x y)) color) 
           (setf (pixel surface (- center-y x) (+ center-x y)) color) 
           (setf (pixel surface (- center-y y) (+ center-x x)) color) 
           (setf (pixel surface (- center-y y) (- center-x x)) color) 
           (setf (pixel surface (- center-y x) (- center-x y)) color) 
           (setf (pixel surface (+ center-y x) (- center-x y)) color) 
           (setf (pixel surface (+ center-y y) (- center-x x)) color)))
    (let ((x 0)
          (y radius)p
          (d (- 1 radius))
          (delta-e 3)
          (delta-se (+ (* -2 radius) 5)))
      (declare (type fixnum x y d delta-e delta-se))
      (circle-points y x color)
      (do () ((>= x y))
        (if (< d 0)
            (progn
              (incf d delta-e)
              (incf delta-e 2)
              (incf delta-se 2))
            (progn
              (incf d delta-se)
              (incf delta-e 2)
              (incf delta-se 4)
              (decf y)))
        (incf x)
        (circle-points y x color)))))