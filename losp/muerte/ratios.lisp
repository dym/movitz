;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ratios.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Jul 20 00:39:59 2004
;;;;                
;;;; $Id: ratios.lisp,v 1.5 2004/07/31 23:35:09 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/arithmetic-macros)
(require :muerte/defstruct)
(provide :muerte/ratios)

(in-package muerte)

;;;(defstruct (ratio (:constructor make-ratio (numerator denominator))
;;;	    (:superclass rational))
;;;  numerator denominator)

(defun make-ratio (numerator denominator)
  (check-type numerator integer)
  (check-type denominator (integer 1 *))
  (let ((ratio (malloc-pointer-words 4)))
    (setf (memref ratio #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte32)
      #.(movitz:tag :ratio))
    (setf (memref ratio -6 2 :lisp) numerator
	  (memref ratio -6 3 :lisp) denominator)
    ratio))

(defun ratio-p (x)
  (typep x 'ratio))

(define-compiler-macro %ratio-numerator (x)
  `(memref ,x ,(bt:slot-offset 'movitz::movitz-ratio 'movitz::numerator) 0 :lisp))

(defun ratio-numerator (x)
  (check-type x ratio)
  (%ratio-numerator x))

(define-compiler-macro %ratio-denominator (x)
  `(memref ,x ,(bt:slot-offset 'movitz::movitz-ratio 'movitz::denominator) 0 :lisp))

(defun ratio-denominator (x)
  (check-type x ratio)
  (%ratio-denominator x))

(defun make-rational (numerator denominator)
  (check-type numerator integer)
  (check-type denominator integer)
  (cond
   ((= 1 denominator)
    numerator)
   ((minusp denominator)
    (make-rational (- numerator) (- denominator)))
   ((= 0 denominator)
    (error 'division-by-zero))
   (t (let ((gcd (gcd numerator denominator)))
	(if (= denominator gcd)
	    (values (truncate numerator denominator))
	  (make-ratio (truncate numerator gcd)
		      (truncate denominator gcd)))))))

(defun numerator (x)
  (etypecase x
    (integer x)
    (ratio (%ratio-numerator x))))

(defun denominator (x)
  (etypecase x
    (integer 1)
    (ratio (%ratio-denominator x))))

(defconstant pi #xea7632a/4aa1a8b)
