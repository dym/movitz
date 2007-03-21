;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      equalp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Mar 13 17:09:08 2001
;;;;                
;;;; $Id: equalp.lisp,v 1.8 2007/03/21 21:54:12 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/integers)
(require :muerte/typep)
(provide :muerte/equalp)

(in-package muerte)

(defun eql (x y)
  (compiler-macro-call eql x y))

(defun equal (x y)
  (typecase x
    (symbol
     (eq x y))
    (string
     (and (stringp y)
	  (string= x y)))
    (number
     (eql x y))
    (cons
     (when (consp y)
       (do ()
           ((not (equal (pop x) (pop y)))
            nil)
         (when (or (not (consp x))
                   (not (consp y)))
           (return (equal x y))))))
    (bit-vector
     (when (typep y 'bit-vector)
       (not (mismatch x y))))
    (t (eq x y))))

(defun equalp (x y)
  (typecase x
    (character
     (and (characterp y)
	  (char-equal x y)))
    (cons
     (and (consp y)
	  (equalp (car x) (car y))
	  (equalp (cdr x) (cdr y))))
    (vector
     (and (typep y 'vector)
	  (let ((length (length x)))
	    (and (= length (length y))
		 (do ((i 0 (1+ i)))
		     ((= i length) t)
		   (declare (index i))
		   (unless (equalp (aref x i) (aref y i))
		     (return nil)))))))
    (structure-object
     (and (eq (class-of x) (class-of y))
	  (dotimes (i (structure-object-length x) t)
	    (unless (equalp (structure-ref x i)
			    (structure-ref y i))
	      (return nil)))))
    (t (equal x y))))
