;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      equalp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Mar 13 17:09:08 2001
;;;;                
;;;; $Id: equalp.lisp,v 1.2 2004/01/19 11:23:46 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/integers)
(require :muerte/typep)
(provide :muerte/equalp)

(in-package muerte)

(defun eql (x y)
  (eql x y))

(defun equal (x y)
  (typecase x
    (string
     (and (stringp y)
	  (string= x y)))
    (symbol
     (eq x y))
    (number
     (and (numberp y)
	  (= x y)))
    (cons
     (and (consp y)
	  (equal (car x) (car y))
	  (equal (cdr x) (cdr y))))
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
		   (unless (equalp (aref x i) (aref y i))
		     (return nil)))))))
    (t (equal x y))))
