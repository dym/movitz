;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Description:   Complex numbers
;;;; Author:        Frode Vatvedt Fjeld
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: complexes.lisp,v 1.4 2009-07-19 18:52:08 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/defstruct)

(in-package muerte)

(provide :muerte/complexes)

(defstruct (complex (:constructor make-complex (realpart imagpart))
		    (:predicate complexp))
  realpart
  imagpart)

(defun complex (realpart &optional (imagpart 0))
  (check-type realpart real)
  (check-type imagpart real)
  (if (= 0 imagpart)
      realpart
      (make-complex realpart imagpart)))

(defmethod print-object ((x complex) stream)
  (format stream "#c(~W ~W)"
          (complex-realpart x)
          (complex-imagpart x)))

(defun realpart (x)
  (etypecase x
    (complex
     (complex-realpart x))
    (real
     x)))

(defun imagpart (x)
  (etypecase x
    (complex
     (complex-imagpart x))
    (real
     0)))
