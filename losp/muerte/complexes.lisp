;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Description:   Complex numbers
;;;; Author:        Frode Vatvedt Fjeld
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: complexes.lisp,v 1.3 2008-07-09 20:17:46 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/defstruct)

(in-package muerte)

(provide :muerte/complexes)

(defstruct (complex (:constructor make-complex-number)
		    (:conc-name #:||)
		    (:predicate complexp))
  realpart
  imagpart)

(defun complex (realpart &optional (imagpart 0))
  (check-type realpart real)
  (check-type imagpart real)
  (if (= 0 imagpart)
      realpart
      (make-complex-number :realpart realpart
                           :imagpart imagpart)))
