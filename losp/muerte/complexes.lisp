;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Description:   Complex numbers
;;;; Author:        Frode Vatvedt Fjeld
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: complexes.lisp,v 1.2 2008-04-21 19:31:32 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/defstruct)

(in-package muerte)

(provide :muerte/complexes)

(defstruct (complex (:constructor make-complex-number)
		    (:conc-name #:||))
  realpart
  imagpart)

(defun complex (realpart &optional (imagpart 0))
  (check-type realpart real)
  (check-type imagpart real)
  (if (= 0 imagpart)
      realpart
      (make-complex-number :realpart realpart
                           :imagpart imagpart)))
