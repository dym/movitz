;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      bcd.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep 30 14:03:57 2002
;;;;                
;;;; $Id: bcd.lisp,v 1.1 2004/01/13 11:05:04 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :lib/bcd)

(defpackage muerte.lib
  (:export bcd-to-integer
	   integer-to-bcd))

(in-package muerte.lib)

(defun bcd-to-integer (bcd)
  (loop for factor = 1 then (* factor 10)
      while (plusp bcd)
      sum (* factor (ldb (byte 4 0) bcd))
      do (setf bcd (ash bcd -4))))

(defun integer-to-bcd (integer)
  (loop for factor = 1 then (* factor 16)
      while (plusp integer)
      sum (* factor (rem integer 10))
      do (setf integer (truncate integer 10))))
