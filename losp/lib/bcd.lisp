;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      bcd.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep 30 14:03:57 2002
;;;;                
;;;; $Id: bcd.lisp,v 1.3 2004/01/19 11:23:44 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/bcd)

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
