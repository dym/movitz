;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      package.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Sep 27 17:24:11 2002
;;;;                
;;;; $Id: package.lisp,v 1.1 2004/01/13 11:05:04 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage muerte.lib
  (:use muerte.cl)
  (:export *scroll-offset*
	   cursor-x cursor-y
	   console-width console-height
	   console-char
	   scroll-down
	   clear-line
	   local-echo-p
	   with-saved-excursion))

(provide :lib/package)

(in-package muerte.lib)

(defvar *scroll-offset* 0)
