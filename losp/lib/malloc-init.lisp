;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      malloc-init.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Jan  9 15:57:22 2002
;;;;                
;;;; $Id: malloc-init.lisp,v 1.2 2004/01/19 11:23:44 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/malloc-init :load-priority 200)

(in-package muerte.lib)

(let ((memsize (muerte.x86-pc::memory-size))
      (start (truncate (* 1 1024 1024) 4096)))
  ;; (format t "Memory: ~D MB.~%" memsize)
  (muerte:malloc-initialize start (- (* memsize #x100) start)))


