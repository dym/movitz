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
;;;; $Id: malloc-init.lisp,v 1.3 2004/06/09 23:00:57 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/malloc-init :load-priority 200)

(in-package muerte.lib)

(let ((memsize (muerte.x86-pc::memory-size))
      (start (truncate (* 2 1024 1024) 4096))) ; XXX We really should calcucalte this..
  ;; (format t "Memory: ~D MB.~%" memsize)
  (muerte:malloc-initialize start (- (* memsize #x100) start)))


