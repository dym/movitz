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
;;;; $Id: malloc-init.lisp,v 1.4 2004/07/07 17:37:11 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/malloc-init :load-priority 200)

(in-package muerte.lib)

(let* ((stack-vector (%run-time-context-slot 'muerte::stack-vector))
       (kernel-end (+ (* 4 (muerte:object-location stack-vector))
		      8 (* 4 (array-dimension stack-vector 0))))
       (memsize (muerte.x86-pc::memory-size))
       (start (truncate (+ kernel-end 4095) 4096)))
  (muerte:malloc-initialize start (- (* memsize #x100) start))
  (loop for x from (truncate kernel-end 4) below (* start 1024)
      do (setf (memref x 0 0 :unsigned-byte32) 0))
  ;; (format t "Memory: ~D MB. Malloc area at ~D K.~%" memsize (* start 4))
  (values))


