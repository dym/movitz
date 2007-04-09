;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      malloc-init.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Jan  9 15:57:22 2002
;;;;                
;;;; $Id: malloc-init.lisp,v 1.8 2007/04/09 16:01:53 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/malloc-init :load-priority 200)

(in-package muerte.lib)

(let* ((stack-vector (%run-time-context-slot nil 'muerte::stack-vector))
       ;; We assume the kernel static are ends with the stack-vector.
       (kernel-end-location (+ 2 (muerte:object-location stack-vector)
			       (array-dimension stack-vector 0)))
       (memsize-mb (muerte.x86-pc::memory-size))
       ;; Start-location is kernel-end rounded up to the next 4096 edge.
       (start-location (logand (+ kernel-end-location (1- 4096/4)) -4096/4))
       ;; End-location is the end of the memory.
       (end-location (* (1- memsize-mb) 1024 1024/4)))
  (muerte:malloc-initialize start-location (- end-location start-location))
  (setf (cdar muerte::%memory-map%) end-location)
  (loop for x from kernel-end-location below start-location
      do (setf (memref x 0 :type :unsigned-byte32) 0))
  (values))


