;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromsoe, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      load.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Jan 15 18:40:58 2004
;;;;                
;;;; $Id: load.lisp,v 1.3 2004/01/15 19:00:09 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package :cl-user)

(load (compile-file #p"../binary-types/binary-types"))

(let ((*default-pathname-defaults* #p"../ia-x86/"))
  #+(or cmu sbcl)
  (let ((pwd (ext:default-directory)))
    (progn
      (unwind-protect
	  (progn
	    (setf (ext:default-directory) #p"../ia-x86/")
	    (load "load"))
	(setf (ext:default-directory) pwd))))
  #-(or cmu sbcl) (load "load"))

;; (load (compile-file #p"../infunix/procfs"))


#+allegro (progn
	    (load "packages.lisp")
	    (load "movitz.lisp")
	    (excl:compile-system :movitz)
	    (excl:load-system :movitz)
	    (setf excl:*tenured-bytes-limit* #x2000000)
	    (setf (system::gsgc-parameter :generation-spread) 12)
	    (sys:resize-areas :new (* 16 1024 1024)))

#-allegro (with-compilation-unit ()
	    #+cmu (setf bt::*ignore-hidden-slots-for-pcl* t)
	    (mapcar (lambda (path)
		      (load (compile-file (make-pathname :name path :type "lisp") :print nil)))
		    '("packages"
		      "movitz"
		      "parse"
		      "eval"
		      "multiboot"
		      "bootblock"
		      "environment"
		      "compiler-types"
		      "compiler-protocol"
		      "storage-types"
		      "image"
		      "stream-image"
		      ;; "procfs-image"
		      "assembly-syntax"
		      "compiler-protocol"
		      "compiler" "special-operators" "special-operators-cl")))
