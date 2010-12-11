;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      load.lisp
;;;; Description:   Load the Movitz development system.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Jan 15 18:40:58 2004
;;;;                
;;;; $Id: load.lisp,v 1.14 2008-03-15 20:46:17 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package :cl-user)

#+lispworks-personal-edition (progn
			       (dbg::clear-all-source-level-debugging)
			       (hcl:toggle-source-debugging nil)
			       (compiler::clear-xref-info t)
			       (setf compiler:*source-level-debugging* nil
				     compiler:*load-xref-info* nil
				     compiler:*produce-xref-info* nil)
			       (proclaim '(optimize (space 3) (speed 0) 
					   (debug 0) (compilation-speed 3))))

(load (compile-file #p"../binary-types/binary-types"))

(load (compile-file #p"asm")) ; these are here for now, because
(load (compile-file #p"asm-x86")) ; ia-x86 needs them while testing/migrating.


#+ia-x86 (let ((*default-pathname-defaults* (merge-pathnames #p"../ia-x86/")))
	   #+(or cmu) (let ((pwd (ext:default-directory)))
			(progn
			  (unwind-protect
			       (progn
				 (setf (ext:default-directory) #p"../ia-x86/")
				 (load "load"))
			    (setf (ext:default-directory) pwd))))
	   #-(or cmu) (load "load"))

(do () (nil)
  (with-simple-restart (retry "Retry loading Movitz")
    (return
      (with-compilation-unit ()
	#+cmu (setf bt::*ignore-hidden-slots-for-pcl* t)
	(mapcar (lambda (path)
		  (do () (nil)
		    #+lispworks-personal-edition (hcl:mark-and-sweep 3)
		    (with-simple-restart (retry "Retry loading ~S" path)
		      (return
			(handler-bind 
			    (#+sbcl (sb-ext:defconstant-uneql #'continue))
			  (load (or (compile-file path :print nil)
				    (error "Compile-file of ~S failed?" path))))))))
		'("packages"
		  "movitz"
		  "parse"
		  "eval"
		  "environment"
		  "compiler-types"
		  "compiler-protocol"
		  "storage-types"
		  "multiboot"
		  "bootblock"
		  "image"
		  "stream-image"
		  ;; "procfs-image"
		  "assembly-syntax"
		  "compiler-protocol"
		  "compiler"
		  "special-operators"
		  "special-operators-cl"))))))

#+(and cmu18 (not cmu19))
(setf movitz:*compiler-compile-eval-whens* nil
      movitz:*compiler-compile-macro-expanders* nil)

#+lispworks (load "muerte-packages")	; work around an apparent bug in defpackage.
#+lispworks-personal-edition
(progn
  ;; (setf movitz:*compiler-compile-eval-whens* nil)
  (setf movitz::*compiler-do-optimize-p* nil
	movitz::*compiler-do-type-inference* nil)
  (mark-and-sweep 3))
