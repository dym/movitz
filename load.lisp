;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      load.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Jan 15 18:40:58 2004
;;;;                
;;;; $Id: load.lisp,v 1.7 2004/01/19 19:21:14 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package :cl-user)

(load (compile-file #p"../binary-types/binary-types"))

(let ((*default-pathname-defaults* (merge-pathnames #p"../ia-x86/")))
  #+(or cmu) (let ((pwd (ext:default-directory)))
	       (progn
		 (unwind-protect
		     (progn
		       (setf (ext:default-directory) #p"../ia-x86/")
		       (load "load"))
		   (setf (ext:default-directory) pwd))))
  #-(or cmu) (load "load"))

#+allegro (progn
	    (load (compile-file #p"../infunix/procfs"))
	    (load "packages.lisp")
	    (load "movitz.lisp")
	    (excl:compile-system :movitz)
	    (excl:load-system :movitz)
	    (setf excl:*tenured-bytes-limit* #x2000000)
	    (setf (system::gsgc-parameter :generation-spread) 12)
	    (sys:resize-areas :new (* 16 1024 1024)))

#+clisp (load "packages")
#+clisp (defconstant movitz::&all 'movitz::&all) ; CLisp has this wonderful bug..
#+clisp (defconstant movitz::&code 'movitz::&code)
#+clisp (defconstant movitz::&form 'movitz::&form)
#+clisp (defconstant movitz::&returns 'movitz::&returns)
#+clisp (defconstant movitz::&functional-p 'movitz::&functional-p)
#+clisp (defconstant movitz::&modifies 'movitz::&modifies)
#+clisp (defconstant movitz::&type 'movitz::&type)
#+clisp (defconstant movitz::&final-form 'movitz::&final-form)
#+clisp (defconstant movitz::&funobj 'movitz::&funobj)
#+clisp (defconstant movitz::&top-level-p 'movitz::&top-level-p)
#+clisp (defconstant movitz::&result-mode 'movitz::&result-mode)
#+clisp (defconstant movitz::&env 'movitz::&env)
#+clisp (defconstant movitz::&producer 'movitz::&producer)


#-allegro (do () (nil)
	    (with-simple-restart (retry "Retry loading Movitz")
	      (return
		(with-compilation-unit ()
		  #+cmu (setf bt::*ignore-hidden-slots-for-pcl* t)
		  (mapcar (lambda (path)
			    (do () (nil)
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
