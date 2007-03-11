;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      error.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Sep  1 00:49:11 2001
;;;;                
;;;; $Id: error.lisp,v 1.6 2007/03/11 22:42:01 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/error)

(in-package muerte)

(defvar *ignore-errors* nil)
(defvar *simple-console-on-error* nil)
(defvar *backtrace-on-error* nil)
(defvar *error-no-condition-for-debugger* nil
  "If true, don't create a simple-error object just for the debugger,
 (presumably) since this might trigger another bug.")
(defvar *disable-interrupts-on-error* nil)

(defun error (&rest arguments)
  (declare (dynamic-extent arguments))
  (when *disable-interrupts-on-error*
    (cli))
  (unless arguments
    (error 'wrong-argument-count
	   :function #'error
	   :argument-count 0))
  (let ((datum (car arguments))
	(args (cdr arguments))
	(*standard-output* (if *simple-console-on-error*
			       #'muerte.x86-pc::textmode-console
			     *standard-output*)))
    (cond
     ((not *ignore-errors*)
      (let (#+ignore (*ignore-errors* t))
	(let ((condition (signal-simple 'simple-error datum args)))
	  (when *backtrace-on-error*
	    (backtrace))
	  (if condition
	      (invoke-debugger condition)
	    (apply 'invoke-debugger-on-designator 'simple-error datum args)))))
     #+ignore
     (t (with-inline-assembly (:returns :nothing)
	  (:compile-two-forms (:ebx :ecx) (car args) (cadr arguments))
	  (:compile-form (:result-mode :eax) datum)
	  (:halt)))))
  (muerte::halt-cpu))

(defun formatted-error (type format-control &rest format-arguments)
  (declare (dynamic-extent format-arguments))
  (error type :format-control format-control :format-arguments format-arguments))

(defun cerror (continue-format-control datum &rest arguments)
  (declare (dynamic-extent arguments))
  (with-simple-restart (continue "~?" continue-format-control arguments)
    (apply 'error datum arguments))
  nil)
