;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      repl.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Mar 19 14:58:12 2003
;;;;                
;;;; $Id: repl.lisp,v 1.18 2008-04-27 08:34:46 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(require :lib/readline)
(provide :lib/repl)

(defpackage #:muerte.repl
  (:documentation "Implementation of Read Eval Print Loop.")
  (:nicknames #:repl)
  (:use #:common-lisp #:muerte)
  (:export #:*repl-level*
	   #:*repl-prompter*
	   #:*repl-prompt-context*
	   #:*repl-print-format*
	   #:*repl-readline-context*
	   #:read-eval-print))

(in-package #:muerte.repl)

(defparameter *repl-level* -1)
(defparameter *repl-prompter* 'default-repl-prompter)
(defparameter *repl-prompt-context* nil)
(defparameter *repl-print-format* "~@{~&~W~}")
(defvar *repl-readline-context* nil)
(defvar *repl-consless* nil)

(defun default-repl-prompter ()
  (fresh-line)
  (when (or (plusp *repl-level*) *repl-prompt-context*)
    (format t "[~D~@[~A~]] " *repl-level* *repl-prompt-context*))
  (format t "~A> " (package-name *package*)))

(defun read-eval-print (&optional (*repl-readline-context* *repl-readline-context*)
				  (*repl-level* (1+ *repl-level*)))
  (let ((muerte:*print-safely* t))
    (if (stringp *repl-prompter*)
	(format t *repl-prompter* *repl-level* *package*)
      (funcall *repl-prompter*)))
  (handler-case
      (let ((previous-package *package*)
	    (buffer-string
	     (handler-bind
		 ((serious-condition
		   (lambda (c)
		     (backtrace :frame (muerte:current-stack-frame))
		     (format *terminal-io* "~&Error during readline (~S): ~A" 
			     *repl-readline-context* c)
		     (muerte:halt-cpu))))
	       (muerte.readline:contextual-readline *repl-readline-context*))))
	(when (plusp (length buffer-string))
	  (terpri)
	  (multiple-value-bind (form buffer-pointer)
	      (handler-bind
		  ((muerte::missing-delimiter
		    (lambda (c)
		      (declare (ignore c))
		      (format t "~&> ")
		      (invoke-restart 'muerte::next-line
				      (muerte.readline:contextual-readline *repl-readline-context*)))))
		(simple-read-from-string buffer-string t t))
	    (fresh-line)		; Let the user know something happened.
	    (flet ((process-expresion (form previous-package printp &rest results)
		     (declare (dynamic-extent results))
		     (unless (packagep *package*)
		       (warn "Resetting *package*")
		       (setf *package* previous-package))
		     (unless (boundp '*)
		       (warn "* was unbound!")
		       (setf * nil))
		     (when printp
		       (let ((muerte:*print-safely* t))
			 (apply #'format t *repl-print-format* results)))
		     (psetq +++ ++ ++ + + form)
		     (psetq *** ** ** * * (car results))
		     (psetq /// // // / / (if *repl-consless*
					      nil
					    (copy-list results)))
		     (values-list results)))
	      (let ((restart (and (integerp form)
				  muerte:*debugger-dynamic-context*
				  (muerte:find-restart-by-index form
								muerte:*debugger-dynamic-context*))))
		(cond
		 (restart
		  (invoke-restart-interactively restart))
		 ((not (keywordp form))
		  (let ((- form))
		    (multiple-value-call #'process-expresion
		      form previous-package t (eval form))))
		 (t (multiple-value-call #'process-expresion
		      form previous-package nil
		      (apply 'muerte.toplevel:invoke-toplevel-command
			     form
			     (loop for arg = (multiple-value-bind (arg x)
						 (simple-read-from-string buffer-string nil '#0=#:eof
									  :start buffer-pointer)
					       (setq buffer-pointer x)
					       arg)
				 until (eq arg '#0#)
				 collect arg))))))))))
    (muerte.readline::readline-break (c)
      (declare (ignore c))
      (values))))

