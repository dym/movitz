;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      repl.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Mar 19 14:58:12 2003
;;;;                
;;;; $Id: repl.lisp,v 1.6 2004/03/26 01:36:30 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(require :lib/readline)
(provide :lib/repl)

(in-package muerte.lib)

(defparameter *repl-level* -1)
(defparameter *repl-prompter* 'default-repl-prompter)
(defparameter *repl-prompt-context* nil)
(defparameter *repl-print-format* "~@{~&~W~}")
(defvar *repl-readline-context*)
(defvar *repl-consless* nil)

(defun default-repl-prompter ()
  (fresh-line)
  (when (plusp *repl-level*)
    (format t "[~D~@[~A~]] " *repl-level* *repl-prompt-context*))
  (format t "~A> " (package-name *package*)))

(defun read-eval-print (&optional (*repl-readline-context* *repl-readline-context*)
				  (*repl-level* (1+ *repl-level*)))
  (if (stringp *repl-prompter*)
      (format t *repl-prompter* *repl-level* *package*)
    (funcall *repl-prompter*))
  (handler-case
      (let ((previous-package *package*)
	    (buffer-string (muerte.readline:contextual-readline *repl-readline-context*)))
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
	    (multiple-value-call
		(lambda (form previous-package &rest results)
		  (declare (dynamic-extent results))
		  (unless (packagep *package*)
		    (warn "Resetting *package*")
		    (setf *package* previous-package))
		  (unless (boundp '*)
		    (warn "* was unbound!")
		    (setf * nil))
		  (apply #'format t *repl-print-format* results)
		  (psetq +++ ++ ++ + + form)
		  (psetq *** ** ** * * (car results))
		  (psetq /// // // / / (if *repl-consless*
					   nil
					 (copy-list results)))
		  (values-list results))
	      form previous-package
	      (if (not (keywordp form))
		  (eval form)
		(apply 'muerte.toplevel:invoke-toplevel-command
		       form
		       (loop for arg = (multiple-value-bind (arg x)
					   (simple-read-from-string buffer-string nil '#0=#:eof
								    :start buffer-pointer)
					 (setq buffer-pointer x)
					 arg)
			   until (eq arg '#0#)
			   collect arg)))))))
    #+ignore (muerte.readline::readline-break (c)
	       (declare (ignore c))
	       (values))))

