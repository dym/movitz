;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      toplevel.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Sep  5 15:56:26 2002
;;;;                
;;;; $Id: toplevel.lisp,v 1.5 2004/03/26 01:46:47 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/toplevel)

(defpackage muerte.toplevel
  (:use #:muerte.cl #:muerte)
  (:export #:define-toplevel-command
	   #:invoke-toplevel-command
	   #:*toplevel-commands*))

(in-package muerte.toplevel)

(define-compile-time-variable *toplevel-commands*
    (make-hash-table :test #'eq))

(defmacro define-toplevel-command (name lambda-list &body body)
  (assert (keywordp name))
  (let ((function-name (intern (format nil "~A~A" 'toplevel- name) :muerte.toplevel)))
    `(progn
       (defun ,function-name ,lambda-list ,@body)
       (eval-when (:compile-toplevel)
	 (setf (gethash ,name *toplevel-commands*) ',function-name)))))
       
(defun invoke-toplevel-command (name &rest arguments)
  (declare (dynamic-extent arguments))
  (let ((f (gethash name *toplevel-commands*)))
    (if f
	(apply f arguments)
      (multiple-value-bind (completion completion-count)
	  (muerte.readline:complete-symbol-name (string name)
						:package :keyword
						:filter-matches (lambda (x)
								  (and (gethash x *toplevel-commands*)
								       t)))
	(case completion-count
	  (0 (format t "~&No toplevel command named ~S." name)
	     name)
	  (1 (apply (gethash completion *toplevel-commands*) arguments))
	  (t (format t "~&Toplevel command ~W is ambigous, matching~{ ~A~}."
		     name
		     (nth-value 4 (muerte.readline:complete-symbol-name
				   (string name)
				   :package :keyword
				   :collect-matches t
				   :filter-matches (lambda (x)
						     (and (gethash x *toplevel-commands*)
							  t)))))
	     (values)))))))


