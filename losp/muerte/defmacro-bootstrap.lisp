;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Filename:      defmacro-bootstrap.lisp
;;;; Author:        Frode Vatvedt Fjeld
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: defmacro-bootstrap.lisp,v 1.3 2008-04-12 17:11:23 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/defmacro-bootstrap)

(muerte::defmacro/compile-time muerte.cl:defmacro (name lambda-list &body macro-body)
  (`(muerte::defmacro/compile-time ,name ,lambda-list ,macro-body)))

(muerte.cl:defmacro muerte.cl:in-package (name)
  `(progn
     (eval-when (:compile-toplevel)
       (in-package ,(movitz::movitzify-package-name name)))))

(in-package #:muerte)

(defmacro defmacro/cross-compilation (name lambda-list &body body)
  `(progn
     (defmacro/compile-time ,name ,lambda-list ,body)
     ',name))

(defmacro defmacro (name lambda-list &body body)
  `(defmacro/cross-compilation ,name ,lambda-list ,@body))

(defmacro defmacro/run-time (name lambda-list &body body)
  (multiple-value-bind (real-body declarations docstring)
      (movitz::parse-docstring-declarations-and-body body 'cl:declare)
    (let* ((block-name (compute-function-block-name name))
	   (ignore-var (gensym))
	   (whole-var (when (eq '&whole (car lambda-list))
			(list (pop lambda-list)
			      (pop lambda-list))))
	   (form-var (gensym "form-"))
	   (env-var nil)
	   (operator-var (gensym))
	   (destructuring-lambda-list
	    (do ((l lambda-list)
		 (r nil))
		((atom l)
		 (cons operator-var
		       (nreconc r l)))
	      (let ((x (pop l)))
		(if (eq x '&environment)
		    (setf env-var (pop l))
		    (push x r))))))
      (multiple-value-bind (env-var ignore-env)
	  (if env-var
	      (values env-var nil)
	      (let ((e (gensym)))
		(values e (list e))))
	(cond
	  ((and whole-var
		(null lambda-list))
	   `(make-named-function ,name
				 (&edx edx &optional ,form-var ,env-var &rest ,ignore-var)
				 ((ignore ,ignore-var ,@ignore-env))
				 ,docstring
				 (block ,block-name
				   (verify-macroexpand-call edx ',name)
				   (let ((,(second whole-var) ,form-var))
				     (declare ,@declarations)
				     ,@real-body))
				 :type :macro-function))
	  (t `(make-named-function ,name
				   (&edx edx &optional ,form-var ,env-var &rest ,ignore-var)
				   ((ignore ,ignore-var ,@ignore-env))
				   ,docstring
				   (block ,block-name
				     (verify-macroexpand-call edx ',name)
				     (destructuring-bind ,(append whole-var destructuring-lambda-list)
					 ,form-var
				       (declare (ignore ,operator-var) ,@declarations)
				       ,@real-body))
				   :type :macro-function)))))))
