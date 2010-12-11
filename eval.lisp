;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      eval.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Nov  2 17:45:05 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: eval.lisp,v 1.13 2008-04-27 19:17:17 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defun in-package-form-p (form)
  (and (consp form)
       (string= '#:in-package (car form))))

(defun require-form-p (form)
  (and (consp form)
       (string= '#:require (car form))))

(defun provide-form-p (form)
  (and (consp form)
       (string= '#:provide (car form))))

(defun movitz-module-path (require-form)
  "Given a require form, return the path of the file that is expected ~
   to provide that module."
  (let ((module (second require-form)))
    (concatenate 'string
      "losp/"
      (or (third require-form)
	  (concatenate 'string
	    (string-downcase (symbol-name module))
	    ".lisp")))))

(defun movitzify-package-name (name)
  (let ((name (string name)))
    (if (member name '("cl" "common-lisp" "mop")
		:test #'string-equal)
	(concatenate 'string (string '#:muerte.) name)
      name)))

(defmacro with-retries-until-true ((name format-control &rest format-arguments) &body body)
  `(do () (nil)
     (with-simple-restart (,name ,format-control ,@format-arguments)
       (return (progn ,@body)))))

(defun quote-form-p (x)
  (and (consp x)
       (or (eq 'cl:quote (first x))
	   (eq 'muerte.cl::quote (first x)))
       t))

(defun movitz-constantp (form &optional (env nil))
  (typecase form
    (keyword t)
    (symbol
     (let ((form (translate-program form :cl :muerte.cl)))
       (or (movitz-env-get form 'constantp nil env)
	   (typep (movitz-binding form env) 'constant-object-binding))))
    (cons
     (let* ((compiler-macro-function (movitz-compiler-macro-function (car form) env))
	    (compiler-macro-expansion (and compiler-macro-function
					   (handler-case
					       (funcall *movitz-macroexpand-hook*
							compiler-macro-function
							form env)
					     (error () form)))))
       (or (let ((form (translate-program form :cl :muerte.cl)))
	     (case (car form)
	       ((muerte.cl:quote) t)
	       ((muerte.cl:not)
		(movitz-constantp (second form)))
	       ((muerte.cl:+ muerte.cl:- muerte.cl:*)
		(every (lambda (sub-form)
			 (movitz-constantp sub-form env))
		       (cdr form)))
	       ((muerte.cl:coerce)
		(and (= 3 (length form))
		     (every (lambda (sub-form)
			      (movitz-constantp sub-form env))
			    (cdr form))
		     (not (member (movitz-eval (third form) env)
				  '(muerte.cl:function)))))))
	   (and compiler-macro-function
		(not (movitz-env-get (car form) 'notinline nil env))
		(not (eq form compiler-macro-expansion))
		(movitz-constantp compiler-macro-expansion env)))))
    (t t)))				; anything else is self-evaluating.


;;;(defun isconst (x)
;;;  (or (integerp x)
;;;      (stringp x)
;;;      (eq t x)
;;;      (eq nil x)
;;;      (quote-form-p x)))

(defun eval-form (&rest args)
  (apply 'movitz-eval args))

(defun movitz-eval (form &optional env top-level-p)
  "3.1.2.1 Form Evaluation"
  (let ((form (translate-program form :cl :muerte.cl)))
    (typecase form
      (symbol (eval-symbol form env top-level-p))
      (cons   (eval-cons form env top-level-p))
      (t      (eval-self-evaluating form env top-level-p)))))

(defun eval-form-or-error (form env error-value)
  (handler-case (eval-form form env)
    (error () error-value)))

(defun eval-symbol (form env top-level-p)
  "3.1.2.1.1 Symbols as Forms"
  (declare (ignore top-level-p))
  (cond
   ((keywordp form)
    (eval-self-evaluating form env top-level-p))
   ((typep (movitz-binding form env) 'constant-object-binding)
    (translate-program (movitz-print (constant-object (movitz-binding form env)))
		       :cl :muerte.cl))
   ((movitz-constantp form env)
    (symbol-value form))
;;;   ((movitz-lexical-binding form env)
;;;    (eval-lexical-variable form env top-level-p))
   (t (error "Don't know how to eval symbol-form ~S" form))))

(defun eval-self-evaluating (form env top-level-p)
  "3.1.2.1.3 Self-Evaluating Objects"
  (declare (ignore env top-level-p))
  form)

(defun eval-cons (form env top-level-p)
  "3.1.2.1.2 Conses as Forms"
  (let* ((operator (car form))
	 (compiler-macro-function (movitz-compiler-macro-function operator env))
	 (compiler-macro-expansion (and compiler-macro-function
					(funcall *movitz-macroexpand-hook*
						 compiler-macro-function
						 form env))))
    (cond
;;;     ((movitz-constantp form env)
;;;      (eval-constant-compound form env top-level-p))
     ((member operator '(cl:quote muerte.cl::quote))
      (eval-self-evaluating (second form) env top-level-p))
     ((member operator '(muerte.cl::not))
      (not (eval-form (second form) env nil)))
     ((member operator '(muerte.cl:+ muerte.cl:- muerte.cl:*))
      (apply (translate-program (car form) :muerte.cl :cl)
	     (mapcar (lambda (sub-form)
		       (movitz-eval sub-form env nil))
		     (cdr form))))
     ((member operator '(muerte.cl:coerce muerte.cl:make-hash-table))
      (apply (translate-program operator :muerte.cl :cl)
	     (mapcar (lambda (arg)
                       (translate-program (movitz-eval arg env nil) :muerte.cl :cl))
		     (cdr form))))
     ((and compiler-macro-function
	   (not (movitz-env-get (car form) 'notinline nil env))
	   (not (eq form compiler-macro-expansion)))
      (movitz-eval compiler-macro-expansion env top-level-p))
;;;     ((lambda-form-p form)
;;;      (eval-lambda-form form env top-level-p))
;;;     ((symbolp operator)
;;;      (cond
;;;       ((movitz-special-operator-p operator)
;;;	(eval-special-operator form env top-level-p))
;;;       ((movitz-macro-function operator env)
;;;	(eval-macro-form form env top-level-p))
;;;       (t (eval-apply-symbol form env top-level-p))))
     (t (case (car form)
	  (muerte.cl::function
	   (if (symbolp (second form))
	       (movitz-env-symbol-function (second form) env)
	     (error "Don't know how to eval function form ~A." form)))
	  (t (error "Don't know how to eval compound form ~A" form)))))))

(defun eval-constant-compound (form env top-level-p)
  (case (car form)
   ((cl:quote muerte.cl::quote)
    (eval-self-evaluating (second form) env top-level-p))
   (muerte.cl::not
    (not (eval-form (second form) env nil)))
   ((muerte.cl:+ muerte.cl:- muerte.cl:*)
    (apply (translate-program (car form) :muerte.cl :cl)
	   (mapcar (lambda (sub-form)
		     (movitz-eval sub-form env nil))
		   (cdr form))))
   ((muerte.cl:coerce)
    (apply #'coerce
	   (mapcar (lambda (arg) (movitz-eval arg env nil))
		   (cdr form))))
   (t (error "Don't know how to compile constant compound form ~A" form))))
