;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      eval.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 19 21:15:12 2001
;;;;                
;;;; $Id: eval.lisp,v 1.35 2008-07-09 20:11:23 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/eval)

(in-package muerte)

(define-compile-time-variable *eval-special-operators*
    (make-hash-table :test #'eq))

(defmacro define-eval-special-operator (operator lambda-list &body body)
  (let ((name (intern (format nil "~A-~A" 'eval-special-operator operator))))
    `(progn
       (eval-when (:compile-toplevel)
	 (setf (gethash (find-symbol ,(symbol-name operator))
			*eval-special-operators*)
	       ',name))
       (defun ,name ,lambda-list ,@body))))

(defun special-operator-p (symbol)
  (if (gethash symbol *eval-special-operators*)
      t
      nil))

(defun eval (form)
  (eval-form form nil))

(defun eval-form (form env)
  "3.1.2.1 Form Evaluation."
  (check-stack-limit)
  (multiple-value-bind (macro-expansion expanded-p)
      (macroexpand form env)
    (if expanded-p
	(eval-form macro-expansion env)
	(typecase form
	  (null nil)
	  (symbol (eval-symbol form env))
	  (cons (eval-cons form env))
	  (t form)))))

(defun env-binding (env var)
  ;; (warn "env: ~S in ~S" var env)
  (find var env :key #'car))

(defun op-env-binding (env var &rest types)
  (declare (dynamic-extent types))
  (dolist (binding env)
    (when (and (consp (cdr binding))
	       (eq var (cadr binding))
	       (or (null types)
		   (member (car binding) types)))
      (return binding))))

;; These are integers because regular (lexical) bindings are never
;; named by integers.
(defconstant +eval-binding-type-flet+ 0)
(defconstant +eval-binding-type-go-tag+ 1)
(defconstant +eval-binding-type-block+ 2)
(defconstant +eval-binding-type-macrolet+ 3)
(defconstant +eval-binding-type-declaration+ 4)

(defun eval-symbol (form env)
  "3.1.2.1.1 Symbols as Forms"
  (if (symbol-constant-variable-p form)
      (symbol-value form)
    (let ((binding (env-binding env form)))
      (if binding
	  (cdr binding)
	  (symbol-value form)))))

;;;  block      let*                  return-from      
;;;  catch      load-time-value       setq             
;;;  eval-when  locally               symbol-macrolet  
;;;  flet       macrolet              tagbody          
;;;  function   multiple-value-call   the              
;;;  go         multiple-value-prog1  throw            
;;;  if         progn                 unwind-protect   
;;;  labels     progv                                  
;;;  let        quote                                  
;;;
;;;Figure 3-2. Common Lisp Special Operators

(define-eval-special-operator quote (form env)
  (declare (ignore env))
  (cadr form))

(define-eval-special-operator progn (form env)
  (eval-progn (cdr form) env))

(define-eval-special-operator if (form env)
  (if (eval-form (second form) env)
      (eval-form (third form) env)
      (eval-form (fourth form) env)))

(define-eval-special-operator block (form env)
  (catch form
    (eval-progn (cddr form)
		(cons (list* +eval-binding-type-block+
			     (cadr form)
			     form)
		      env))))

(define-eval-special-operator return-from (form env)
  (let ((b (cdr (op-env-binding env (cadr form) +eval-binding-type-block+))))
    (unless b (error "Block ~S is not visible." (cadr form)))
    (throw (cdr b)
      (eval-form (caddr form) env))))

(define-eval-special-operator macrolet (form env)
  (dolist (macrolet (cadr form))
    (destructuring-bind (name lambda &body body)
	macrolet
      (check-type name symbol)
      (check-type lambda list)
      (push (list* +eval-binding-type-macrolet+
		   name
		   (cdr macrolet))
	    env)))
  (eval-progn (cddr form)
	      env))

(define-eval-special-operator let (form env)
  (let ((var-specs (cadr form))
	(declarations-and-body (cddr form)))
    (let (special-vars
	  special-values
	  (local-env env))
      (multiple-value-bind (body declarations)
	  (parse-declarations-and-body declarations-and-body)
	(dolist (var-spec var-specs)
	  (multiple-value-bind (var init-form)
	      (if (atom var-spec)
		  (values var-spec nil)
		  (values (car var-spec) (cadr var-spec)))
	    (cond
	      ((or (symbol-special-variable-p var)
		   (declared-special-p var declarations))
	       ;; special
	       (push var special-vars)
	       (push (eval-form init-form env) special-values))
	      (t ;; lexical
	       (push (cons var (eval-form init-form env))
		     local-env)))))
	(if (null special-vars)
	    (eval-progn body local-env)
	    (progv special-vars special-values
	      (eval-progn body local-env)))))))

(define-eval-special-operator let* (form env)
  (let ((var-specs (cadr form))~)
    (if (null var-specs)
	(eval-progn body env)
	(multiple-value-bind (body declarations)
	    (parse-declarations-and-body (cddr form))
	  (multiple-value-bind (var init-form)
	      (let ((var-spec (pop var-specs)))
		(if (atom var-spec)
		    (values var-spec nil)
		    (destructuring-bind (var init-form)
			var-spec
		      (values var init-form))))
	    (if (or (symbol-special-variable-p var)
		    (declared-special-p var declarations))
		(progv (list var) (list (eval-form init-form env))
		  (eval-let* var-specs
			     declarations
			     body
			     env))
		(eval-let* var-specs
			   declarations
			   body
			   (cons (cons var
				       (eval-form init-form env))
				 env))))))))

(define-eval-special-operator multiple-value-call (form env)
  (apply (eval-form (cadr form) env)
	 (mapcan (lambda (args-form)
		   (multiple-value-list (eval-form args-form env)))
		 (cddr form))))

(define-eval-special-operator catch (form env)
  (catch (eval-form (second form) env)
    (eval-progn (cddr form) env)))

(define-eval-special-operator throw (form env)
  (throw (eval-form (second form) env)
    (eval-form (third form) env)))

(define-eval-special-operator unwind-protect (form env)
  (unwind-protect
       (eval-form (second form) env)
    (eval-progn (cddr form) env)))

(define-eval-special-operator the (form env)
  (destructuring-bind (value-type form)
      (cdr form)
    (declare (ignore value-type))
    (eval-form form env)))

(define-eval-special-operator multiple-value-prog1 (form env)
  (multiple-value-prog1 (eval-form (cadr form) env)
    (eval-progn (cddr form) env)))

(define-eval-special-operator symbol-macrolet (form env)
  (error "Special operator ~S not implemented in ~S." (car form) 'eval))

(defun eval-cons (form env)
  "3.1.2.1.2 Conses as Forms"
  (if (and (consp (car form))
	   (eq 'lambda (caar form)))
      (eval-funcall (cons (let ((lambda-list (cadar form))
				(lambda-body (parse-docstring-declarations-and-body (cddar form))))
			    (lambda (&rest args)
			      (declare (dynamic-extent args))
			      (eval-progn lambda-body
					  (make-destructuring-env lambda-list args env
								  :environment-p nil
								  :recursive-p nil
								  :whole-p nil))))
			  (cdr form))
		    env)
      (let ((special-operator (gethash (car form) *eval-special-operators*)))
	(if special-operator
	    (funcall special-operator form env)
	    (case (car form)
	      (setq (eval-setq form env))
	      (setf (eval-setf form env))
;; 	      ((defvar) (eval-defvar form env))
	      ((multiple-value-bind)
	       (eval-m-v-bind form env))
	      (t (eval-funcall form env)))))))

(defun eval-progn (forms env)
  (do ((p forms (cdr p)))
      ((endp (cdr p))
       (eval-form (car p) env))
    (eval-form (car p) env)))

(defun eval-funcall (form env)
  (let ((f (pop form))
	a0 a1)
    (if (null form)
	(funcall f)
	(if (null (progn (setf a0 (eval-form (pop form) env)) form))
	    (funcall f a0)
	    (if (null (progn (setf a1 (eval-form (pop form) env)) form))
		(funcall f a0 a1)
		(apply (lambda (f env a0 a1 &rest args)
			 (declare (dynamic-extent args))
			 (let ((evaluated-args (do ((p args (cdr p)))
						   ((endp p) args)
						 (setf (car p) (eval-form (car p) env)))))
			   (apply f a0 a1 evaluated-args)))
		       f env a0 a1 form))))))

(defun parse-macro-lambda-list (lambda-list)
  (let* ((whole-var (when (eq '&whole (car lambda-list))
                      (pop lambda-list)
                      (pop lambda-list)))
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
                  (push x r)))))
         (ignore-env-var
          (when (not env-var)
            (gensym "ignore-env-"))))
    (values destructuring-lambda-list
            whole-var
            (or env-var
                ignore-env-var)
            (when ignore-env-var
              (list ignore-env-var))
            (list operator-var))))

(defun parse-declarations-and-body (forms &optional (declare 'declare))
  "From the list of FORMS, return first the list of non-declaration forms, ~
second the list of declaration-specifiers."
  (assert (eq declare 'declare))
  (do (declarations
       (p forms (cdr p)))
      ((not (and (consp (car p)) (eq 'declare (caar p))))
       (values p declarations))
    (dolist (d (cdar p))
      (push d declarations))))

(defun parse-docstring-declarations-and-body (forms &optional (declare-symbol 'muerte.cl::declare))
  "From the list of FORMS, return first the non-declarations forms, second the declarations, ~
   and third the documentation string."
  (let ((docstring nil))
    (do (declarations docstring)
	((endp forms)
	 (values nil
		 declarations
		 docstring))
      (cond
	((typep (car forms)
		'(cons (eql declare)))
	 (setf declarations (append declarations (cdr (pop forms)))))
	((and (stringp (car forms))
	      (cdr forms))
	 (setf docstring (pop forms)))
	(t (return (values forms
			   declarations
			   docstring)))))))

(defun compute-function-block-name (function-name)
  (cond
   ((symbolp function-name) function-name)
   ((and (consp function-name)
	 (symbolp (cadr function-name)))
    (cadr function-name))
   (t (error "Unknown kind of function-name: ~S" function-name))))

(defun declared-special-p (var declarations)
  (dolist (d declarations nil)
    (when (and (consp d)
	       (eq 'special (car d))
	       (member var (cdr d)))
      (return t))))

(defun decode-optional-formal (formal)
  "3.4.1.2 Specifiers for optional parameters.
Parse {var | (var [init-form [supplied-p-parameter]])}
Return the variable, init-form, and suplied-p-parameter."
  (etypecase formal
    (symbol (values formal nil nil))
    (cons (values (first formal) (second formal) (third formal)))))

(defun decode-keyword-formal (formal)
  "3.4.1.4 Specifiers for keyword parameters.
Parse {var | ({var | (keyword-name var)} [init-form [supplied-p-parameter]])}
Return the variable, keyword, init-fom, and supplied-p-parameter."
  (cond
   ((symbolp formal)
    (values formal
	    (intern (symbol-name formal) :keyword)
	    nil nil))
   ((symbolp (car formal))
    (values (car formal)
	    (intern (symbol-name (car formal)) :keyword)
	    (cadr formal)
	    (caddr formal)))
   (t (values (cadar formal)
	      (caar formal)
	      (cadr formal)
	      (caddr formal)))))

(defun make-destructuring-env (pattern values env &key (recursive-p t)
			       (environment-p nil)
			       (whole-p t))
  (let (env-var)
    (when (and whole-p (eq '&whole (car pattern)))
      (push (cons (cadr pattern) values)
	    env)
      (setf pattern (cddr pattern)))
    (when (and environment-p
	       (eq '&environment (car pattern)))
      (setf env-var (cadr pattern)
	    pattern (cddr pattern)))
    (loop with next-states = '(&optional &rest &key &aux)
       with state = 'requireds
       for pp on pattern as p = (car pp)
       if (member p next-states)
       do (setf next-states (member p next-states)
		state p)
       else do (cond
		 ((and (eq state 'requireds)
		       recursive-p
		       (consp p))
		  (unless (listp (car values))
		    (simple-program-error "Lambda-list pattern mismatch."))
		  (setf env (make-destructuring-env p (pop values) env
						    :recursive-p nil
						    :environment-p nil)))
		 ((and environment-p
		       (eq p '&environment))
		  (setf env-var (cadr pp)
			pp (cdr pp)))
		 ((or (symbolp p)
		      (not (eq state 'requireds)))
		  (case state
		    (requireds
		     (when (null values)
		       (simple-program-error "Too few values provided. [~S:~S:~S]"
					     state next-states env))
		     (push (cons p (pop values))
			   env))
		    (&optional
		     (multiple-value-bind (var init-form supplied-p-parameter)
			 (decode-optional-formal p)
		       (when supplied-p-parameter
			 (push (cons supplied-p-parameter
				     (not (null values)))
			       env))
		       (push (cons var (if values
					   (pop values)
					   (eval-form init-form env)))
			     env)))
		    (&rest
		     (push (cons p values)
			   env))
		    (&key
		     (multiple-value-bind (var key init-form supplied-p-parameter)
			 (decode-keyword-formal p)
		       (let* ((x (member key values :test #'eq))
			      (present-p (not (null x)))
			      (value (if present-p
					 (cadr x)
					 (eval-form init-form env))))
			 (when supplied-p-parameter
			   (push (cons supplied-p-parameter
				       present-p)
				 env))
			 (push (cons var value)
			       env))))
		    (&aux
		     (multiple-value-bind (var init-form)
			 (if (consp p)
			     (values (car p) (cadr p))
			     (values p nil))
		       (push (cons var (eval-form init-form env))
			     env)))))
		 (t (error "Illegal destructuring pattern: ~S" pattern)))
       (when (not (listp (cdr pp)))
	 (push (cons (cdr pp) values)
	       env))
       finally
       (when (and values (member state '(requireds optionals)))
	 (simple-program-error "Too many arguments.")))
    (if (and environment-p env-var)
	(cons (cons env-var env)
	      env)
	env)))

(defun eval-let* (var-specs declarations body env)
  (if (null var-specs)
      (eval-progn body env)
      (multiple-value-bind (var init-form)
	  (let ((var-spec (pop var-specs)))
	    (if (atom var-spec)
		(values var-spec nil)
		(destructuring-bind (var init-form)
		    var-spec
		  (values var init-form))))
	(if (or (symbol-special-variable-p var)
		(declared-special-p var declarations))
	    (progv (list var) (list (eval-form init-form env))
	      (eval-let* var-specs
			 declarations
			 body
			 env))
	    (eval-let* var-specs
		       declarations
		       body
		       (cons (cons var
				   (eval-form init-form env))
			     env))))))

(defun eval-m-v-bind (form env)
  (destructuring-bind (variables values-form &body declarations-and-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let ((values (multiple-value-list (eval-form values-form env)))
	    special-vars
	    special-values)
	(dolist (var variables)
	  (let ((value (pop values)))
	    (cond
	      ((or (symbol-special-variable-p var)
		   (declared-special-p var declarations))
	       ;; special
	       (push var special-vars)
	       (push value special-values))
	      (t ;; lexical
	       (push (cons var value)
		     env)))))
	(eval-progn body env)))))

(define-eval-special-operator function (form env)
  (let ((function-name (second form)))
    (etypecase function-name
      (symbol
       (let ((binding (cdr (op-env-binding env function-name +eval-binding-type-flet+))))
	 (or (and binding (cdr binding))
	     (symbol-function function-name))))
      (list
       (ecase (car function-name)
	 ((setf)
	  (symbol-function (lookup-setf-function (second function-name))))
	 ((lambda)
	  (let ((lambda-list (cadr function-name))
		(lambda-body (parse-docstring-declarations-and-body (cddr function-name))))
	    (install-funobj-name :anonymous-lambda
				 (lambda (&rest args)
				   (declare (dynamic-extent args))
				   (eval-progn lambda-body
					       (make-destructuring-env lambda-list args env
								       :environment-p nil
								       :recursive-p nil
								       :whole-p nil)))))))))))

(defun lookup-setf-function (name)
  (let ((setf-name (gethash name *setf-namespace*)))
    (assert setf-name (name)
      "No function (~S ~S) defined." 'setf name)
    setf-name))

(defun setf-intern (name)
  (values (gethash name *setf-namespace*)))

(defun special-operator-p (operator-name)			   
  (member operator-name '(quote function if progn tagbody go)))
  
(defun eval-arglist (list env)
  (if (null list)
      nil
    (cons (eval-form (car list) env)
	  (eval-arglist (cdr list) env))))

(define-eval-special-operator tagbody (form env)
  ;; build the..
  (do* ((pc (cdr form) (cdr pc))
	(instruction (car pc) (car pc)))
       ((endp pc))
    (when (typep instruction '(or integer symbol))
      (push (list* +eval-binding-type-go-tag+ instruction form)
	    env)))
  ;; execute body..
  (prog ((pc (cdr form)))
   start
   (let ((tag (catch form
		(do () ((endp pc) (go end))
		  (let ((instruction (pop pc)))
		    (unless (typep instruction '(or integer symbol))
		      (eval-form instruction env)))))))
     (setf pc (cdr (member tag (cdr form))))
     (go start))
   end))

(define-eval-special-operator go (form env)
  (let* ((tag (cadr form))
	 (b (cdr (op-env-binding env tag +eval-binding-type-go-tag+))))
    (assert b () "Go-tag ~S is not visible." tag)
    (throw (cdr b) (values tag))))

(defun eval-set-variable (variable-name value env)
  "Perform e.g. (setq <variable-name> <value>) according to <env>. Return <value>."
  (check-type variable-name symbol "a variable name")
  (if (symbol-special-variable-p variable-name)
      (set variable-name value)
    (let ((binding (env-binding env variable-name)))
      (if binding
	  (setf (cdr binding) value)
	;; We could emit a warning here, or whatever.
	(set variable-name value)))))

(defun eval-setq (form env)
  (do* ((p (cdr form) (cddr p))
	(final-value nil))
      ((null p) final-value)
    (assert (cdr p) (form)
      "Odd number of arguments to setq: ~W" form)
    (setf final-value
      (eval-set-variable (car p) (eval-form (cadr p) env) env))))

(defun eval-setf (form env)
  (do* ((p (cdr form) (cddr p))
	(final-value nil))
      ((null p) final-value)
    (assert (cdr p) (form)
      "Odd number of arguments to setf: ~W" form)
    (setf final-value
      (let ((place (first p))
	    (value-form (second p)))
	(if (symbolp place)
	    (eval-set-variable place (eval-form value-form env) env)
	  ;; eval place's subforms before value-form..
	  (let ((place-subvalues (eval-arglist (cdr place) env)))
	    (apply (lookup-setf-function (caar p))
		   (eval-form value-form env)
		   place-subvalues)))))))

(defun eval-defvar (form env)
  (let ((name (second form)))
    (check-type name symbol "variable name")
    (setf (symbol-special-variable-p name) t)
    (when (and (cddr form) (not (boundp name)))
      (setf (symbol-value name)
	(eval-form (third form) env)))
    name))

(defun compile (name &optional definition)
  "=> function, warnings-p, failure-p"
  (let ((function (eval (or definition (symbol-function name)))))
    (check-type function function)
    (warn ";; There is no real compiler here.")
    (values (if (not name)
		function
	      (setf (symbol-function name) function))
	    nil
	    nil)))

(defun macroexpand-1 (form &optional env)
  (if (atom form)
      (values form nil) ; no symbol-macros yet
      (let ((operator (car form)))
	(when (symbolp operator)
	  (let ((macrolet-binding (op-env-binding env operator +eval-binding-type-macrolet+)))
	    (if (not macrolet-binding)
		(let ((macro-function (macro-function operator)))
		  (if macro-function
		      (values (funcall *macroexpand-hook* macro-function form env)
			      t)
		      (values form
			      nil)))
		(let ((lambda-list (caddr macrolet-binding)))
                  (multiple-value-bind (body declarations docstring)
                      (parse-docstring-declarations-and-body (cdddr macrolet-binding))
                    (declare (ignore docstring))
                    (multiple-value-bind (destructuring-lambda-list whole-var env-var ignore-env ignore-operator)
                        (parse-macro-lambda-list lambda-list)
                      (let* ((form-var (or whole-var (gensym)))
                             (expander (lambda (form env)
                                         (eval-form `(let ((,form-var ',form)
                                                           (,env-var ',env))
                                                       (declare (ignore ,@ignore-env))
                                                       (destructuring-bind ,destructuring-lambda-list
                                                           ,form-var
                                                         (declare (ignore ,@ignore-operator)
                                                                  ,@declarations)
                                                         ,@body))
                                                    env))))
                        (values (funcall *macroexpand-hook* expander form env)
                                t)))))))))))

(defun macroexpand (form &optional env)
  (do ((expanded-at-all-p nil)) (nil)
    (multiple-value-bind (expansion expanded-p)
	(macroexpand-1 form env)
      (when (not expanded-p)
	(return (values expansion expanded-at-all-p)))
      (setf form expansion
	    expanded-at-all-p t))))

(defun proclaim (declaration)
  ;; What do do?
  (warn "Unknown declaration: ~S" declaration)
  (values))


(defun constantp (form &optional environment)
  (typecase form
    (boolean t)
    (keyword t)
    (symbol
     (symbol-constant-variable-p form))
    (cons
     (eq 'quote (car form)))
    (t t)))

(defun macro-function (symbol &optional environment)
  "=> function"
  (when (not (eq nil environment))
    (error "Unknown environment ~S." environment))
  (when (fboundp symbol)
    (let ((f (symbol-function symbol)))
      (when (typep f 'macro-function)
	f))))
