;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      eval.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 19 21:15:12 2001
;;;;                
;;;; $Id: eval.lisp,v 1.1 2004/01/13 11:05:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/eval)

(in-package muerte)

(defun eval (form)
  (eval-form form nil))

(defun eval-form (form env)
  "3.1.2.1 Form Evaluation."
  (check-stack-limit)
  (typecase form
    (null nil)
    (symbol (eval-symbol form env))
    (cons (eval-cons form env))
    (t form)))

(defun env-binding (env var)
  ;; (warn "env: ~S in ~S" var env)
  (find var env :key #'car))

(defun op-env-binding (type env var)
  (dolist (binding env)
    (when (and (eq type (car binding))
	       (eq var (cadr binding)))
      (return (cdr binding)))))

;; These are integers because regular (lexical) bindings are never
;; named by integers.
(defconstant +eval-binding-type-flet+ 0)
(defconstant +eval-binding-type-go-tag+ 1)

(defun eval-symbol (form env)
  "3.1.2.1.1 Symbols as Forms"
  (if (symbol-constant-variable-p form)
      (symbol-global-value form)
    (let ((binding (env-binding env form)))
      (or (and binding (cdr binding))
	  (symbol-value form)))))

(defun eval-cons (form env)
  "3.1.2.1.2 Conses as Forms"
  (case (car form)
    (quote (cadr form))
    (function (eval-function (second form) env))
    (if (if (eval-form (second form) env)
	    (eval-form (third form) env)
	  (eval-form (fourth form) env)))
    (progn (eval-progn (cdr form) env))
    (prog1 (prog1 (eval-form (cadr form) env)
	     (eval-progn (cddr form) env)))
    (tagbody (eval-tagbody form env))
    (go (eval-go form env))
    (setq (eval-setq form env))
    (setf (eval-setf form env))
    (let (eval-let (cadr form) (cddr form) env))
    (time (eval-time (cadr form) env))
    ((defun) (eval-defun (cadr form) (caddr form) (cdddr form) env))
    ((lambda) (eval-function form env)) ; the lambda macro..
    ((multiple-value-prog1)
     (multiple-value-prog1 (eval-form (cadr form) env)
       (eval-progn (cddr form) env)))
    ((destructuring-bind)
     (eval-progn (cdddr form)
      (make-destructuring-env (cadr form)
			      (eval-form (caddr form) env)
			      env)))
    ((throw)
     (throw (eval-form (second form) env)
       (eval-form (third form) env)))
    (t (eval-funcall form env))))

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

(defun eval-time (form env)
  "Supposed to be the time macro."
  (cond
   ((cpu-featurep :tsc)
    (let ((start-mem (malloc-cons-pointer)))
      (multiple-value-bind (start-time-lo start-time-hi)
	  (read-time-stamp-counter)
	(multiple-value-prog1
	    (eval-form form env)
	  (multiple-value-bind (end-time-lo end-time-hi)
	      (read-time-stamp-counter)
	    (let ((clumps (- (malloc-cons-pointer) start-mem))
		  (delta-hi (- end-time-hi start-time-hi))
		  (delta-lo (- end-time-lo start-time-lo)))
	      (format t "~&;; Time report:")
	      (if (< delta-hi #x1f)
		  (format t "~&;; CPU cycles: ~D.~%;; Space used: ~D clumps = ~/muerte:pprint-clumps/.~%"
			  (+ (ash delta-hi 24) delta-lo) clumps clumps)
		(format t "~&;; CPU cycles: ~D000.~%;; Space used: ~D clumps = ~/muerte:pprint-clumps/.~%"
			(+ (ash delta-hi 14) (ash delta-lo -10)) clumps clumps))))))))
   (t (let ((start-mem (malloc-cons-pointer)))
	(multiple-value-prog1
	    (eval-form form env)
	  (let ((clumps (- (malloc-cons-pointer) start-mem)))
	    (format t ";; Space used: ~D clumps = ~/muerte:pprint-clumps/.~%"
		    clumps clumps)))))))
    
(defun parse-declarations-and-body (forms)
  "From the list of FORMS, return first the list of non-declaration forms, ~
second the list of declaration-specifiers."
  (do (declarations
       (p forms (cdr p)))
      ((not (and (consp (car p)) (eq 'declare (caar p))))
       (values p declarations))
    (dolist (d (cdar p))
      (push d declarations))))

(defun declared-special-p (var declarations)
  (dolist (d declarations nil)
    (when (and (consp d)
	       (eq 'special (car d))
	       (member var (cdr d)))
      (return t))))

(defun eval-defun (name lambda-list body env)
  (assert (not (eq (symbol-package name)
		   (find-package 'common-lisp)))
      () "Won't allow defun of a common-lisp symbol.")
  (setf (symbol-function name)
    (install-funobj-name name
			 (lambda (&rest args)
			   (declare (dynamic-extent args))
			   (eval-progn body (make-destructuring-env
					     lambda-list args env
					     :environment-p nil
					     :recursive-p nil
					     :whole-p nil)))))
  name)



(defun parse-optional-formal (formal)
  "3.4.1.2 Specifiers for optional parameters.
Parse {var | (var [init-form [supplied-p-parameter]])}
Return the variable, init-form, and suplied-p-parameter."
  (etypecase formal
    (symbol (values formal nil nil))
    (cons (values (first formal) (second formal) (third formal)))))

(defun parse-keyword-formal (formal)
  "3.4.1.4 Specifiers for keyword parameters.
Parse {var | ({var | (keyword-name var)} [init-form [supplied-p-parameter]])}
Return the variable, keyword, init-fom, and supplied-p-parameter."
  (cond
   ((symbolp formal)
    (values formal formal nil nil))
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
    (loop with next-states = '(&optional &rest &key)
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
		    (error "Pattern mismatch."))
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
		       (error "Too few values provided. [~S:~S:~S]" state next-states env))
		     (push (cons p (pop values))
			   env))
		    (&optional
		     (multiple-value-bind (var init-form supplied-p-parameter)
			 (parse-optional-formal p)
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
			 (parse-keyword-formal p)
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
			       env))))))
		 (t (error "Illegal destructuring pattern: ~S" pattern)))
	     (when (not (listp (cdr pp)))
	       (push (cons (cdr pp) values)
		     env)))
    (if (and environment-p env-var)
	(cons (cons env-var env)
	      env)
      env)))

(defun eval-let (var-specs declarations-and-body env)
  (let (special-vars
	special-values
	(local-env env))
    (multiple-value-bind (body declarations)
	declarations-and-body
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
	  (eval-progn body local-env))))))

(defun eval-function (function-name env)
  (etypecase function-name
    (symbol
     (let ((binding (op-env-binding +eval-binding-type-flet+ env function-name)))
       (or (and binding (cdr binding))
	   (symbol-function function-name))))
    (list
     (ecase (car function-name)
       ((setf)
	(symbol-function (lookup-setf-function (second function-name))))
       ((lambda)
	(let ((lambda-list (cadr function-name))
	      (lambda-body (cddr function-name)))
	  (lambda (&rest args)
	    (declare (dynamic-extent args))
	    (eval-progn lambda-body
			(make-destructuring-env lambda-list args env
						:environment-p nil
						:recursive-p nil
						:whole-p nil)))))))))
  
(defun lookup-setf-function (name)
  (let ((setf-name (gethash name (get-global-property :setf-namespace))))
    (assert setf-name (name)
      "No function (~S ~S) defined." 'setf name)
    setf-name))

(defun setf-intern (name)
  (values (gethash name (get-global-property :setf-namespace))))

(defun special-operator-p (operator-name)			   
  (member operator-name '(quote function if progn tagbody go)))
  
(defun eval-arglist (list env)
  (if (null list)
      nil
    (cons (eval-form (car list) env)
	  (eval-arglist (cdr list) env))))

(defun eval-tagbody (form env)
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

(defun eval-go (form env)
  (declare (ignore))
  (let* ((tag (cadr form))
	 (b (op-env-binding +eval-binding-type-go-tag+ env tag)))
    (unless b (error "Go-tag ~S is not visible." tag))
    (throw (cdr b) (values tag))))


(defun eval-setq (form env)
  (do* ((p (cdr form) (cddr p))
	(value nil))
      ((null p) value)
    (assert (cdr p) (form)
      "Odd number of arguments to setq: ~W" form)
    (setf value
      (set (car p) (eval-form (cadr p) env)))))

(defun eval-setf (form env)
  (do* ((p (cdr form) (cddr p))
	(value nil))
      ((null p) value)
    (assert (cdr p) (form)
      "Odd number of arguments to setf: ~W" form)
    (setf value
      (let ((place (first p))
	    (value-form (second p)))
	(if (symbolp place)
	    (set place (eval-form value-form env))
	  ;; eval subvalues before value-form..
	  (let ((place-subvalues (eval-arglist (cdr place) env)))
	    (apply (lookup-setf-function (caar p))
		   (eval-form value-form env)
		   place-subvalues)))))))
