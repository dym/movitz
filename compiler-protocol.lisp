;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      compiler-protocol.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Oct 10 13:02:03 2001
;;;;                
;;;; $Id: compiler-protocol.lisp,v 1.5 2008-03-21 22:30:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +boolean-modes+
      '(:boolean-greater
	:boolean-less
	:boolean-greater-equal
	:boolean-less-equal
	:boolean-below
	:boolean-above
	:boolean-below-equal
	:boolean-above-equal
	:boolean-zf=1
	:boolean-zf=0
	:boolean-cf=1
	:boolean-cf=0
	:boolean-ecx
	:boolean-overflow
	:boolean-no-overflow))
  
  (defconstant +multiple-value-result-modes+
      '(:multiple-values
	:function)))

;; Mode :boolean-ecx takes two parameters: the true value and the false value.

(defmacro post-incf (place &optional (delta 1) &environment env)
  (multiple-value-bind (dummies vals new setter getter)
      (get-setf-expansion place env)
    `(let* (,@(mapcar #'list dummies vals) (,(car new) ,getter))
       (prog1 ,(car new)
         (setq ,(car new) (+ ,(car new) ,delta))
         ,setter))))

(defmacro default-compiler-values-producer () nil)

(defun valid-finals (&rest final-form-values)
  (not (some (lambda (x) (eq x 'unknown-final-form)) final-form-values)))

(defun modifies-union (x y)
  (if (or (eq x t) (eq y t))
      t
    (union x y)))

(defun modifies-member (item set)
  (or (eq set t) (member item set :test #'eq)))

;;; Upstream values
;;; ===============
;;; code:         Assembly code (required, may be nothing).
;;; returns:      The returns mode of code (required).
;;; functional-p: The code has no side-effects.
;;; producer:     The name of the compiler function that generated code.
;;; type:         The (lisp) type of the value(s) returned by code.
;;; modifies:     The set of lexical bindings modified by code, or t for unknown.
;;; final-form:   The fully-expanded form that got compiled.
;;;               For self-evaluating objects, a movitz-object (from storage-types.lisp).
;;;               For lexical bindings, the binding object.
;;;               For function applications, the form (<function-name> <args> ..)
;;;               For dynamic loads, the symbol.

(defmacro compiler-values ((&optional default-values &key abstract)
			   &key (code nil code-p)
				(returns :nothing returns-p)
				(functional-p (null code) functional-p-p)
				(producer '(default-compiler-values-producer) producer-p)
				(modifies (if (eq t functional-p) nil t) modifies-p)
				(type ''(values &rest t) type-p)
				(final-form ''unknown-final-form final-form-p))
  "Return the compiler-values as provided by the &key arguments. DEFAULT-VALUES names
an &all variable from compiler-values-bind whose values will be used as defaults in the
absence of values explicitly passed. If ABSTRACT is true, it means these compiler-values does
not represent actual code, and certain consistency rules will not be enforced."
  (if (not default-values)
      (progn
	(assert (or abstract
		    (eq :nothing returns)
		    code-p) ()
	  "Returning CODE and RETURNS is mandatory ~@[for ~A ~]in the compiler protocol."
	  producer)
	`(values ,code ,returns ,functional-p ,producer ,modifies ,type ,final-form))
    `(values ,(if code-p code `(,default-values :code))
	     ,(if returns-p returns `(,default-values :returns))
	     ,(if functional-p-p functional-p `(,default-values :functional-p))
	     ,(if producer-p producer `(,default-values :producer))
	     ,(if modifies-p modifies `(,default-values :modifies))
	     ,(if type-p type `(,default-values :type))
	     ,(if final-form-p final-form `(,default-values :final-form)))))

(defmacro compiler-values-bind ((&key ((&all all))
				      ((&code code) (gensym) code-p)
				      ((&returns returns) (gensym) returns-p)
				      ((&functional-p functional-p) (gensym) functional-p-p)
				      ((&producer producer) (gensym) producer-p)
				      ((&modifies modifies) (gensym) modifies-p)
				      ((&type type) (gensym) type-p)
				      ((&final-form final-form) (gensym) final-form-p))
				form &body body)
  "Run BODY with variables lexically bound to the compiler-values returned by FORM. &all names a
variable that will represent all the compiler-values, to be passed on as default-values to
COMPILER-VALUES."
  (if (not all)
      `(multiple-value-bind (,code ,returns ,functional-p ,producer ,modifies ,type ,final-form)
	   ,form
	 (declare (ignore ,@(unless code-p (list code))
			  ,@(unless returns-p (list returns))
			  ,@(unless functional-p-p (list functional-p))
			  ,@(unless producer-p (list producer))
			  ,@(unless modifies-p (list modifies))
			  ,@(unless type-p (list type))
			  ,@(unless final-form-p (list final-form))))
	 ,@body)
    `(multiple-value-bind (,code ,returns ,functional-p ,producer ,modifies ,type ,final-form)
	 ,form
       (declare (ignorable ,@(unless code-p (list code))
			   ,@(unless returns-p (list returns))
			   ,@(unless functional-p-p (list functional-p))
			   ,@(unless producer-p (list producer))
			   ,@(unless modifies-p (list modifies))
			   ,@(unless type-p (list type))
			   ,@(unless final-form-p (list final-form))))
       (macrolet ((,all (x)
		    (ecase x
		      (:code ',code) (:returns ',returns) (:functional-p ',functional-p)
		      (:producer ',producer) (:modifies ',modifies) (:type ',type)
		      (:final-form ',final-form))))
	 ,@body))))

(defmacro compiler-values-list (&rest compiler-values-spec)
  "Wrap up compiler-values in a list."
  `(multiple-value-list (compiler-values ,@compiler-values-spec)))

(defmacro compiler-values-list-bind (var-specs form &body body)
  "Unwrap compiler-values from a list."
  `(compiler-values-bind ,var-specs
       (values-list ,form)
     ,@body))

(defmacro compiler-values-getf (values indicator)
  `(compiler-values-list-bind (&all my-values) ,values (my-values ,indicator)))

(defmacro define-compiler (name
			   (&key ((&all all-var) nil all-p)
				 ((&form form-var) (copy-symbol 'form) form-p)
				 ((&funobj funobj-var) (copy-symbol 'funobj) funobj-p)
				 ((&env env-var) (copy-symbol 'env) env-p)
				 ((&top-level-p top-level-p-var) (copy-symbol 'top-level-p) top-level-p-p)
				 ((&result-mode result-mode-var) (copy-symbol 'result-mode) result-mode-p)
				 ((&extent extent-var) (copy-symbol 'extent) extent-p))
			   &body defun-body)
  (multiple-value-bind (body docstring)
      (if (and (cdr defun-body)
	       (stringp (car defun-body)))
	  (values (cdr defun-body) (list (car defun-body)))
	(values defun-body nil))
    `(defun ,name (,form-var ,funobj-var ,env-var ,top-level-p-var ,result-mode-var ,extent-var)
       ,@docstring
       (declare (,(if all-p 'ignorable 'ignore)
		    ,@(unless form-p (list form-var))
		  ,@(unless funobj-p (list funobj-var))
		  ,@(unless env-p (list env-var))
		  ,@(unless top-level-p-p (list top-level-p-var))
		  ,@(unless result-mode-p (list result-mode-var))
		  ,@(unless extent-p (list extent-var))))
       (macrolet ((default-compiler-values-producer () '',name)
		  ,@(when all-p
		      `((,all-var (v) (ecase v (:form ',form-var) (:funobj ',funobj-var)
					     (:env ',env-var) (:top-level-p ',top-level-p-var)
					     (:result-mode ',result-mode-var)
					     (:extent ',extent-var))))))
	 ,@body))))

(defmacro compiler-call (compiler-name &rest all-keys
			 &key defaults forward with-stack-used modify-accumulate
			      ((:form form-var) nil form-p)
			      ((:funobj funobj-var) nil funobj-p)
			      ((:env env-var) nil env-p)
			      ((:extent extent-var) nil extent-p)
			      ((:top-level-p top-level-p-var) nil top-level-p-p)
			      ((:result-mode result-mode-var) :ignore result-mode-p))
  (assert (not (and defaults forward)) ()
    "Both :defaults and :forward can't be specified.")
  (cond
   (modify-accumulate
    `(compiler-values-bind (&all save-all &modifies keep-modifies)
	 (compiler-call ,compiler-name :modify-accumulate nil ,@all-keys)
       (setf ,modify-accumulate (modifies-union ,modify-accumulate keep-modifies))
       (compiler-values (save-all))))
   (defaults
       `(let* ((outer-env ,(if env-p env-var `(,defaults :env)))
	       (inner-env ,(if (not with-stack-used)
			       `outer-env
			     `(make-instance 'with-things-on-stack-env
				:uplink outer-env :stack-used ,with-stack-used
				:funobj (movitz-environment-funobj outer-env)))))
	  (funcall ,compiler-name
		   ,(if form-p form-var `(,defaults :form))
		   ,(if funobj-p funobj-var `(,defaults :funobj))
		   inner-env
		   ,(when top-level-p-p top-level-p-var) ; default to nil, no forwarding.
		   ,(if result-mode-p result-mode-var `(,defaults :result-mode))
		   ,(if extent-p extent-var `(,defaults :extent)))))
   (forward
    `(let* ((outer-env ,(if env-p env-var `(,forward :env)))
	    (inner-env ,(if (not with-stack-used)
			    `outer-env
			  `(make-instance 'with-things-on-stack-env
			     :uplink outer-env :stack-used ,with-stack-used
			     :funobj (movitz-environment-funobj outer-env)))))

       (funcall ,compiler-name
		,(if form-p form-var `(,forward :form))
		,(if funobj-p funobj-var `(,forward :funobj))
		inner-env
		,(if top-level-p-p top-level-p-var `(,forward :top-level-p))
		,(if result-mode-p result-mode-var `(,forward :result-mode))
		,(if extent-p extent-var `(,forward :extent)))))
   ((not with-stack-used)
    `(funcall ,compiler-name ,form-var ,funobj-var ,env-var
	      ,top-level-p-var ,result-mode-var ,extent-var))
   (t (assert env-p () ":env is required when with-stack-used is given.")
      `(funcall ,compiler-name ,form-var ,funobj-var
		(make-instance 'with-things-on-stack-env
		  :uplink ,env-var :stack-used ,with-stack-used
		  :funobj (movitz-environment-funobj ,env-var))
		,top-level-p-var ,result-mode-var ,extent-var))))

(defmacro define-special-operator (name formals &body body)
  (let* ((movitz-name (intern (symbol-name (translate-program name :cl :muerte.cl))
			   :muerte))
	 (fname (intern (with-standard-io-syntax
			  (format nil "~A-~A" 'special-operator movitz-name)))))
    `(progn
       (eval-when (:compile-toplevel :load-toplevel :execute)
	 (export ',movitz-name (symbol-package ',movitz-name)))
       (setf (movitz-env-symbol-function ',movitz-name *persistent-movitz-environment*)
	 (make-instance 'movitz-special-operator
	   'compiler ',fname))
       (define-compiler ,fname ,formals
	 (block ,name ,@body)))))

(defmacro compiler-values-setq ((&key ((&code code-var) nil code-p)
				      ((&returns returns-var) nil returns-p))
				values-form)
  (let ((code-tmp (gensym))
	(returns-tmp (gensym)))
    `(compiler-values-bind (,@(when code-p `(&code ,code-tmp))
			    ,@(when returns-p `(&returns ,returns-tmp)))
	 ,values-form
       (setq ,@(when code-p `(,code-var ,code-tmp))
	     ,@(when returns-p `(,returns-var ,returns-tmp))))))

(defmacro with-labels ((prefix labels) &body body)
  `(let ,(loop for label in labels
	     collect `(,label (gensym ,(format nil "~A-~A" prefix label))))
     ,@body))
