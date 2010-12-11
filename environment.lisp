;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      environment.lisp
;;;; Description:   Compiler environment.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov  3 11:40:15 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: environment.lisp,v 1.24 2008-04-27 19:16:16 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defun setf-name (name)
  "If NAME is on the form (setf <x>), return <x>. Otherwise return NIL."
  (and (listp name)
       (= 2 (length name))
       (eq 'muerte.cl:setf (first name))
       (second name)))

;;;;;;;

(defclass movitz-macro ()
  ((expander-function
    :initarg expander-function
    :reader movitz-macro-expander-function)))

(defclass movitz-special-operator (movitz-macro)
  ((expander-function
    :initform nil)
   (compiler-function
    :initarg compiler
    :reader movitz-special-operator-compiler-function)))

(defclass movitz-environment ()
  ((uplink
    :initarg :uplink
    :initform nil
    :reader movitz-environment-uplink)
   (extent-uplink
    :initarg :extent-uplink
    :accessor movitz-environment-extent-uplink)
   (funobj
    :initarg :funobj
    :reader movitz-environment-funobj)))

(defmethod initialize-instance :after ((instance movitz-environment) &rest x)
  (declare (ignore x))
  (unless (slot-boundp instance 'extent-uplink)
    (setf (movitz-environment-extent-uplink instance)
      (movitz-environment-uplink instance))))

(defmethod movitz-environment-macros ((env movitz-environment))
  (load-time-value (make-hash-table :test #'eq)))
(defmethod movitz-environment-compiler-macros ((env movitz-environment))
  (load-time-value (make-hash-table :test #'eq)))
(defmethod movitz-environment-function-cells ((env movitz-environment))
  (load-time-value (make-hash-table :test #'eq)))
(defmethod movitz-environment-modifies-stack ((env movitz-environment))
  "nil: no stack modification.
t: some (unknown amount) stack modified.
integer: that many words pushed on stack."
  nil)
(defmethod movitz-environment-bindings ((env movitz-environment))
  nil)
(defmethod movitz-environment-plists ((env movitz-environment))
  nil)
(defmethod stack-used ((env movitz-environment)) 0)
(defmethod num-specials ((x movitz-environment)) 0)
(defmethod num-dynamic-slots ((x movitz-environment)) 0)

(defclass global-env (movitz-environment)
  ((properties
    :initform nil
    :accessor movitz-environment-properties)
   (function-cells
    :initarg :function-cells
    :initform (make-hash-table :test #'eq :size 11)
    :reader movitz-environment-function-cells)
   (setf-function-names
    :initform (make-hash-table :test #'eq :size 11)
    :accessor movitz-environment-setf-function-names)
   (plists				; this is a plist of plists
    :initform nil
    :accessor movitz-environment-plists)
   (bindings
    :initform nil
    :accessor movitz-environment-bindings)
   (macros
    :initform (make-hash-table :test #'eq :size 400)
    :accessor movitz-environment-macros)
   (compiler-macros
    :initform (make-hash-table :test #'eq :size 400)
    :accessor movitz-environment-compiler-macros)))

(defclass with-things-on-stack-env (movitz-environment)
  ((stack-used
    :accessor stack-used
    :initarg :stack-used
    :initform 0)
   (num-specials
    :initform 0
    :initarg :num-specials
    :accessor num-specials)))

(defclass progv-env (with-things-on-stack-env)
  ((stack-used
    :initform t)
   (num-specials
    :initform t)))

(defun make-stack-use-env (stack-used)
  (make-instance 'with-things-on-stack-env
    :stack-used stack-used))

(defclass let-env (with-things-on-stack-env)
  ((bindings
    :initform nil
    :accessor movitz-environment-bindings)
   (plists				; this is a plist of plists
    :initform nil
    :accessor movitz-environment-plists)
   (num-specials
    :initform 0
    :initarg :num-specials
    :accessor num-specials)
   (special-variable-shadows
    :initform nil
    :accessor special-variable-shadows)))

(defclass with-dynamic-extent-scope-env (let-env)
  ((save-esp-binding
    :initarg :save-esp-binding
    :accessor save-esp-binding)
   (base-binding
    :initarg :base-binding
    :accessor base-binding)
   (scope-tag
    :initarg :scope-tag
    :reader dynamic-extent-scope-tag)
   (stack-used
    :initform t)
   (members
    :initform nil
    :accessor dynamic-extent-scope-members)))

(defun find-dynamic-extent-scope (env)
  (loop for e = env then (movitz-environment-uplink e)
      while (and e (not (typep e 'funobj-env)))
      do (when (typep e 'with-dynamic-extent-allocation-env)
	   (return (allocation-env-scope e)))))

(defun dynamic-extent-object-offset (scope-env object)
  (loop with offset = 0
      for x in (dynamic-extent-scope-members scope-env)
      do (if (eq x object)
	     (return (* 8 offset))
	   (incf offset (truncate (+ (sizeof x) 4) 8)))))

(defmethod print-object ((env with-dynamic-extent-scope-env) stream)
  (print-unreadable-object (env stream :type t)
    (princ (dynamic-extent-scope-tag env) stream))
  env)

(defclass with-dynamic-extent-allocation-env (movitz-environment)
  ((scope
    :initarg :scope
    :reader allocation-env-scope)))

(defclass funobj-env (let-env)
  ()
  (:documentation "A funobj-env represents the (possibly null)
lexical environment that a closure funobj captures."))

(defclass function-env (let-env)
  ((without-check-stack-limit-p
    :accessor without-check-stack-limit-p
    :initform nil)
   (without-function-prelude-p
    :accessor without-function-prelude-p
    :initform nil)
   (forward-2op
    :accessor forward-2op
    :initform nil)
   (min-args
    :initform 0
    :accessor min-args)
   (max-args
    :initform nil
    :accessor max-args)
   (oddeven-args
    :initform nil
    :accessor oddeven-args)
   (allow-other-keys-p
    :accessor allow-other-keys-p)
   (rest-args-position
    :initform nil
    :accessor rest-args-position)
   (edx-var
    :initform nil
    :accessor edx-var)
   (required-vars
    :initform nil
    :accessor required-vars)
   (optional-vars
    :initform nil
    :accessor optional-vars)
   (rest-var
    :initform nil
    :accessor rest-var)
   (key-vars-p
    :initform nil
    :accessor key-vars-p)
   (key-vars
    :initform nil
    :accessor key-vars)
   (key-decode-map
    :initform nil
    :accessor key-decode-map)
   (key-decode-shift
    :accessor key-decode-shift)
   (aux-vars
    :initform nil
    :accessor aux-vars)
   (need-normalized-ecx-p
    :initarg :need-normalized-ecx-p
    :accessor need-normalized-ecx-p)
   (frame-map
    :accessor frame-map)
   (extended-code
    :accessor extended-code)
   (potentially-lended-bindings
    :initform nil
    :accessor potentially-lended-bindings))
  (:documentation "A function-env represents the initial env. that
the function sets up itself. Its parent env. must be a funobj-env."))

(defun find-function-env (env funobj)
  "Starting from <env>, search for the parent environment that is <funobj>'s top env."
  (assert env () "funobj-env not found!")
  (or (and (typep env 'function-env)
	   (eq funobj (movitz-environment-funobj env))
	   env)
      (find-function-env (movitz-environment-uplink env) funobj)))

(defun sub-env-p (sub-env env)
  "Check if sub-env is a sub-environment (or eq) of env."
  (cond
   ((not sub-env)
    nil)
   ((eq env sub-env)
    t)
   (t (sub-env-p (movitz-environment-uplink sub-env) env))))

(defmethod num-dynamic-slots ((x with-things-on-stack-env))
  (num-specials x))

(defmethod print-object ((object let-env) stream)
  (cond
   ((not *print-pretty*)
    (call-next-method))
   (t (print-unreadable-object (object stream :type t :identity t)
	(format stream "of ~A binding~?"
		(movitz-funobj-name (movitz-environment-funobj object))
		"~#[ nothing~; ~S~; ~S and ~S~:;~@{~#[~; and~] ~S~^,~}~]"
		(mapcar #'binding-name (mapcar #'cdr (movitz-environment-bindings object)))))
      object)))


(defclass operator-env (movitz-environment)
  ((bindings
    :initform nil
    :accessor movitz-environment-bindings)
   (plists				; this is a plist of plists
    :initform nil
    :accessor movitz-environment-plists)))

(defclass lexical-exit-point-env (let-env)
  ((save-esp-variable
    :initarg :save-esp-variable
    :reader save-esp-variable)
   (exit-label
    :initarg :exit-label
    :reader exit-label)
   (exit-result-mode
    :initarg :exit-result-mode
    :reader exit-result-mode)
   (lexical-catch-tag-variable
    :initarg :lexical-catch-tag-variable
    :reader movitz-env-lexical-catch-tag-variable)))

(defclass tagbody-env (lexical-exit-point-env) ())

(defclass unwind-protect-env (movitz-environment)
  ((cleanup-form
    :initarg :cleanup-form
    :reader unwind-protect-env-cleanup-form)))

(defmethod num-dynamic-slots ((x unwind-protect-env)) 1)

(defclass simple-dynamic-env (with-things-on-stack-env)
  ((stack-used
    :initform 4))
  (:documentation "An environment that installs one dynamic-env."))

(defmethod num-dynamic-slots ((x simple-dynamic-env)) 1)
  
(defparameter *movitz-macroexpand-hook*
    #'(lambda (macro-function form environment)
;; 	(break "Expanding form ~W" form)
;;;	(warn "..with body ~W" macro-function)
	(let ((expansion (funcall macro-function form environment)))
	  (cond
	   #+ignore ((member (if (atom form) form (car form))
			     '(setf pcnet-reg) :test #'string=)
		     (warn "Expanded ~S to ~S" form expansion)
		     expansion)
	   (t
	    #+ignore (warn "Expanded ~A:~%~S."
			   (if (atom form) form (car form))
			   expansion)
	    expansion)))))

(defun movitz-macroexpand-1 (form &optional env)
  (let ((movitz-form (translate-program form :cl :muerte.cl)))
    (typecase movitz-form
      (cons
       (let ((expander (movitz-macro-function (car movitz-form) env)))
	 (if (not expander)
	     (values movitz-form nil)
	     (values (translate-program (funcall *movitz-macroexpand-hook* expander movitz-form env)
					:muerte.cl :cl)
		     t))))
      (symbol
       (let ((binding (movitz-binding movitz-form env)))
	 (if (not (typep binding 'symbol-macro-binding))
	     (values movitz-form nil)
	     (values (translate-program (funcall *movitz-macroexpand-hook*
						 (macro-binding-expander binding)
						 movitz-form env)
					:muerte.cl :cl)
		     t))))
      (t (values movitz-form nil)))))

(defun movitz-macroexpand (form &optional env)
  (let ((global-expanded-p nil))
    (loop while
	 (multiple-value-bind (expansion expanded-p)
	     (movitz-macroexpand-1 form env)
	   (when expanded-p
	     (setf form expansion)
	     (setf global-expanded-p expanded-p))))
    (values form global-expanded-p)))

(define-symbol-macro *movitz-global-environment*
    (image-global-environment *image*))

(defun movitz-env-add-binding (env binding &optional (variable (binding-name binding)))
  "Returns the binding."
  (check-type binding binding)
  (check-type variable symbol "a variable name")
  (let ((env (or env *movitz-global-environment*)))
    (assert (not (slot-boundp binding 'env)) (binding)
      "Binding ~S is already associated with ~S, can't also be associated with ~S."
      binding (binding-env binding) env)
    (unless (eq env *movitz-global-environment*)
      (assert (not (assoc variable (movitz-environment-bindings env))) ()
	"Variable ~S is being multiple bound in ~S." variable env))
    (pushnew (cons variable binding)
	     (movitz-environment-bindings env)
	     :key #'car)
    (setf (binding-env binding) env)
    binding))

(defun movitz-env-load-declarations (declarations environment context)
  (loop for (declaration-identifier . data) in declarations
      do (case declaration-identifier
	   ((muerte.cl::ftype muerte.cl::optimize)
	    nil)			; ignore for now
	   (muerte.cl::ignore
	    (dolist (var data)
	      (check-type var symbol)
	      (setf (movitz-env-get var 'ignore nil environment) t)))
	   (muerte.cl::ignorable
	    (dolist (var data)
	      (check-type var symbol)
	      (setf (movitz-env-get var 'ignorable nil environment) t)))
	   (muerte::constant-variable
	    (dolist (var data)
	      (check-type var symbol)
	      (when (eq :declaim context)
		(pushnew :constant-variable (movitz-symbol-flags (movitz-read var))))
	      (setf (movitz-env-get var 'constantp nil environment) t)))
	   (muerte.cl:special
	    (dolist (var data)
	      (check-type var symbol)
	      (when (eq :declaim context)
		(pushnew :special-variable (movitz-symbol-flags (movitz-read var))))
	      (setf (movitz-env-get var 'special nil environment) t)))
	   (muerte.cl:dynamic-extent
	    (dolist (var data)
	      (setf (movitz-env-get var 'dynamic-extent nil environment) t)))
	   (muerte.cl:notinline
	    (dolist (var data)
	      (setf (movitz-env-get var 'notinline nil environment) t)))
	   (muerte.cl:type
	    (destructuring-bind (typespec . vars)
		data
	      (dolist (var vars)
		(setf (movitz-env-get var :variable-type nil environment) typespec))))
	   (muerte::primitive-function
	    (unless (eq :funobj context)
	      (warn "Declaration ~S appeared in context ~S but is only allowed in funobj context."
		    declaration-identifier context))
	    (setf (getf (movitz-environment-properties environment) 'primitive-function) t))
	   (muerte::without-function-prelude
	    (unless (eq :funobj context)
	      (warn "Declaration ~S appeared in context ~S but is only allowed in funobj context."
		    declaration-identifier context))
	    (setf (without-function-prelude-p environment) t))
	   (muerte::without-check-stack-limit
	    (unless (eq :funobj context)
	      (warn "Declaration ~S appeared in context ~S but is only allowed in funobj context."
		    declaration-identifier context))
	    (setf (without-check-stack-limit-p environment) t))
	   (muerte::forward-2op
	    (unless (eq :funobj context)
	      (warn "Declaration ~S appeared in context ~S but is only allowed in funobj context."
		    declaration-identifier context))
	    (let ((symbol (car data)))
	      (check-type symbol symbol "a function name")
	      (setf (forward-2op environment) (movitz-read symbol))))
	   ((muerte::loop-tag)
	    (dolist (var data)
	      (setf (movitz-env-get var declaration-identifier nil environment) t)))
	   (t (let ((typespec declaration-identifier)
		    (vars data))
		(dolist (var vars)
		  (setf (movitz-env-get var :variable-type nil environment) typespec))))))
  environment)
		      
(defun make-local-movitz-environment (uplink funobj
				   &rest init-args
				   &key (type 'global-env)
					declarations declaration-context bindings
				   &allow-other-keys)
  (dolist (p '(:type :declarations :declaration-context :bindings))
    (remf init-args p))
  (let ((env (apply #'make-instance type
		    :uplink (or uplink *movitz-global-environment*)
		    :funobj funobj
		    init-args)))
    (movitz-env-load-declarations declarations env declaration-context)
    (loop for (nil . val) in bindings
	do (movitz-env-add-binding env val))
    env))

(defun make-global-movitz-environment ()
  (let ((env (make-instance 'global-env :uplink nil)))
    (setf (movitz-env-get 'nil 'constantp nil env) t
	  (movitz-env-get 'muerte.cl:t 'constantp nil env) t
	  (symbol-value 'muerte.cl:t) 'muerte.cl:t)
    env))

;;; Bindings
	   
(defun movitz-binding (symbol environment &optional (recurse t))
  (check-type symbol symbol)
  (if (not environment)
      nil
    (let ((local-binding (cdr (assoc symbol (movitz-environment-bindings environment)))))
      (if (typep local-binding '(and binding (not operator-binding)))
	  (values local-binding environment)
	(and recurse (movitz-binding symbol (movitz-environment-uplink environment)))))))

(defun movitz-operator-binding (symbol environment &optional (recurse t))
  (labels ((operator-binding-p (b)
	     (or (typep b 'operator-binding)
		 (and (typep b 'borrowed-binding)
		      (operator-binding-p (borrowed-binding-target b))))))
    (if (not environment)
	nil
      (let ((local-binding (cdr (assoc symbol (movitz-environment-bindings environment)))))
	(if (operator-binding-p local-binding)
	    (values local-binding environment)
	  (and recurse (movitz-operator-binding symbol (movitz-environment-uplink environment))))))))

;;; Accessor: movitz-env-get (symbol property)

(defun movitz-env-get (symbol indicator &optional (default nil)
					       (environment nil)
					       (recurse-p t))
  (loop for env = (or environment *movitz-global-environment*)
     then (when recurse-p (movitz-environment-uplink env))
     for plist = (and env (getf (movitz-environment-plists env) symbol))
     while env
     do (let ((val (getf plist indicator '#0=#:not-found)))
	  (unless (eq val '#0#)
	    (return (values val env))))
     finally (return default)))

(defun (setf movitz-env-get) (val symbol indicator
			   &optional default environment)
  (declare (ignore default))
  (setf (getf (getf (movitz-environment-plists (or environment
						*movitz-global-environment*))
		    symbol)
	      indicator)
    val))
    
;;; Accessor: movitz-env-symbol-function

(defun movitz-env-symbol-function (symbol &optional env)
  (values (gethash symbol (movitz-environment-function-cells (or env *movitz-global-environment*)))))

(defun (setf movitz-env-symbol-function) (value symbol &optional env)
  (setf (gethash symbol (movitz-environment-function-cells (or env *movitz-global-environment*)))
    value))

(defun movitz-env-setf-operator-name (name &optional env)
  "Map an setf operator name like from (setf operator) to a symbol."
  (assert (null env))
  (or #0=(gethash name (movitz-environment-setf-function-names *movitz-global-environment*))
      (let ((setf-symbol (make-symbol
			  (symbol-name name))))
	(setf (symbol-plist setf-symbol) (list :setf-placeholder name)
	      #0# setf-symbol))))
  
(defun movitz-env-named-function (name &optional env)
  (cond
    ((setf-name name)
     (movitz-env-symbol-function (movitz-env-setf-operator-name
                                  (setf-name name) env)))
    ((symbolp name)
     (movitz-env-symbol-function name env))
    (t (error "Not a function name: ~S" name))))

(defun (setf movitz-env-named-function) (value name &optional env)
  (check-type value movitz-funobj)
  (let ((effective-env (or env *movitz-global-environment*)))
    (cond
     ((setf-name name)
      (let* ((sn (setf-name name))
	     (function-name (movitz-env-setf-operator-name sn env)))
	(setf (movitz-env-named-function function-name env) value)))
     ((symbolp name)
      (setf (gethash name (movitz-environment-function-cells effective-env))
	value))
     (t (error "Not a function name: ~S" name)))))

(defun movitz-macro-function (symbol &optional environment)
  (or (let ((binding (movitz-operator-binding symbol (or environment *movitz-global-environment*))))
	(and (typep binding 'macro-binding)
	     (macro-binding-expander binding)))
      (loop for env = (or environment *movitz-global-environment*)
	 then (movitz-environment-uplink env)
	 for val = (when env
		     (gethash symbol (movitz-environment-macros env)))
	 while env
	 when val
	 do (return (movitz-macro-expander-function val)))))

(defun (setf movitz-macro-function) (fun symbol &optional environment)
  (let* ((env (or environment *movitz-global-environment*))
	 (obj (or (gethash symbol (movitz-environment-macros env))
		  (setf (gethash symbol (movitz-environment-macros env))
			(make-instance 'movitz-macro)))))
    (setf (slot-value obj 'expander-function) fun)))

;;; Accessor: COMPILER-MACRO-FUNCTION

(defun movitz-compiler-macro-function (name &optional environment)
  (gethash name (movitz-environment-compiler-macros *movitz-global-environment*))
  #+ignore
  (loop for env = (or environment *movitz-global-environment*)
     then (movitz-environment-uplink env)
     for val = (when env
		 (gethash name (movitz-environment-compiler-macros env)))
     while env
     when val do (return val)))

(defun (setf movitz-compiler-macro-function) (fun name &optional environment)
  (setf (gethash name (movitz-environment-compiler-macros (or environment
							      *movitz-global-environment*)))
	fun))

;;; Special operators

(defvar *persistent-movitz-environment* (make-global-movitz-environment))

(defun movitz-special-operator-p (symbol)
  (let ((val (gethash symbol (movitz-environment-function-cells *persistent-movitz-environment*))))
    (typep val 'movitz-special-operator)))

(defun movitz-special-operator-compiler (symbol)
  (movitz-special-operator-compiler-function
   (gethash symbol (movitz-environment-function-cells *persistent-movitz-environment*))))
