;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      special-operators.lisp
;;;; Description:   Compilation of internal special operators.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov 24 16:22:59 2000
;;;;                
;;;; $Id: special-operators.lisp,v 1.59 2008-04-17 19:28:37 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defun ccc-result-to-returns (result-mode)
  (check-type result-mode keyword)
  (case result-mode
    (:ignore :nothing)
    (:function :multiple-values)
    (t result-mode)))

(defun make-compiled-cond-clause (clause clause-num last-clause-p exit-label funobj env result-mode)
  "Return three values: The code for a cond clause,
a boolean value indicating whether the clause's test was constantly true,
The set of modified bindings."
  (assert (not (atom clause)))
  (let* ((clause-modifies nil)
	 (test-form (car clause))
	 (then-forms (cdr clause)))
    (cond
     ((null then-forms)
      (compiler-values-bind (&code test-code &returns test-returns)
	  (compiler-call #'compile-form
	    :modify-accumulate clause-modifies
	    :result-mode (case (operator result-mode)
			   (:boolean-branch-on-false
			    (if last-clause-p
				result-mode
			      (cons :boolean-branch-on-true
				    exit-label)))
			   (:boolean-branch-on-true
			    result-mode)
			   (:ignore
			    (cons :boolean-branch-on-true
				  exit-label))
			   (:push
			    (if last-clause-p
				:push
			      :eax))
			   (#.+multiple-value-result-modes+
			    :eax)
			   (t result-mode))
	    :form test-form
	    :funobj funobj
	    :env env)
	(assert (not (null test-code)) (clause) "null test-code!")
	(values (ecase (operator test-returns)
		  ((:boolean-branch-on-true
		    :boolean-branch-on-false)
		   test-code)
		  (:push
		   (assert last-clause-p)
		   test-code)
		  ((:multiple-values :eax :ebx :ecx :edx)
;;;		   (when (eq result-mode :function)
;;;		     (warn "test-returns: ~S" test-returns))
		   (let ((singlify (when (member result-mode +multiple-value-result-modes+)
				     '((:clc)))))
		     (append test-code
			     (cond
			      ((not last-clause-p)
			       (append
				`((:cmpl :edi ,(single-value-register (operator test-returns))))
				singlify
				(when (eq :push result-mode)
				  `((:pushl ,(single-value-register (operator test-returns)))))
				`((:jne ',exit-label))))
			      (t singlify))))))
		nil)))
     ((not (null then-forms))
      (let ((skip-label (gensym (format nil "cond-skip-~D-" clause-num))))
	(compiler-values-bind (&code test-code)
	    (compiler-call #'compile-form
	      :result-mode (cond
			    ((and last-clause-p
				  (eq (operator result-mode)
				      :boolean-branch-on-false))
			     (cons :boolean-branch-on-false
				   (cdr result-mode)))
			    (t (cons :boolean-branch-on-false
				     skip-label)))
	      :modify-accumulate clause-modifies
	      :form test-form
	      :funobj funobj
	      :env env)
	  (compiler-values-bind (&code then-code &returns then-returns)
	      (compiler-call #'compile-form
		:form (cons 'muerte.cl::progn then-forms)
		:modify-accumulate clause-modifies
		:funobj funobj
		:env env
		:result-mode result-mode)
	    (let ((constantly-true-p (null test-code)))
	      (values (append test-code
			      then-code
			      (unless (or last-clause-p (eq then-returns :non-local-exit))
				`((:jmp ',exit-label)))
			      (unless constantly-true-p
				(list skip-label)))
		      constantly-true-p
		      clause-modifies)))))))))

(defun chose-joined-returns-and-result (result-mode)
  "From a result-mode, determine a joined result-mode (for several branches),
and the correspondig returns mode (secondary value)."
  (let ((joined-result-mode (case (operator result-mode)
			      (:values :multiple-values)
			      ((:ignore :function :multiple-values :eax :ebx :ecx :edx
				:boolean-branch-on-false :boolean-branch-on-true)
			       result-mode)
			      (t :eax))))
    (values joined-result-mode
	    (ecase (operator joined-result-mode)
	      (:ignore :nothing)
	      (:function :multiple-values)
	      ((:multiple-values :eax :push :eax :ebx :ecx :edx
		:boolean-branch-on-true :boolean-branch-on-false)
	       joined-result-mode)))))

(define-special-operator compiled-cond
    (&form form &funobj funobj &env env &result-mode result-mode)
  (let ((clauses (cdr form)))
    (let* ((cond-exit-label (gensym "cond-exit-"))
	   (cond-result-mode (case (operator result-mode)
			       (:values :multiple-values)
			       ((:ignore :function :multiple-values :eax :ebx :ecx :edx
				 :boolean-branch-on-false :boolean-branch-on-true)
				result-mode)
			       (t :eax)))
	   (cond-returns (ecase (operator cond-result-mode)
			   (:ignore :nothing)
			   (:function :multiple-values)
			   ((:multiple-values :eax :push :eax :ebx :ecx :edx
			     :boolean-branch-on-true :boolean-branch-on-false)
			    cond-result-mode)))
	   (only-control-p (member (operator cond-result-mode)
				   '(:ignore
				     :boolean-branch-on-true
				     :boolean-branch-on-false))))
      (loop with last-clause-num = (1- (length clauses))
	  for clause in clauses
	  for clause-num upfrom 0
	  as (clause-code constantly-true-p) =
	    (multiple-value-list
	     (make-compiled-cond-clause clause
					clause-num
					(and only-control-p
					     (= clause-num last-clause-num))
					cond-exit-label funobj env cond-result-mode))
	  append clause-code into cond-code
	  when constantly-true-p
	  do (return (compiler-values ()
		       :returns cond-returns
		       :code (append cond-code
				     (list cond-exit-label))))
	  finally
	    (return (compiler-values ()
		      :returns cond-returns
		      :code (append cond-code
				    ;; no test succeeded => nil
				    (unless only-control-p
				      (compiler-call #'compile-form
					:form nil
					:funobj funobj
					:env env
					:top-level-p nil
					:result-mode cond-result-mode))
				    (list cond-exit-label))))))))


(define-special-operator compiled-case (&all all &form form &result-mode result-mode)
  (destructuring-bind (keyform &rest clauses)
      (cdr form)
    #+ignore
    (let ((cases (loop for (clause . nil) in clauses
		     append (if (consp clause)
				clause
			      (unless (member clause '(nil muerte.cl:t muerte.cl:otherwise))
				(list clause))))))
      (warn "case clauses:~%~S" cases))
    (compiler-values-bind (&code key-code &returns key-returns)
	(compiler-call #'compile-form-unprotected
	  :result-mode :eax
	  :forward all
	  :form keyform)
      (multiple-value-bind (case-result-mode case-returns)
	  (chose-joined-returns-and-result result-mode)
	(let ((key-reg (accept-register-mode key-returns)))
	  (flet ((otherwise-clause-p (x)
		   (member (car x) '(muerte.cl:t muerte.cl:otherwise)))
		 (make-first-check (key then-label then-code exit-label)
		   `((:load-constant ,key ,key-reg :op :cmpl)
		     (:je '(:sub-program (,then-label)
			    ,@then-code
			    (:jmp ',exit-label))))))
	    (cond
	     ((otherwise-clause-p (first clauses))
	      (compiler-call #'compile-implicit-progn
		:forward all
		:form (rest (first clauses))))
	     (t (compiler-values ()
		  :returns case-returns
		  :code (append (make-result-and-returns-glue key-reg key-returns key-code)
				(loop with exit-label = (gensym "case-exit-")
				    for clause-head on clauses
				    as clause = (first clause-head)
				    as keys =  (first clause)
				    as then-forms = (rest clause)
				    as then-label = (gensym "case-then-")
				    as then-code = (compiler-call #'compile-form
						     :result-mode case-result-mode
						     :forward all
						     :form `(muerte.cl:progn ,@then-forms))
				    if (otherwise-clause-p clause)
				    do (assert (endp (rest clause-head)) ()
					 "Case's otherwise clause must be the last clause.")
				    and append then-code
				    else if (atom keys)
				    append (make-first-check keys then-label then-code exit-label)
				    else append (make-first-check (first keys) then-label
								  then-code exit-label)
				    and append (loop for key in (rest keys)
						   append `((:load-constant ,key ,key-reg :op :cmpl)
							    (:je ',then-label)))
				    if (endp (rest clause-head))
				    append (append (unless (otherwise-clause-p clause)
						     (compiler-call #'compile-form
						       :result-mode case-result-mode
						       :forward all
						       :form nil))
						   (list exit-label)))))))))))))
					     
(define-special-operator compile-time-find-class (&all all &form form)
  (destructuring-bind (class-name)
      (cdr form)
    (compiler-call #'compile-form-unprotected
      :form (muerte::movitz-find-class class-name)
      :forward all)))
	     
(define-special-operator make-named-function (&form form &env env)
  (destructuring-bind (name formals declarations docstring body &key (type :standard-function))
      (cdr form)
    (declare (ignore docstring))
    (handler-bind (#+ignore ((or error warning) (lambda (c)
					 (declare (ignore c))
					 (format *error-output* "~&;; In function ~S:~&" name))))
      (let* ((*compiling-function-name* name)
	     (funobj (make-compiled-funobj name formals declarations body env nil)))
	(setf (movitz-funobj-type funobj) type)
	(setf (movitz-funobj-symbolic-name funobj) name)
	(setf (movitz-env-named-function name) funobj))))
  (compiler-values ()))

(define-special-operator make-primitive-function (&form form &env env)
  (destructuring-bind (name docstring body)
      (cdr form)
    (destructuring-bind (name &key symtab-property)
	(if (consp name) name (list name))
      (handler-bind (((or warning error)
		      (lambda (c)
			(declare (ignore c))
			(format *error-output* "~&;; In primitive function ~S:" name))))
	(multiple-value-bind (code-vector symtab)
	    (make-compiled-primitive body env nil docstring)
	  (setf (movitz-symbol-value (movitz-read name)) code-vector)
	  (when symtab-property
	    (setf (movitz-env-get name :symtab)
	      (muerte::translate-program symtab :movitz :muerte)))
	  (compiler-values ()))))))

(define-special-operator define-prototyped-function (&form form)
  (destructuring-bind (function-name proto-name &rest parameters)
      (cdr form)
    (let* ((funobj-proto (movitz-env-named-function proto-name))
	   (funobj (make-instance 'movitz-funobj
		     :name (movitz-read function-name)
		     :code-vector (movitz-funobj-code-vector funobj-proto)
		     :code-vector%1op (movitz-funobj-code-vector%1op funobj-proto)
		     :code-vector%2op (movitz-funobj-code-vector%2op funobj-proto)
		     :code-vector%3op (movitz-funobj-code-vector%3op funobj-proto)
		     :lambda-list (movitz-funobj-lambda-list funobj-proto)
		     :num-constants (movitz-funobj-num-constants funobj-proto)
		     :num-jumpers (movitz-funobj-num-jumpers funobj-proto)
		     :jumpers-map (movitz-funobj-jumpers-map funobj-proto)
		     :symbolic-code (when (slot-boundp funobj-proto 'symbolic-code)
				      (movitz-funobj-symbolic-code funobj-proto))
		     :const-list (let ((c (copy-list (movitz-funobj-const-list funobj-proto))))
				   (loop for (lisp-parameter value) in parameters
				       as parameter = (movitz-read lisp-parameter)
				       do (assert (member parameter c) ()
					    "~S is not a function prototype parameter for ~S. ~
The valid parameters are~{ ~S~}."
					    parameter proto-name
					    (mapcar #'movitz-print (movitz-funobj-const-list funobj-proto)))
					  (setf (car (member parameter c))
					    (if (and (consp value)
						     (eq :movitz-find-class (car value)))
						(muerte::movitz-find-class (cadr value))
					      (movitz-read value))))
				   c))))
      (setf (movitz-funobj-symbolic-name funobj) function-name)
      (setf (movitz-env-named-function function-name) funobj)
      (compiler-values ()))))

(define-special-operator define-setf-expander-compile-time (&form form)
  (destructuring-bind (access-fn lambda-list macro-body)
      (cdr form)
    (multiple-value-bind (wholevar envvar reqvars optionals restvar keyvars auxvars)
	(decode-macro-lambda-list lambda-list)
      (let ((cl-lambda-list (translate-program `(,@reqvars
						 ,@(when optionals '(&optional)) ,@optionals
						 ,@(when restvar `(&rest ,restvar))
						 ,@(when keyvars '(&key)) ,@keyvars
						 ,@(when auxvars '(&aux)) ,@auxvars)
					       :muerte.cl :cl))
	    (cl-macro-body (translate-program macro-body :muerte.cl :cl)))
	(multiple-value-bind (cl-body declarations doc-string)
	    (parse-docstring-declarations-and-body cl-macro-body 'cl:declare)
	  (declare (ignore doc-string))
	  (setf (movitz-env-get access-fn 'muerte::setf-expander nil)
	    (let* ((form-formal (or wholevar (gensym)))
		   (env-formal (or envvar (gensym)))
		   (expander (if (null cl-lambda-list)
				 `(lambda (,form-formal ,env-formal)
				    (declare (ignorable ,form-formal ,env-formal)
					     ,@declarations)
				    (translate-program (block ,access-fn ,@cl-body) :cl :muerte.cl))
			       `(lambda (,form-formal ,env-formal)
				  (declare (ignorable ,form-formal ,env-formal)
					   ,@declarations)
				  (destructuring-bind ,cl-lambda-list
				      (translate-program (rest ,form-formal) :muerte.cl :cl)
				    (values-list
				     (translate-program (multiple-value-list (block ,access-fn ,@cl-body))
							:cl :muerte.cl)))))))
	      (movitz-macro-expander-make-function expander :type :setf :name access-fn)))))))
  (compiler-values ()))

(define-special-operator muerte::defmacro/compile-time (&form form)
  (destructuring-bind (name lambda-list macro-body)
      (cdr form)
    (check-type name symbol "a macro name")
    (multiple-value-bind (wholevar envvar reqvars optionals restvar keyvars auxvars)
	(decode-macro-lambda-list lambda-list)
      (let ((expander-name (make-symbol (format nil "~A-macro" name)))
	    (cl-lambda-list (translate-program `(,@reqvars
						 ,@(when optionals '(&optional)) ,@optionals
						 ,@(when restvar `(&rest ,restvar))
						 ,@(when keyvars '(&key)) ,@keyvars
						 ,@(when auxvars '(&aux)) ,@auxvars)
					       :muerte.cl :cl))
	    (cl-macro-body (translate-program macro-body :muerte.cl :cl)))
	(when (member name (image-called-functions *image*) :key #'first)
	  (warn "Macro ~S defined after being called as function (first in ~S)."
		name
		(cdr (find name (image-called-functions *image*) :key #'first))))
	(multiple-value-bind (cl-body declarations doc-string)
	    (parse-docstring-declarations-and-body cl-macro-body 'cl:declare)
	  (declare (ignore doc-string))
	  (let ((expander-lambda
		 (let ((form-formal (or wholevar (gensym)))
		       (env-formal (or envvar (gensym))))
		   (if (null cl-lambda-list)
		       `(lambda (,form-formal ,env-formal)
			  (declare (ignorable ,form-formal ,env-formal))
			  (declare ,@declarations)
			  (translate-program  (block ,name ,@cl-body) :cl :muerte.cl))
		     `(lambda (,form-formal ,env-formal)
			(declare (ignorable ,form-formal ,env-formal))
			(destructuring-bind ,cl-lambda-list
			    (translate-program (rest ,form-formal) :muerte.cl :cl)
			  (declare ,@declarations)
			  (translate-program  (block ,name ,@cl-body) :cl :muerte.cl)))))))
	    (setf (movitz-macro-function name)
		  (movitz-macro-expander-make-function expander-lambda
						       :name expander-name
						       :type :defmacro)))))))
  (compiler-values ()))

(define-special-operator muerte::define-compiler-macro-compile-time (&form form)
  ;; This scheme doesn't quite cut it..
  (destructuring-bind (name lambda-list doc-dec-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-docstring-declarations-and-body doc-dec-body)
      (let ((operator-name (or (and (setf-name name)
				    (movitz-env-setf-operator-name (setf-name name)))
			       name)))
	(multiple-value-bind (wholevar envvar reqvars optionals restvar keyvars auxvars)
	    (decode-macro-lambda-list lambda-list)
	  (let ((cl-lambda-list (translate-program `(,@reqvars
						     ,@(when optionals '(&optional)) ,@optionals
						     ,@(when restvar `(&rest ,restvar))
						     ,@(when keyvars '(&key)) ,@keyvars
						     ,@(when auxvars '(&aux)) ,@auxvars)
						   :muerte.cl :cl))
		(cl-body (translate-program body :muerte.cl :cl))
		(declarations (translate-program declarations :muerte.cl :cl))
		(form-formal (or wholevar (gensym)))
		(env-formal (or envvar (gensym)))
		(expansion-var (gensym)))
	    (when (member operator-name (image-called-functions *image*) :key #'first)
	      (warn "Compiler-macro ~S defined after being called as function (first in ~S)"
		    operator-name
		    (cdr (find operator-name (image-called-functions *image*) :key #'first))))
	    (let ((expander
		   `(lambda (,form-formal ,env-formal)
		      (declare (ignorable ,env-formal))
		      (destructuring-bind ,cl-lambda-list
			  (translate-program (rest ,form-formal) :muerte.cl :cl)
			(declare ,@declarations)
			(let ((,expansion-var (block ,operator-name ,@cl-body)))
			  (if (eq ,form-formal ,expansion-var)
			      ,form-formal ; declined
			    (translate-program ,expansion-var :cl :muerte.cl)))))))
	      (setf (movitz-compiler-macro-function operator-name nil)
		(movitz-macro-expander-make-function expander
						     :name name
						     :type :compiler-macro))))))))
  (compiler-values ()))

(define-special-operator muerte::with-inline-assembly-case
    (&all forward &form form &funobj funobj &env env &result-mode result-mode)
  (destructuring-bind (global-options &body inline-asm-cases)
      (cdr form)
    (destructuring-bind (&key (side-effects t) ((:type global-type)))
	global-options
      (let ((modifies ()))
	(loop for case-spec in inline-asm-cases
	    finally (error "Found no inline-assembly-case matching ~S." result-mode)
	    do (destructuring-bind ((matching-result-modes &optional (returns :same)
							   &key labels (type global-type))
				    &body inline-asm)
		   (cdr case-spec)
		 (when (eq returns :same)
		   (setf returns 
		     (case result-mode
		       (:function :multiple-values)
		       (t result-mode))))
		 (when (flet ((match (matching-result-mode)
				(or (eq 'muerte.cl::t matching-result-mode)
				    (eq t matching-result-mode)
				    (eq (operator result-mode) matching-result-mode)
				    (and (eq :register matching-result-mode)
					 (member result-mode '(:eax ebx ecx edx :single-value))))))
			 (if (symbolp matching-result-modes)
			     (match matching-result-modes)
			   (find-if #'match matching-result-modes)))
		   (case returns
		     (:register
		      (setf returns (case result-mode
				      ((:eax :ebx :ecx :edx) result-mode)
				      (t :eax)))))
		   (unless type
		     (setf type
		       (ecase (operator returns)
			 ((:nothing) nil)
			 ((:eax :ebx :ecx :edx) t)
			 (#.+boolean-modes+ t)
			 ((:boolean-branch-on-false
			   :boolean-branch-on-true) t)
			 ((:multiple-values) '(values &rest t)))))
		   (return
		     (let ((amenv (make-assembly-macro-environment))) ; XXX this is really wasteful..
		       (setf (assembly-macro-expander :branch-when amenv)
			 #'(lambda (expr)
			     (destructuring-bind (boolean-mode)
				 (cdr expr)
			       (ecase (operator result-mode)
				 ((:boolean-branch-on-true :boolean-branch-on-false)
				  (list (make-branch-on-boolean boolean-mode (operands result-mode)
								:invert nil)))))))
		       (setf (assembly-macro-expander :compile-form amenv)
			 #'(lambda (expr)
			     (destructuring-bind ((&key ((:result-mode sub-result-mode))) sub-form)
				 (cdr expr)
			       (case sub-result-mode
				 (:register
				  (setf sub-result-mode returns))
				 (:same
				  (setf sub-result-mode result-mode)))
			       (assert sub-result-mode (sub-result-mode)
				 "Assembly :COMPILE-FORM directive doesn't provide a result-mode: ~S"
				 expr)
			       (compiler-values-bind (&code sub-code &functional-p sub-functional-p
						      &modifies sub-modifies)
				   (compiler-call #'compile-form
				     :defaults forward
				     :form sub-form
				     :result-mode sub-result-mode)
				 ;; if a sub-compile has side-effects, then the entire
				 ;; with-inline-assembly form does too.
				 (unless sub-functional-p
				   (setq side-effects t))
				 (setf modifies (modifies-union modifies sub-modifies))
				 sub-code))))
		       (setf (assembly-macro-expander :offset amenv)
			 #'(lambda (expr)
			     (destructuring-bind (type slot &optional (extra 0))
				 (cdr expr)
			       (let ((mtype (find-symbol (symbol-name type) :movitz))
				     (mslot (find-symbol (symbol-name slot) :movitz)))
				 (assert mtype (mtype) "Type not a Movitz symbol: ~A" type)
				 (assert mslot (mslot) "Slot not a Movitz symbol: ~A" slot)
				 (list (+ (slot-offset mtype mslot)
					  (eval extra)))))))
		       (setf (assembly-macro-expander :returns-mode amenv)
			 #'(lambda (expr)
			     (assert (= 1 (length expr)))
			     (list returns)))
		       (setf (assembly-macro-expander :result-register amenv)
			 #'(lambda (expr)
			     (assert (= 1 (length expr)))
			     (assert (member returns '(:eax :ebx :ecx :edx)))
			     (list returns)))
		       (setf (assembly-macro-expander :result-register-low8 amenv)
			 #'(lambda (expr)
			     (assert (= 1 (length expr)))
			     (assert (member returns '(:eax :ebx :ecx :edx)))
			     (list (register32-to-low8 returns))))
		       (setf (assembly-macro-expander :compile-arglist amenv)
			 #'(lambda (expr)
			     (destructuring-bind (ignore &rest arg-forms)
				 (cdr expr)
			       (declare (ignore ignore))
			       (setq side-effects t)
			       (make-compiled-argument-forms arg-forms funobj env))))
		       (setf (assembly-macro-expander :compile-two-forms amenv)
			 #'(lambda (expr)
			     (destructuring-bind ((reg1 reg2) form1 form2)
				 (cdr expr)
			       (multiple-value-bind (code sub-functional-p sub-modifies)
				   (make-compiled-two-forms-into-registers form1 reg1 form2 reg2
									   funobj env)
				 (unless sub-functional-p
				   (setq side-effects t))
				 (setq modifies (modifies-union modifies sub-modifies))
				 code))))
		       (setf (assembly-macro-expander :call-global-pf amenv)
			 #'(lambda (expr)
			     (destructuring-bind (name)
				 (cdr expr)
			       `((:globally (:call (:edi (:edi-offset ,name))))))))
		       (setf (assembly-macro-expander :call-local-pf amenv)
			 #'(lambda (expr)
			     (destructuring-bind (name)
				 (cdr expr)
			       `((:locally (:call (:edi (:edi-offset ,name))))))))
		       (setf (assembly-macro-expander :warn amenv)
			 #'(lambda (expr)
			     (apply #'warn (cdr expr))
			     nil))
		       (setf (assembly-macro-expander :lexical-store amenv)
			 (lambda (expr)
			   (destructuring-bind (var reg &key (type t) protect-registers)
			       (cdr expr)
			     `((:store-lexical ,(movitz-binding var env) ,reg
					       :type ,type
					       :protect-registers ,protect-registers)))))
		       (setf (assembly-macro-expander :lexical-binding amenv)
			 (lambda (expr)
			   (destructuring-bind (var)
			       (cdr expr)
			     (let ((binding (movitz-binding var env)))
			       (check-type binding binding)
			       (list binding)))))
		       (let ((code (assembly-macroexpand inline-asm amenv)))
			 #+ignore
			 (assert (not (and (not side-effects)
					   (tree-search code '(:store-lexical))))
			     ()
			   "Inline assembly is declared side-effects-free, but contains :store-lexical.")
			 (when labels
			   (setf code (subst (gensym (format nil "~A-" (first labels)))
					     (first labels)
					     code))
			   (dolist (label (rest labels))
			     (setf code (nsubst (gensym (format nil "~A-" label))
						label
						code))))
			 (compiler-values ()
			   :code code
			   :returns returns
			   :type (translate-program type :muerte.cl :cl)
			   :modifies modifies
			   :functional-p (not side-effects))))))))))))


(define-special-operator muerte::declaim-compile-time (&form form &top-level-p top-level-p)
  (unless top-level-p
    (warn "DECLAIM not at top-level."))
  (let ((declaration-specifiers (cdr form)))
    (movitz-env-load-declarations declaration-specifiers *movitz-global-environment* :declaim))
  (compiler-values ()))

(define-special-operator call-internal (&form form)
  (destructuring-bind (if-name &optional argument)
      (cdr form)
    (assert (not argument))
    (compiler-values ()
      :code `((:call (:edi ,(slot-offset 'movitz-run-time-context if-name))))
      :returns :nothing)))

(define-special-operator inlined-not (&all forward &form form &result-mode result-mode)
  (assert (= 2 (length form)))
  (let ((x (second form)))
    (if (eq result-mode :ignore)
	(compiler-call #'compile-form-unprotected
	  :forward forward
	  :form x)
      (multiple-value-bind (not-result-mode result-mode-inverted-p)
	  (cond
	   ((or (member (operator result-mode) +boolean-modes+)
		(member (operator result-mode) '(:boolean-branch-on-false
						 :boolean-branch-on-true)))
	    (values (complement-boolean-result-mode result-mode)
		    t))
	   ((member (operator result-mode) +multiple-value-result-modes+)
	    (values :eax nil))
	   ((member (operator result-mode) '(:push))
	    (values :eax nil))
	   (t (values result-mode nil)))
	(compiler-values-bind (&all not-values &returns not-returns &code not-code &type not-type)
	    (compiler-call #'compile-form-unprotected
	      :defaults forward
	      :form x
	      :result-mode not-result-mode)
	  (setf (not-values :producer)
	    (list :not (not-values :producer)))
	  (let ((not-type (type-specifier-primary not-type)))
	   (setf (not-values :type)
	    (cond
	     ((movitz-subtypep not-type 'null)
	      '(eql t))
	     ((movitz-subtypep not-type '(not null))
	      'null)
	     (t 'boolean))))
	  ;; (warn "res: ~S" result-mode-inverted-p)
	  (cond
	   ((and result-mode-inverted-p
		 (eql not-result-mode not-returns))
	    ;; Inversion by result-mode ok.
	    (compiler-values (not-values)
	      :returns result-mode))
	   (result-mode-inverted-p
	    ;; (warn "Not done: ~S/~S/~S." result-mode not-result-mode not-returns)
	    (multiple-value-bind (code)
		(make-result-and-returns-glue not-result-mode not-returns not-code)
	      (compiler-values (not-values)
		:returns result-mode
		:code code)))
	   ((not result-mode-inverted-p)
	    ;; We must invert returns-mode
	    (case (operator not-returns)
	      (#.(append +boolean-modes+ '(:boolean-branch-on-true :boolean-branch-on-false))
		 (compiler-values (not-values)
		   :returns (complement-boolean-result-mode not-returns)))
;;;	      ((:eax :function :multiple-values :ebx :edx)
;;;	       (case result-mode
;;;		 ((:eax :ebx :ecx :edx :function :multiple-values)
;;;		  (compiler-values (not-values)
;;;		    :code (append (not-values :code)
;;;				  `((:cmpl :edi ,(single-value-register not-returns))
;;;				    (:sbbl :ecx :ecx)
;;;				    (:cmpl ,(1+ (image-nil-word *image*))
;;;					   ,(single-value-register not-returns))
;;;				    (:adcl 0 :ecx)))
;;;		    :returns '(:boolean-ecx 1 0)))
;;;		 (t (compiler-values (not-values)
;;;		      :code (append (not-values :code)
;;;				    `((:cmpl :edi ,(single-value-register not-returns))))
;;;		      :returns :boolean-zf=1))))
	      ((:eax :function :multiple-values :ebx :ecx :edx)
	       (compiler-values (not-values)
		 :code (append (not-values :code)
			       `((:cmpl :edi ,(single-value-register not-returns))))
		 :returns :boolean-zf=1)) ; TRUE iff result equal to :edi/NIL.
	      (otherwise
	       #+ignore
	       (warn "unable to deal intelligently with inlined-NOT not-returns: ~S for ~S from ~S"
		     not-returns not-result-mode (not-values :producer))
	       (let ((label (make-symbol "not-label")))
		 (compiler-values (not-values)
		   :returns :eax
		   :code (append (make-result-and-returns-glue :eax not-returns (not-values :code))
				 `((:cmpl :edi :eax)
				   (:movl :edi :eax)
				   (:jne ',label)
				   (:globally (:movl (:edi (:edi-offset t-symbol)) :eax))
				   ,label)))))))))))))

(define-special-operator muerte::with-progn-results
    (&all forward &form form &top-level-p top-level-p &result-mode result-mode)
  (destructuring-bind (buried-result-modes &body body)
      (cdr form)
    (assert (< (length buried-result-modes) (length body)) ()
      "WITH-PROGN-RESULTS must have fewer result-modes than body elements: ~S" form)
    (loop with returns-mode = :nothing
	with no-side-effects-p = t
	with modifies = nil
	for sub-form on body
	as sub-form-result-mode = buried-result-modes
	then (or (cdr sub-form-result-mode)
		 sub-form-result-mode)
	as current-result-mode = (if (endp (cdr sub-form))
				     ;; all but the last form have result-mode as declared
				     result-mode
				   (car sub-form-result-mode))
	as last-form-p = (endp (cdr sub-form))
			 ;; do (warn "progn rm: ~S" (car sub-form-result-mode))
	appending
	  (compiler-values-bind (&code code &returns sub-returns-mode
				 &functional-p no-sub-side-effects-p
				 &modifies sub-modifies)
	      (compiler-call (if last-form-p
				 #'compile-form-unprotected
			       #'compile-form)
		:defaults forward
		:form (car sub-form)
		:top-level-p top-level-p
		:result-mode current-result-mode)
	    (unless no-sub-side-effects-p
	      (setf no-side-effects-p nil))
	    (setq modifies (modifies-union modifies sub-modifies))
	    (when last-form-p
	      ;; (warn "progn rm: ~S form: ~S" sub-returns-mode (car sub-form))
	      (setf returns-mode sub-returns-mode))
	    (if (and no-sub-side-effects-p (eq current-result-mode :ignore))
		nil
	      code))
	into progn-code
	finally (return (compiler-values ()
			  :code progn-code
			  :returns returns-mode
			  :modifies modifies
			  :functional-p no-side-effects-p)))))

(define-special-operator muerte::simple-funcall (&form form)
  (destructuring-bind (apply-funobj)
      (cdr form)
    (compiler-values ()
      :returns :multiple-values
      :functional-p nil
      :code `((:load-constant ,apply-funobj :esi) ; put function funobj in ESI
	      (:xorl :ecx :ecx)		; number of arguments
					; call new ESI's code-vector
	      (:call (:esi ,(slot-offset 'movitz-funobj 'code-vector)))))))

(define-special-operator muerte::compiled-nth-value (&all all &form form &env env &result-mode result-mode)
  (destructuring-bind (n-form subform)
      (cdr form)
    (cond
     ((movitz-constantp n-form)
      (let ((n (eval-form n-form env)))
	(check-type n (integer 0 *))
	(compiler-values-bind (&code subform-code &returns subform-returns)
	    (compiler-call #'compile-form-unprotected
	      :forward all
	      :result-mode :multiple-values
	      :form subform)
	  (if (not (eq subform-returns :multiple-values))
	      ;; single-value result
	      (case n
		(0 (compiler-values ()
		     :code subform-code
		     :returns subform-returns))
		(t (compiler-call #'compile-implicit-progn
		     :forward all
		     :form `(,subform nil))))
	    ;; multiple-value result
	    (case n
	      (0 (compiler-call #'compile-form-unprotected
		   :forward all
		   :result-mode result-mode
		   :form `(muerte.cl:values ,subform)))
	      (1 (compiler-values ()
		   :returns :ebx
		   :code (append subform-code
				 (with-labels (nth-value (done no-secondary))
				   `((:jnc '(:sub-program (,no-secondary)
					     (:movl :edi :ebx)
					     (:jmp ',done)))
				     (:cmpl 2 :ecx)
				     (:jb ',no-secondary)
				     ,done)))))
	      (t (compiler-values ()
		   :returns :eax
		   :code (append subform-code
				 (with-labels (nth-value (done no-value))
				   `((:jnc '(:sub-program (,no-value)
					     (:movl :edi :eax)
					     (:jmp ',done)))
				     (:cmpl ,(1+ n) :ecx)
				     (:jb ',no-value)
				     (:locally (:movl (:edi (:edi-offset values ,(* 4 (- n 2))))
						      :eax))
				     ,done))))))))))
     (t (error "non-constant nth-values not yet implemented.")))))
	      

(define-special-operator muerte::with-cloak
    (&all all &result-mode result-mode &form form &env env &funobj funobj)
  "Compile sub-forms such that they execute ``invisibly'', i.e. have no impact
on the current result."
  (destructuring-bind ((&optional (cover-returns :nothing) cover-code (cover-modifies t)
				  (cover-type '(values &rest t)))
		       &body cloaked-forms)
      (cdr form)
    (assert (or cover-type (eq cover-returns :nothing)))
    (let ((modifies cover-modifies))
      (cond
       ((null cloaked-forms)
	(compiler-values ()
	  :code cover-code
	  :modifies modifies
	  :type cover-type
	  :returns cover-returns))
       ((or (eq :nothing cover-returns)
	    (eq :ignore result-mode))
	(let* ((code (append cover-code
			     (loop for cloaked-form in cloaked-forms
				 appending
				   (compiler-values-bind (&code code &modifies sub-modifies)
				       (compiler-call #'compile-form-unprotected
					 :forward all
					 :form cloaked-form
					 :result-mode :ignore)
				     (setf modifies (modifies-union modifies sub-modifies))
				     code)))))
	  (compiler-values ()
	    :code code
	    :type nil
	    :modifies modifies
	    :returns :nothing)))
       (t (let* ((cloaked-env (make-instance 'with-things-on-stack-env
				:uplink env
				:funobj funobj))
		 (cloaked-code (loop for cloaked-form in cloaked-forms
				   append (compiler-values-bind (&code code &modifies sub-modifies)
					      (compiler-call #'compile-form-unprotected
						:env cloaked-env
						:defaults all
						:form cloaked-form
						:result-mode :ignore)
					    (setf modifies (modifies-union modifies sub-modifies))
					    code))))
	    (cond
	     ((member cloaked-code
		      '(() ((:cld)) ((:std))) ; simple programs that don't interfere with current-result.
		      :test #'equal)
	      (compiler-values ()
		:returns cover-returns
		:type cover-type
		:modifies modifies
		:code (append cover-code cloaked-code)))
	     ((and (eq :multiple-values cover-returns)
		   (member result-mode '(:function :multiple-values))
		   (type-specifier-num-values cover-type)
		   (loop for i from 0 below (type-specifier-num-values cover-type)
		       always (type-specifier-singleton (type-specifier-nth-value i cover-type))))
	      ;; We cover a known set of values, so no need to push anything.
	      (let ((value-forms
		     (loop for i from 0 below (type-specifier-num-values cover-type)
			 collect
			   (cons 'muerte.cl:quote
				 (type-specifier-singleton
				  (type-specifier-nth-value i cover-type))))))
		(compiler-values ()
		:returns :multiple-values
		:type cover-type
		:code (append cover-code
			      cloaked-code
			      (compiler-call #'compile-form
				:defaults all
				:result-mode :multiple-values
				:form `(muerte.cl:values ,@value-forms))))))
	     ((and (eq :multiple-values cover-returns)
		   (member result-mode '(:function :multiple-values))
		   (type-specifier-num-values cover-type))
	      (when (loop for i from 0 below (type-specifier-num-values cover-type)
			always (type-specifier-singleton (type-specifier-nth-value i cover-type)))
		(warn "Covering only constants: ~S" cover-type))
	      ;; We know the number of values to cover..
	      (let ((num-values (type-specifier-num-values cover-type)))
		;; (warn "Cunningly covering ~D values.." num-values)
		(setf (stack-used cloaked-env) num-values)
		(compiler-values ()
		  :returns :multiple-values
		  :type cover-type
		  :code (append cover-code
				(when (<= 1 num-values)
				  '((:locally (:pushl :eax))))
				(when (<= 2 num-values)
				  '((:locally (:pushl :ebx))))
				(loop for i from 0 below (- num-values 2)
				    collect
				      `(:locally (:pushl (:edi ,(+ (global-constant-offset 'values)
								   (* 4 i))))))
				cloaked-code
				(when (<= 3 num-values)
				  `((:locally (:movl ,(* +movitz-fixnum-factor+
							 (- num-values 2))
						     (:edi (:edi-offset num-values))))))
				(loop for i downfrom (- num-values 2 1) to 0
				    collect
				      `(:locally (:popl (:edi ,(+ (global-constant-offset 'values)
								  (* 4 i))))))
				(when (<= 2 num-values)
				  '((:popl :ebx)))
				(when (<= 1 num-values)
				  '((:popl :eax)))
				(case num-values
				  (1 '((:clc)))
				  (t (append (make-immediate-move num-values :ecx)
					     '((:stc)))))))))
	     ((and (eq :multiple-values cover-returns)
		   (member result-mode '(:function :multiple-values)))
	      (when (type-specifier-num-values cover-type)
		(warn "covering ~D values: ~S." 
		      (type-specifier-num-values cover-type)
		      cover-type))
	      ;; we need a full-fledged m-v-prog1, i.e to save all values of first-form.
	      ;; (lexically) unknown amount of stack is used.
	      (setf (stack-used cloaked-env) t)
	      (compiler-values ()
		:returns :multiple-values
		:modifies modifies
		:type cover-type
		:code (append cover-code
			      (make-compiled-push-current-values)
			      `((:pushl :ecx))
			      cloaked-code
			      `((:popl :ecx)
				(:globally (:call (:edi (:edi-offset pop-current-values))))
				(:leal (:esp (:ecx 4)) :esp)))))
	     ((and (not (cdr cloaked-code))
		   (instruction-is (car cloaked-code) :incf-lexvar))
	      (destructuring-bind (binding delta &key protect-registers)
		  (cdar cloaked-code)
		(let ((protected-register (case cover-returns
					    ((:eax :ebx :ecx :edx) cover-returns)
					    (t :edx))))
		  (assert (not (member protected-register protect-registers)) ()
		    "Can't protect ~S. Sorry, this opertor must be smartened up."
		    protected-register)
		  (compiler-values ()
		    :returns protected-register
		    :type cover-type
		    :code (append cover-code
				  (make-result-and-returns-glue protected-register cover-returns)
				  `((:incf-lexvar ,binding ,delta
						  :protect-registers ,(cons protected-register
									    protect-registers))))))))
	     (t ;; just put the (singular) result of form1 on the stack..
;;;	      (when (not (typep cover-returns 'keyword))
;;;		;; if it's a (non-modified) lexical-binding, we can do better..
;;;		(warn "Covering non-register ~S" cover-returns))
;;;	      (when (type-specifier-singleton (type-specifier-primary cover-type))
;;;		(warn "Covering constant ~S"
;;;		      (type-specifier-singleton cover-type)))  
	      (let ((protected-register (case cover-returns
					  ((:ebx :ecx :edx) cover-returns)
					  (t :eax))))
		#+ignore
		(when (>= 2 (length cloaked-code))
		  (warn "simple-cloaking for ~S: ~{~&~S~}" cover-returns cloaked-code))
		(setf (stack-used cloaked-env) 1)
		(compiler-values ()
		  :returns protected-register
		  :modifies modifies
		  :type cover-type
		  :code (append cover-code
				(make-result-and-returns-glue protected-register cover-returns)
				`((:pushl ,protected-register))
				;; evaluate each rest-form, discarding results
				cloaked-code
				;; pop the result back
				`((:popl ,protected-register)))))))))))))

(define-special-operator muerte::with-local-env (&all all &form form)
  (destructuring-bind ((local-env) sub-form)
      (cdr form)
    (compiler-call #'compile-form-unprotected
      :forward all
      :env local-env
      :form sub-form)))

(define-special-operator muerte::++%2op (&all all &form form &env env &result-mode result-mode)
  (destructuring-bind (term1 term2)
      (cdr form)
    (if (eq :ignore result-mode)
	(compiler-call #'compile-form-unprotected
	  :forward all
	  :form `(muerte.cl:progn term1 term2))
      (let ((returns (ecase (result-mode-type result-mode)
		       ((:function :multiple-values :eax :push) :eax)
		       ((:ebx :ecx :edx) result-mode)
		       ((:lexical-binding) result-mode))))
	(compiler-values ()
	  :returns returns
	  :type 'number
	  :code `((:add ,(movitz-binding term1 env) ,(movitz-binding term2 env) ,returns)))))))

(define-special-operator muerte::include (&form form)
  (let ((*require-dependency-chain*
	 (and (boundp '*require-dependency-chain*)
	      (symbol-value '*require-dependency-chain*))))
    (declare (special *require-dependency-chain*))
    (destructuring-bind (module-name &optional path-spec)
	(cdr form)
      (declare (ignore path-spec))
      (push module-name *require-dependency-chain*)
      (when (member module-name (cdr *require-dependency-chain*))
	(error "Circular Movitz module dependency chain: ~S"
	       (reverse (subseq *require-dependency-chain* 0
				(1+ (position  module-name *require-dependency-chain* :start 1))))))
      (let ((require-path (movitz-module-path form)))
	(movitz-compile-file-internal require-path))))
  (compiler-values ()))

;;;

(define-special-operator muerte::no-macro-call (&all all &form form)
  (destructuring-bind (operator &rest arguments)
      (cdr form)
    (compiler-call #'compile-apply-symbol
      :forward all
      :form (cons operator arguments))))

(define-special-operator muerte::compiler-macro-call (&all all &form form &env env)
  (destructuring-bind (operator &rest arguments)
      (cdr form)
    (let ((name (if (not (setf-name operator))
		    operator
		  (movitz-env-setf-operator-name (setf-name operator)))))
      (assert (movitz-compiler-macro-function name env) ()
	"There is no compiler-macro ~S." name)
      (compiler-call #'compile-compiler-macro-form
	:forward all
	:form (cons name arguments)))))

(define-special-operator muerte::do-result-mode-case (&all all &result-mode result-mode &form form)
  (loop for (cases . then-forms) in (cddr form)
      do (when (or (eq cases 'muerte.cl::t)
		   (and (eq cases :plural)
			(member result-mode +multiple-value-result-modes+))
		   (and (eq cases :booleans)
			(member (result-mode-type result-mode) '(:boolean-branch-on-false :boolean-branch-on-true)))
		   (if (atom cases)
		       (eq cases (result-mode-type result-mode))
		     (member (result-mode-type result-mode) cases)))
	   (return (compiler-call #'compile-implicit-progn
		     :form then-forms
		     :forward all)))
      finally (error "No matching result-mode-case for result-mode ~S." result-mode)))


(define-special-operator muerte::inline-values (&all all &result-mode result-mode &form form)
  (let ((sub-forms (cdr form)))
    (if (eq :ignore result-mode)
	(compiler-call #'compile-implicit-progn ; compile only for side-effects.
	  :forward all
	  :form sub-forms)
      (case (length sub-forms)
	(0 (compiler-values ()
	     :functional-p t
	     :returns :multiple-values
	     :type '(values)
	     :code `((:movl :edi :eax)
		     (:xorl :ecx :ecx)
		     (:stc))))
	(1 (compiler-values-bind (&all sub-form &code code &returns returns &type type)
	       (compiler-call #'compile-form-unprotected
		 :result-mode (if (member result-mode +multiple-value-result-modes+)
				  :eax
				result-mode)
		 :forward all
		 :form (first sub-forms))
	     (compiler-values (sub-form)
	       :type (type-specifier-primary type)
	       :returns (if (eq :multiple-values returns)
			    :eax
			  returns))))
	(2 (multiple-value-bind (code functional-p modifies first-values second-values)
	       (make-compiled-two-forms-into-registers (first sub-forms) :eax
						       (second sub-forms) :ebx
						       (all :funobj)
						       (all :env))
	     (compiler-values ()
	       :code (append code
			     ;; (make-immediate-move 2 :ecx)
			     '((:xorl :ecx :ecx) (:movb 2 :cl))
			     '((:stc)))
	       :returns :multiple-values
	       :type `(values ,(type-specifier-primary (compiler-values-getf first-values :type))
			      ,(type-specifier-primary (compiler-values-getf second-values :type)))
	       :functional-p functional-p
	       :modifies modifies)))
	(t (multiple-value-bind (arguments-code stack-displacement arguments-modifies
				 arguments-types arguments-functional-p)
	       (make-compiled-argument-forms sub-forms (all :funobj) (all :env))
	     (assert (not (minusp (- stack-displacement (- (length sub-forms) 2)))))
	     (multiple-value-bind (stack-restore-code new-returns)
		 (make-compiled-stack-restore (- stack-displacement
						 (- (length sub-forms) 2))
					      result-mode
					      :multiple-values)
	       (compiler-values ()
		 :returns new-returns
		 :type `(values ,@arguments-types)
		 :functional-p arguments-functional-p
		 :modifies arguments-modifies
		 :code (append arguments-code
			       (loop for i from (- (length sub-forms) 3) downto 0
				   collecting
				     `(:locally (:popl (:edi (:edi-offset values ,(* i 4))))))
			       (make-immediate-move (* +movitz-fixnum-factor+ (- (length sub-forms) 2))
						    :ecx)
			       `((:locally (:movl :ecx (:edi (:edi-offset num-values)))))
			       (make-immediate-move (length sub-forms) :ecx)
			       `((:stc))
			       stack-restore-code)))))))))

(define-special-operator muerte::compiler-typecase (&all all &form form)
  (destructuring-bind (keyform &rest clauses)
      (cdr form)
    (compiler-values-bind (&type keyform-type)
	;; This compiler-call is only for the &type..
	(compiler-call #'compile-form-unprotected
	  :form keyform
	  :result-mode :eax
	  :forward all)
;;;      (declare (ignore keyform-type))
;;;      (warn "keyform type: ~S" keyform-type)
;;;      (warn "clause-types: ~S" (mapcar #'car clauses))
      #+ignore
      (let ((clause (find 'muerte.cl::t clauses :key #'car)))
	(assert clause)
	(compiler-call #'compile-implicit-progn
	  :form (cdr clause)
	  :forward all))
      (loop for (clause-type . clause-forms) in clauses
	  when (movitz-subtypep (type-specifier-primary keyform-type) clause-type)
	  return (compiler-call #'compile-implicit-progn
		   :form clause-forms
		   :forward all)
	  finally (error "No compiler-typecase clause matched compile-time type ~S." keyform-type)))))

(define-special-operator muerte::exact-throw (&all all-throw &form form &env env &funobj funobj)
  "Perform a dynamic control transfer to catch-env-slot context (evaluated),
with values from value-form. Error-form, if provided, is evaluated in case the context
is zero (i.e. not found)."
  (destructuring-bind (context value-form &optional error-form)
      (cdr form)
    (let* ((local-env (make-local-movitz-environment env funobj :type 'let-env))
	   (dynamic-slot-binding
	    (movitz-env-add-binding local-env
				    (make-instance 'located-binding
				      :name (gensym "dynamic-slot-"))))
	   (next-continuation-step-binding
	    (movitz-env-add-binding local-env
				    (make-instance 'located-binding
				      :name (gensym "continuation-step-")))))
      (compiler-values ()
	:returns :non-local-exit
	:code (append (compiler-call #'compile-form
			:forward all-throw
			:result-mode dynamic-slot-binding
			:form context)
		      (compiler-call #'compile-form
			:forward all-throw
			:result-mode :multiple-values
			:form `(muerte.cl:multiple-value-prog1
				   ,value-form
				 (muerte::with-inline-assembly (:returns :nothing)
				   (:load-lexical ,dynamic-slot-binding :eax)
				   ,@(when error-form
				       `((:testl :eax :eax)
					 (:jz '(:sub-program ()
						(:compile-form (:result-mode :ignore)
						 ,error-form)))))
				   (:locally (:call (:edi (:edi-offset dynamic-unwind-next))))
				   (:store-lexical ,next-continuation-step-binding :eax :type t)
				   )))
		      ;; now outside of m-v-prog1's cloak, with final dynamic-slot in ..
		      ;; ..unwind it and transfer control.
		      ;;
		      ;; * 12 dynamic-env uplink
		      ;; *  8 target jumper number
		      ;; *  4 target catch tag
		      ;; *  0 target EBP
		      `((:load-lexical ,dynamic-slot-binding :edx)
			(:locally (:movl :edx (:edi (:edi-offset raw-scratch0)))) ; final continuation
			(:load-lexical ,next-continuation-step-binding :edx) ; next continuation-step
			(:locally (:movl :edx (:edi (:edi-offset dynamic-env)))) ; goto target dynamic-env
			(:locally (:call (:edi (:edi-offset dynamic-jump-next))))))))))

;;;			(:locally (:movl :esi (:edi (:edi-offset scratch1))))
			

;;;			(:locally (:movl :edx (:edi (:edi-offset dynamic-env)))) ; exit dynamic-env
;;;			(:movl :edx :esp) ; enter non-local jump stack mode.
;;;			(:movl (:esp) :edx) ; target stack-frame EBP
;;;			(:movl (:edx -4) :esi) ; get target funobj into ESI
;;;			(:movl (:esp 8) :edx) ; target jumper number
;;;			(:jmp (:esi :edx ,(slot-offset 'movitz-funobj 'constant0)))))))))


(define-special-operator muerte::with-basic-restart (&all defaults &form form &env env)
  (destructuring-bind ((name function interactive test format-control
			     &rest format-arguments)
		       &body body)
      (cdr form)
    (check-type name symbol "a restart name")
    (let* ((entry-size (+ 10 (* 2 (length format-arguments)))))
      (with-labels (basic-restart-catch (label-set exit-point))
	(compiler-values ()
	  :returns :multiple-values
;;; Basic-restart entry:
;;;   12: parent
;;;    8: jumper index (=> eip)
;;;    4: tag = #:basic-restart-tag
;;;    0: ebp/stack-frame
;;;   -4: name
;;;   -8: function
;;;  -12: interactive function
;;;  -16: test
;;;  -20: format-control
;;;  -24: (on-stack) list of format-arguments
;;;  -28: cdr
;;;  -32: car ...
	  :code	(append `((:locally (:pushl (:edi (:edi-offset dynamic-env)))) ; parent
			  (:declare-label-set ,label-set (,exit-point))
			  (:pushl ',label-set) ; jumper index
			  (:globally (:pushl (:edi (:edi-offset restart-tag)))) ; tag
			  (:pushl :ebp)	; ebp
			  (:load-constant ,name :push)) ; name
			(compiler-call #'compile-form
			  :defaults defaults
			  :form function
			  :with-stack-used 5
			  :result-mode :push)
			(compiler-call #'compile-form
			  :defaults defaults
			  :form interactive
			  :with-stack-used 6
			  :result-mode :push)
			(compiler-call #'compile-form
			  :defaults defaults
			  :form test
			  :with-stack-used 7
			  :result-mode :push)
			`((:load-constant ,format-control :push)
			  (:pushl :edi))
			(loop for format-argument-cons on format-arguments
			    as stack-use upfrom 11 by 2
			    append
			      (if (cdr format-argument-cons)
				  '((:leal (:esp -15) :eax)
				    (:pushl :eax))
				'((:pushl :edi)))
			    append
			      (compiler-call #'compile-form
				:defaults defaults
				:form (car format-argument-cons)
				:result-mode :push
				:with-stack-used stack-use
				:env env))
			`((:leal (:esp ,(* 4 (+ 6 (* 2 (length format-arguments))))) :eax)
			  (:locally (:movl :eax (:edi (:edi-offset dynamic-env)))))
			(when format-arguments
			  `((:leal (:eax -31) :ebx)
			    (:movl :ebx (:eax -24))))
			(compiler-call #'compile-implicit-progn
			  :forward defaults
			  :env (make-instance 'simple-dynamic-env
				 :uplink env
				 :funobj (defaults :funobj)
				 :num-specials 1)
			  :result-mode :multiple-values
			  :with-stack-used entry-size
			  :form body)
			`((:leal (:esp ,(+ -12 -4 (* 4 entry-size))) :esp)
			  ,exit-point
			  (:movl (:esp) :ebp)
			  (:movl (:esp 12) :edx)
			  (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
			  (:leal (:esp 16) :esp)
			  )))))))


(define-special-operator muerte::eql%b (&form form &env env &result-mode result-mode)
  (destructuring-bind (x y)
      (cdr form)
    (let ((returns (case (result-mode-type result-mode)
		     ((:boolean-branch-on-true :boolean-branch-on-false)
		      result-mode)
		     (t :boolean-zf=1)))
	  (x (movitz-binding x env))
	  (y (movitz-binding y env)))
      (compiler-values ()
	:returns returns
	:code `((:eql ,x ,y ,returns))))))
			     

(define-special-operator muerte::with-dynamic-extent-scope
    (&all all &form form &env env &funobj funobj)
  (destructuring-bind ((scope-tag) &body body)
      (cdr form)
    (let* ((save-esp-binding (make-instance 'located-binding
			       :name (gensym "dynamic-extent-save-esp-")))
	   (base-binding (make-instance 'located-binding
			   :name (gensym "dynamic-extent-base-")))
	   (scope-env
	    (make-local-movitz-environment env funobj
					   :type 'with-dynamic-extent-scope-env
					   :scope-tag scope-tag
					   :save-esp-binding save-esp-binding
					   :base-binding base-binding)))
      (movitz-env-add-binding scope-env save-esp-binding)
      (movitz-env-add-binding scope-env base-binding)
      (compiler-values-bind (&code body-code &all body-values)
	  (compiler-call #'compile-implicit-progn
	    :env scope-env
	    :form body
	    :forward all)
	(compiler-values (body-values)
	  :code (append `((:init-lexvar ,save-esp-binding
					:init-with-register :esp
					:init-with-type fixnum)
			  (:enter-dynamic-scope ,scope-env)
			  (:init-lexvar ,base-binding
					:init-with-register :esp
					:init-with-type fixnum))
			body-code
			`((:load-lexical ,save-esp-binding :esp))))))))

(define-special-operator muerte::with-dynamic-extent-allocation
    (&all all &form form &env env &funobj funobj)
  (destructuring-bind ((scope-tag) &body body)
      (cdr form)
    (let* ((scope-env (loop for e = env then (movitz-environment-uplink e)
			  unless e
			  do (error "Dynamic-extent scope ~S not seen." scope-tag)
			  when (and (typep e 'with-dynamic-extent-scope-env)
				    (eq scope-tag (dynamic-extent-scope-tag e)))
			  return e))
	   (allocation-env
	    (make-local-movitz-environment env funobj
					   :type 'with-dynamic-extent-allocation-env
					   :scope scope-env)))
      (compiler-call #'compile-implicit-progn
	:form body
	:forward all
	:env allocation-env))))
						       
  
(define-special-operator muerte::compiled-cons
    (&all all &form form &env env &funobj funobj)
  (destructuring-bind (car cdr)
      (cdr form)
    (let ((dynamic-extent-scope (find-dynamic-extent-scope env)))
      (cond
       (dynamic-extent-scope
	(compiler-values ()
	  :returns :eax
	  :functional-p t
	  :type 'cons
	  :code (append (make-compiled-two-forms-into-registers car :eax cdr :ebx funobj env)
			`((:stack-cons ,(make-instance 'movitz-cons)
				       ,dynamic-extent-scope)))))
       (t (compiler-values ()
	    :returns :eax
	    :functional-p t
	    :type 'cons
	    :code (append (make-compiled-two-forms-into-registers car :eax cdr :ebx funobj env)
			  `((:globally (:call (:edi (:edi-offset fast-cons))))))))))))
