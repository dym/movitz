;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      special-operators-cl.lisp
;;;; Description:   Special operators in the COMMON-LISP package.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov 24 16:31:11 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: special-operators-cl.lisp,v 1.30 2004/11/11 10:48:22 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(define-special-operator progn (&all all &form form &top-level-p top-level-p &result-mode result-mode)
  (compiler-call #'compile-implicit-progn
    :form (cdr form)
    :forward all))

(defun expand-to-operator (operator form env)
  "Attempt to compiler-macroexpand FORM to having operator OPERATOR."
  (if (and (listp form) (eq operator (first form)))
      form
    (multiple-value-bind (expansion expanded-p)
	(like-compile-macroexpand-form form env)
      (if expanded-p
	  (expand-to-operator operator expansion env)
	nil))))

(defun parse-let-var-specs (let-var-specs)
  "Given a list of LET variable specifiers (i.e. either VAR or (VAR INIT-FORM)),~
   return a list on the canonical form (VAR INIT-FORM)."
  (loop for var-spec in let-var-specs
      if (symbolp var-spec)
      collect `(,var-spec nil)
      else if (and (listp var-spec)
		   (= 1 (length var-spec)))
      collect `(,(first var-spec) nil)
      else do (assert (and (listp var-spec)
			   (= 2 (length var-spec))))
      and collect var-spec))

(define-special-operator let (&all all &form form &funobj funobj &env env &result-mode result-mode)
  "An extent-nested let is this: (let ((foo ..) (bar (.. (let ((zot ..)) ..)))))
where zot is not in foo's scope, but _is_ in foo's extent."
  (destructuring-bind (operator let-var-specs &body forms)
      form
    (declare (ignore operator))
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body forms)
      (if (and (null let-var-specs)
	       (null declarations))
	  (compiler-call #'compile-implicit-progn
	    :forward all
	    :form body)
	(let* ((recompile-body-p nil)
	       (let-modifies nil)
	       (let-vars (parse-let-var-specs let-var-specs))
	       (local-env (make-local-movitz-environment env funobj
							 :type 'let-env
							 :declarations declarations))
	       (init-env (make-instance 'with-things-on-stack-env
			   :uplink env
			   :funobj funobj
			   :extent-uplink local-env))
	       (binding-var-codes
		(loop for (var init-form) in let-vars
		    if (movitz-env-get var 'special nil local-env)
		       ;; special... see losp/cl/run-time.lisp
		    collect
		      (list var
			    init-form
			    (append (if (= 0 (num-specials local-env)) ; first special? .. binding tail
					`((:locally (:pushl (:edi (:edi-offset dynamic-env)))))
				      `((:pushl :esp)))
				    (prog1 nil (incf (stack-used init-env)))
				    (compiler-call #'compile-form ; binding value
				      :env init-env
				      :defaults all
				      :form init-form
				      :modify-accumulate let-modifies
				      :result-mode :push)
				    `((:globally (:pushl (:edi (:edi-offset unbound-value)))))
				    (prog1 nil (incf (stack-used init-env) 2))
				    (compiler-call #'compile-self-evaluating ; binding name
				      :env init-env
				      :defaults all
				      :form var
				      :result-mode :push)
				    (prog1 nil (incf (stack-used init-env))))
			    nil t)
		    and do (movitz-env-add-binding local-env (make-instance 'dynamic-binding
							       :name var))
		    and do (incf (num-specials local-env))
			;; lexical...
		    else collect
			 (compiler-values-bind (&code init-code	&functional-p functional-p
						&type type &returns init-register
						&final-form final-form)
			     (compiler-call #'compile-form-to-register
			       :env init-env
			       :defaults all
			       :form init-form
			       :modify-accumulate let-modifies)
			   ;; (warn "prod: ~S, type: ~S" prod type)
			   (list var
				 init-form
				 init-code
				 functional-p
				 (let ((init-type (type-specifier-primary type)))
				   (assert init-type ()
				     "The init-form ~S yielded the empty primary type!" type)
				   init-type)
				 (case init-register
				   (:non-local-exit :edi)
				   (t init-register))
				 final-form))
		    and do (movitz-env-add-binding local-env (make-instance 'located-binding
							       :name var)))))
	  (setf (stack-used local-env)
	    (stack-used init-env))
	  (flet ((compile-body ()
		   (if (= 0 (num-specials local-env))
		       (compiler-call #'compile-implicit-progn
			 :defaults all
			 :form body
			 :env local-env)
		     (compiler-call #'compile-form
		       :result-mode (case result-mode
				      (:push :eax)
				      (:function :multiple-values)
				      (t result-mode))
		       :defaults all
		       :form `(muerte.cl:progn ,@body)
		       :modify-accumulate let-modifies
		       :env local-env))))
	    (compiler-values-bind (&all body-values &code body-code &returns body-returns)
		(compile-body)
;;;	      (print-code 'body body-code)
	      (let ((first-binding (movitz-binding (caar binding-var-codes) local-env nil)))
		(cond
		 ;; Is this (let ((#:foo <form>)) (setq bar #:foo)) ?
		 ;; If so, make it into (setq bar <form>)
		 ((and (= 1 (length binding-var-codes))
		       (typep first-binding 'lexical-binding)
		       (instruction-is (first body-code) :load-lexical)
		       (instruction-is (second body-code) :store-lexical)
		       (null (cddr body-code))
		       (eq first-binding ; same binding?
			   (second (first body-code)))
		       (eq (third (first body-code)) ; same register?
			   (third (second body-code))))
		  (let ((dest-binding (second (second body-code))))
		    (check-type dest-binding lexical-binding)
		    (compiler-call #'compile-form
		      :forward all
		      :result-mode dest-binding
		      :form (second (first binding-var-codes)))))
		 #+ignore
		 ((and (= 1 (length binding-var-codes))
		       (typep (movitz-binding (caar binding-var-codes) local-env nil)
			      'lexical-binding)
		       (member (movitz-binding (caar binding-var-codes) local-env nil)
			       (find-read-bindings (first body-code)))
		       (not (code-uses-binding-p (rest body-code) (second (first body-code))
						 :load t :store nil)))
		  (let ((tmp-binding (second (first body-code))))
		    (print-code 'body body-code)
		    (break "Yuhu: tmp ~S" tmp-binding)
		    
		    ))
		 (t (let ((code (append
				 (loop
				     for ((var init-form init-code functional-p type init-register
					       final-form)
					  . rest-codes)
				     on binding-var-codes
				     as binding = (movitz-binding var local-env nil)
						  ;;  for bb in binding-var-codes
						  ;; do (warn "bind: ~S" bb)
				     do (assert type)
					(assert (not (binding-lended-p binding)))
				     appending
				       (cond
					((and (typep binding 'located-binding)
					      (not (binding-lended-p binding))
;;;					      (= 1 (length init-code))
;;;					      (eq :load-lexical (first (first init-code)))
					      (typep final-form 'lexical-binding)
					      (let ((target-binding final-form))
						(and (typep target-binding 'lexical-binding)
						     (eq (binding-funobj binding)
							 (binding-funobj target-binding))
						     (or (and (not (code-uses-binding-p body-code
											binding
											:load nil
											:store t))
							      (not (code-uses-binding-p body-code
											target-binding
											:load nil
											:store t)))
							 ;; This is the best we can do now to determine
							 ;; if target-binding is ever used again.
							 (and (eq result-mode :function)
							      (not (code-uses-binding-p body-code
											target-binding
											:load t
											:store t))
							      (notany (lambda (code)
									(code-uses-binding-p (third code)
											     target-binding
											     :load t
											     :store t))
								      rest-codes))))))
					 ;; replace read-only binding with the outer binding
					 #+ignore (warn "replace ~S in ~S with outer ~S"
							binding (binding-funobj binding)
							(second (first init-code)))
					 (let ((target (second (first init-code))))
					   (change-class binding 'forwarding-binding 
							 :target-binding target)
					   `((:init-lexvar ,binding
							   :init-with-register ,target
							   :init-with-type ,target))))
					((and (typep binding 'located-binding)
					      (type-specifier-singleton type)
					      (not (code-uses-binding-p body-code binding
									:load nil :store t)))
					 ;; replace read-only lexical binding with
					 ;; side-effect-free form
					 #+ignore (warn "Constant binding: ~S => ~S => ~S"
							(binding-name binding)
							init-form
							(car (type-specifier-singleton type)))
					 (when (code-uses-binding-p body-code binding :load t)
					   (setf recompile-body-p t))
					 (change-class binding 'constant-object-binding
						       :object (car (type-specifier-singleton type)))
					 (if functional-p
					     nil ; only inject code if it's got side-effects.
					   (compiler-call #'compile-form-unprotected
					     :env init-env
					     :defaults all
					     :form init-form
					     :result-mode :ignore
					     :modify-accumulate let-modifies)))
					((typep binding 'lexical-binding)
					 (let ((init (type-specifier-singleton
						      (type-specifier-primary type))))
					   (cond
					    ((and init (eq *movitz-nil* (car init)))
					     (append (if functional-p
							 nil
						       (compiler-call #'compile-form-unprotected
							 :env init-env
							 :defaults all
							 :form init-form
							 :result-mode :ignore
							 :modify-accumulate let-modifies))
						     `((:init-lexvar ,binding
								     :init-with-register :edi
								     :init-with-type null))))
					    ((and (typep final-form 'lexical-binding)
						  (eq (binding-funobj final-form)
						      funobj))
					     (append (if functional-p
							 nil
						       (compiler-call #'compile-form-unprotected
							 :env init-env
							 :defaults all
							 :form init-form
							 :result-mode :ignore
							 :modify-accumulate let-modifies))
						     `((:init-lexvar ,binding
								     :init-with-register ,final-form
								     ;; :init-with-type ,final-form
								     ))))
					    (t (append init-code
						       `((:init-lexvar
							  ,binding
							  :init-with-register ,init-register
							  :init-with-type ,(type-specifier-primary type))))))))
					(t init-code)))
				 (when (plusp (num-specials local-env))
				   `((:locally (:call (:edi ,(bt:slot-offset 'movitz-run-time-context
									     'dynamic-variable-install))))
				     (:locally (:movl :esp (:edi (:edi-offset dynamic-env))))))
				 (if (not recompile-body-p)
				     body-code
				   (progn #+ignore (warn "recompile..") ; XXX
					  (compile-body)))
				 (when (plusp (num-specials local-env))
				   `((:movl (:esp ,(+ -4 (* 16 (num-specials local-env)))) :edx)
				     (:locally (:call (:edi ,(bt:slot-offset 'movitz-run-time-context
									     'dynamic-variable-uninstall))))
				     (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
				     (:leal (:esp ,(* 16 (num-specials local-env))) :esp))))))
		      (compiler-values (body-values)
			:returns body-returns
			:producer (default-compiler-values-producer)
			:modifies let-modifies
			:code code))))))))))))

(define-special-operator symbol-macrolet (&all forward &form form &env env &funobj funobj)
  (destructuring-bind (symbol-expansions &body declarations-and-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let ((local-env (make-local-movitz-environment
			env funobj
			:type 'operator-env
			:declarations declarations)))
	(loop for symbol-expansion in symbol-expansions
	    do (destructuring-bind (symbol expansion)
		   symbol-expansion
		 (movitz-env-add-binding local-env (make-instance 'symbol-macro-binding
						  :name symbol
						  :expander #'(lambda (form env)
								(declare (ignore form env))
								expansion)))))
	(compiler-values-bind (&all body-values &code body-code)
	    (compiler-call #'compile-implicit-progn
	      :defaults forward
	      :form body
	      :env local-env
	      :top-level-p (forward :top-level-p))
	  (compiler-values (body-values)
	    :code body-code))))))

(define-special-operator macrolet (&all forward &form form &funobj funobj &env env)
  (destructuring-bind (macrolet-specs &body declarations-and-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let ((local-env (make-local-movitz-environment env funobj
						      :type 'operator-env
						      :declarations declarations)))
	(loop for (name local-lambda-list . local-body-decl-doc) in macrolet-specs
	    as cl-local-lambda-list = (translate-program local-lambda-list :muerte.cl :cl)
	    as (local-body local-declarations) =
	      (multiple-value-list (parse-docstring-declarations-and-body local-body-decl-doc))
	    as cl-local-body = (translate-program local-body :muerte.cl :cl)
	    as cl-local-declarations = (translate-program local-declarations :muerte.cl :cl)
	    as expander = `(lambda (form env)
			     (declare (ignorable env))
			     (destructuring-bind ,cl-local-lambda-list
				 (translate-program (rest form) :muerte.cl :cl)
			       (declare ,@cl-local-declarations)
			       (translate-program (block ,name (let () ,@cl-local-body))
						  :cl :muerte.cl)))
	    do (movitz-env-add-binding
		local-env
		(make-instance 'macro-binding
		  :name name
		  :expander (movitz-macro-expander-make-function expander
								 :name name
								 :type :macrolet))))
	(compiler-values-bind (&all body-values &code body-code)
	    (compiler-call #'compile-implicit-progn
	      :defaults forward
	      :form body
	      :env local-env
	      :top-level-p (forward :top-level-p))
	  (compiler-values (body-values)
	    :code body-code))))))

(define-special-operator multiple-value-prog1 (&all all &form form &result-mode result-mode &env env)
  (destructuring-bind (first-form &rest rest-forms)
      (cdr form)
    (compiler-values-bind (&code form1-code &returns form1-returns &type type)
	(compiler-call #'compile-form-unprotected
	  :defaults all
	  :result-mode (case (result-mode-type result-mode)
			 ((:boolean-branch-on-true :boolean-branch-on-false)
			  :eax)
			 (t result-mode))
	  :form first-form)
      (compiler-call #'special-operator-with-cloak
	;; :with-stack-used t
	:forward all
	:form `(muerte::with-cloak (,form1-returns ,form1-code t ,type)
		 ,@rest-forms)))))
  
(define-special-operator multiple-value-call (&all all &form form &funobj funobj)
  (destructuring-bind (function-form &rest subforms)
      (cdr form)
    (let* ((local-env (make-instance 'let-env
			:uplink (all :env)
			:funobj funobj
			:stack-used t))
	   (numargs-binding (movitz-env-add-binding local-env
						 (make-instance 'located-binding
						   :name (gensym "m-v-numargs-"))))
	   (arg-code (loop for subform in subforms
			 collecting
			   (compiler-values-bind (&code subform-code &returns subform-returns)
			       (compiler-call #'compile-form-unprotected
				 :defaults all
				 :env local-env
				 :form subform
				 :result-mode :multiple-values)
			     (case subform-returns
			       (:multiple-values
				`(:multiple
				  ,@subform-code
				  ,@(make-compiled-push-current-values)
				  (:load-lexical ,numargs-binding :eax)
				  (:addl :ecx :eax)
				  (:store-lexical ,numargs-binding :eax :type fixnum)))
			       (t (list :single ; marker, used below
					subform))))))
	   (number-of-multiple-value-subforms (count :multiple arg-code :key #'car))
	   (number-of-single-value-subforms (count :single arg-code :key #'car)))
      (cond
       ((= 0 number-of-multiple-value-subforms)
	(compiler-call #'compile-form
	  :forward all
	  :form `(muerte.cl::funcall ,function-form ,@subforms)))
       (t (compiler-values ()
	    :returns :multiple-values
	    :code (append `((:load-constant ,(1+ number-of-single-value-subforms) :eax)
			    (:store-lexical ,numargs-binding :eax :type fixnum))
			  (compiler-call #'compile-form
			    :defaults all
			    :env local-env
			    :form function-form
			    :result-mode :push)
			  (loop for ac in arg-code
			      append (ecase (car ac)
				       (:single
					(compiler-call #'compile-form
					  :defaults all
					  :env local-env
					  :form (second ac)
					  :result-mode :push))
				       (:multiple
					(cdr ac))))
			  `((:load-lexical ,numargs-binding :ecx)
			    ;; (:store-lexical ,numargs-binding :ecx :type t)
			    (:movl (:esp (:ecx 1) -4) :eax)
			    (:movl (:esp (:ecx 1) -8) :ebx)
			    (:shrl ,+movitz-fixnum-shift+ :ecx)
			    (:load-constant muerte.cl::funcall :edx)
			    (:movl (:edx ,(slot-offset 'movitz-symbol 'function-value))
				   :esi) ; load new funobj from symbol into ESI
			    (:call (:esi ,(slot-offset 'movitz-funobj 'code-vector)))
			    (:load-lexical ,numargs-binding :edx)
			    ;; Use LEA so as not to modify CF
			    (:leal (:esp :edx) :esp)))))))))


			    
(define-special-operator multiple-value-bind (&all forward &form form &env env &funobj funobj
						   &result-mode result-mode)
  (destructuring-bind (variables values-form &body body-and-declarations)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body body-and-declarations)
      (compiler-values-bind (&code values-code &returns values-returns &type values-type)
	  (compiler-call #'compile-form
	    :defaults forward
	    :form values-form
	    :result-mode :multiple-values #+ignore (list :values (length variables)))
;;;	(warn "mv-code: ~W ~W => ~W ~W" values-form (list :values (length variables)) values-returns (last values-code 10))
	(let* ((local-env (make-local-movitz-environment
			   env funobj
			   :type 'let-env
			   :declarations declarations))
	       (lexical-bindings
		(loop for variable in variables
		    as new-binding = (make-instance 'located-binding
				       :name variable)
		    do (check-type variable symbol)
		    collect new-binding
		    do (cond
			((movitz-env-get variable 'special nil env)
			 (let* ((shadowed-variable (gensym (format nil "m-v-bind-shadowed-~A"
								   variable))))
			   (movitz-env-add-binding local-env new-binding shadowed-variable)
			   (push (list variable shadowed-variable)
				 (special-variable-shadows local-env))))
			(t (movitz-env-add-binding local-env new-binding)))))
	       (init-var-code
		(case (first (operands values-returns))
		  
		  (t (append
		      (make-result-and-returns-glue :multiple-values values-returns)
		      (case (length lexical-bindings)
			(0 nil)
			(1 `((:init-lexvar ,(first lexical-bindings)
					   :protect-carry nil
					   :protect-registers '(:eax))
			     (:store-lexical ,(first lexical-bindings) :eax
					     :type ,(type-specifier-primary values-type))))
			(2 (let ((done-label (gensym "m-v-bind-done-")))
			     `((:init-lexvar ,(first lexical-bindings)
					     :protect-carry t
					     :protect-registers (:eax :ebx))
			       (:store-lexical ,(first lexical-bindings) :eax
					       :type ,(type-specifier-primary values-type)
					       :protect-registers (:ebx))
			       (:init-lexvar ,(second lexical-bindings)
					     :protect-carry t
					     :protect-registers (:ebx))
			       (:store-lexical ,(second lexical-bindings) :edi
					       :type null)
			       (:jnc ',done-label)
			       (:cmpl 1 :ecx)
			       (:jbe ',done-label)
			       (:store-lexical ,(second lexical-bindings) :ebx
					       :type ,(type-specifier-nth-value 1 values-type))
			       ,done-label)))
			(t (with-labels (m-v-bind (ecx-ok-label))
			     `((:jc ',ecx-ok-label)
			       ,@(make-immediate-move 1 :ecx) ; CF=0 means arg-count=1
			       ,ecx-ok-label
			       ,@(loop for binding in lexical-bindings as pos upfrom 0
				     as skip-label = (gensym "m-v-bind-skip-")
				     as type = (type-specifier-nth-value pos values-type)
				     append
				       (case pos
					 (0 `((:init-lexvar ,binding
							    :protect-registers (:eax :ebx :ecx))
					      (:store-lexical ,binding :eax :type ,type
							      :protect-registers (:eax :ebx :ecx))))
					 (1 `((:init-lexvar ,binding
							    :protect-registers (:ebx :ecx))
					      (:store-lexical ,binding :edi :type null
							      :protect-registers (:ecx))
					      (:cmpl 1 :ecx)
					      (:jbe ',skip-label)
					      (:store-lexical ,binding :ebx :type ,type
							      :protect-registers (:ecx))
					      ,skip-label))
					 (t (if *compiler-use-cmov-p*
						`((:init-lexvar ,binding :protect-registers '(:ecx))
						  (:movl :edi :eax)
						  (:cmpl ,pos :ecx)
						  (:locally (:cmova (:edi (:edi-offset values
										       ,(* 4 (- pos 2))))
								    :eax))
						  (:store-lexical ,binding :eax :type ,type
								  :protect-registers (:eax)))
					      `((:init-lexvar ,binding :protect-registers '(:ecx))
						(:movl :edi :eax)
						(:cmpl ,pos :ecx)
						(:jbe ',skip-label)
						(:locally (:movl (:edi (:edi-offset values
										    ,(* 4 (- pos 2))))
								 :eax))
						,skip-label
						(:store-lexical ,binding :eax :type ,type
								:protect-registers (:ecx))))))))))))))))
	  (compiler-values-bind (&code body-code &returns body-returns-mode)
	      (compiler-call #'compile-form-unprotected
		:defaults forward
		:form `(muerte.cl:let ,(special-variable-shadows local-env) ,@body)
		:env local-env)
	    (compiler-values ()
	      :returns body-returns-mode
	      :code (append values-code
			    init-var-code
			    body-code))))))))
				   
(define-special-operator setq (&all forward &form form &env env &funobj funobj &result-mode result-mode)
  (let ((pairs (cdr form)))
    (unless (evenp (length pairs))
      (error "Odd list of SETQ pairs: ~S" pairs))
    (let* ((last-returns :nothing)
	   (bindings ())
	   (code (loop
		     for (var value-form) on pairs by #'cddr
		     as binding = (movitz-binding var env)
		     as pos downfrom (- (length pairs) 2) by 2
		     as sub-result-mode = (if (zerop pos) result-mode :ignore)
		     do (pushnew binding bindings)
		     append
		       (typecase binding
			 (symbol-macro-binding
			  (compiler-values-bind (&code code &returns returns)
			      (compiler-call #'compile-form-unprotected 
				:defaults forward
				:result-mode sub-result-mode
				:form `(muerte.cl:setf ,var ,value-form))
			    (setf last-returns returns)
			    code))
			 (lexical-binding
			  (case (operator sub-result-mode)
			    (t ;; :ignore
			     ;; (setf last-returns :nothing)
			     (compiler-values-bind (&code sub-code &returns sub-returns)
				 (compiler-call #'compile-form
				   :defaults forward
				   :form value-form
				   :result-mode binding)
			       (setf last-returns sub-returns)
			       ;; (warn "sub-returns: ~S" sub-returns)
			       sub-code))
			    #+ignore
			    (t (let ((register (accept-register-mode sub-result-mode)))
				 (compiler-values-bind (&code code &type type)
				     (compiler-call #'compile-form
				       :defaults forward
				       :form value-form
				       :result-mode register)
				   (setf last-returns register)
				   (append code
					   `((:store-lexical ,binding ,register
							     :type ,(type-specifier-primary type)))))))))
			 (t (unless (movitz-env-get var 'special nil env)
			      (warn "Assuming destination variable ~S with binding ~S is special."
				    var binding))
			    (setf last-returns :ebx)
			    (append (compiler-call #'compile-form
				      :defaults forward
				      :form value-form
				      :result-mode :ebx)
				    `((:load-constant ,var :eax)
				      (:globally (:call (:edi (:edi-offset dynamic-store)))))))))))
      (compiler-values ()
	:code code
	:returns last-returns
	:functional-p nil))))
		  
(define-special-operator tagbody
    (&all forward &funobj funobj &form form &env env)
  (let* ((save-esp-variable (gensym "tagbody-save-esp"))
	 (lexical-catch-tag-variable (gensym "tagbody-lexical-catch-tag-"))
	 (label-set-name (gensym "label-set-"))
	 (tagbody-env (make-instance 'tagbody-env
			:label-set-name label-set-name
			:uplink env
			:funobj funobj
			:save-esp-variable save-esp-variable
			:lexical-catch-tag-variable lexical-catch-tag-variable
			:exit-result-mode :ignore))
	 (save-esp-binding (make-instance 'located-binding
			     :name save-esp-variable))
	 (lexical-catch-tag-binding (make-instance 'located-binding
				      :name lexical-catch-tag-variable)))
    (movitz-env-add-binding tagbody-env save-esp-binding)
    (movitz-env-add-binding tagbody-env lexical-catch-tag-binding)
    (movitz-env-load-declarations `((muerte.cl::ignorable ,save-esp-variable ,lexical-catch-tag-variable))
			       tagbody-env nil)
    ;; First generate an assembly-level label for each tag.
    (let* ((label-set (loop with label-id = 0
			  for tag-or-statement in (cdr form)
			  as label = (when (or (symbolp tag-or-statement)
					       (integerp tag-or-statement))
				       (gensym (format nil "go-tag-~A-" tag-or-statement)))
			  when label
			  do (setf (movitz-env-get tag-or-statement 'go-tag nil tagbody-env)
			       label)
			     (setf (movitz-env-get tag-or-statement 'go-tag-label-id nil tagbody-env)
			       (post-incf label-id))
			  and collect label))
	   (tagbody-codes
	    (loop for tag-or-statement in (cdr form)
		if (or (symbolp tag-or-statement) ; Tagbody tags are "compiled" into..
		       (integerp tag-or-statement)) ; ..their assembly-level labels.
		collect (movitz-env-get tag-or-statement 'go-tag nil tagbody-env)
		else collect
		     (compiler-call #'compile-form
		       :defaults forward
		       :form tag-or-statement
		       :env tagbody-env
		       :result-mode :ignore))))
      (let* ((unlexical-target-p (some (lambda (code)
					 (when (listp code)
					   (code-uses-binding-p code save-esp-binding)))
				       tagbody-codes))
	     (maybe-store-esp-code
	      (when (or unlexical-target-p
			(some (lambda (code)
				(when (listp code)
				  (operators-present-in-code-p code '(:lexical-control-transfer) nil
							       :test (lambda (x)
								       (eq tagbody-env (fifth x))))))
			      tagbody-codes))
		`((:init-lexvar ,save-esp-binding
				:init-with-register :esp
				:init-with-type t)))))
	(if (not unlexical-target-p)
	    (compiler-values ()
	      :code (append maybe-store-esp-code
			    (loop for code in tagbody-codes
				if (listp code)
				append code
				else append (list code)))
	      :returns :nothing)
	  (let ((code (append `((:declare-label-set ,label-set-name ,label-set)
				;; catcher
				(:locally (:pushl (:edi (:edi-offset dynamic-env))))
				(:pushl ',label-set-name)
				(:pushl :eax)
				(:pushl :ebp)
				(:locally (:movl :esp (:edi (:edi-offset dynamic-env)))))
			      maybe-store-esp-code
			      (loop for code in tagbody-codes
				  if (listp code)
				  append code
				  else append (list code '(:movl (:esp) :ebp)))
			      `((:movl (:esp 12) :edx)
				(:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
				(:leal (:esp 16) :esp))
			      )))
	    (setf (num-specials tagbody-env) 1
		  (stack-used tagbody-env) 4)
	    (compiler-values ()
	      :code code
	      :returns :nothing)))))))
			
				
(define-special-operator go (&all all &form form &env env &funobj funobj)
  (destructuring-bind (operator tag)
      form
    (declare (ignore operator))
    (multiple-value-bind (label tagbody-env)
	(movitz-env-get tag 'go-tag nil env)
      (assert (and label tagbody-env) ()
	"Go-tag ~W is not visible." tag)
      (if (and (eq funobj (movitz-environment-funobj tagbody-env))
	       ;; any unwind-protects between here and there?
	       (null (nth-value 2 (stack-delta env tagbody-env))))
	  (compiler-values ()
	    :returns :non-local-exit
	    :code `((:lexical-control-transfer nil :nothing ,env ,tagbody-env ,label)))
	;; Perform a lexical "throw" to the tag. Just like a regular (dynamic) throw.
	(let ((save-esp-binding (movitz-binding (save-esp-variable tagbody-env) env))
	      (label-id (movitz-env-get tag 'go-tag-label-id nil tagbody-env nil)))
	  (assert label-id)
	  (compiler-values ()
	    :returns :non-local-exit
	    :code `((:load-lexical ,save-esp-binding :edx)
		    (:movl :edx :eax)
		    ,@(when (plusp label-id)
			;; The target jumper points to the tagbody's label-set.
			;; Now, install correct jumper within tagbody as target.
			`((:addl ,(* 4 label-id) (:edx 8))))
		    (:globally (:call (:edi (:edi-offset dynamic-unwind-next))))
		    ;; have next-continuation in EAX, final-continuation in EDX
		    (:locally (:movl :edx (:edi (:edi-offset raw-scratch0)))) ; final continuation
		    (:locally (:movl :esi (:edi (:edi-offset scratch1))))
		    (:locally (:movl :eax (:edi (:edi-offset dynamic-env)))) ; exit to next-env
		    (:movl :eax :esp)	; enter non-local jump stack mode.
		    (:movl (:esp) :eax)	; target stack-frame EBP
		    (:movl (:eax -4) :esi) ; get target funobj into ESI
		    (:movl (:esp 8) :eax) ; target jumper number
		    (:clc)
		    (:jmp (:esi :eax ,(slot-offset 'movitz-funobj 'constant0))))))))))

(define-special-operator block (&all forward &funobj funobj &form form &env env
				     &result-mode result-mode)
  (destructuring-bind (block-name &body body)
      (cdr form)
    (let* ((exit-block-label (gensym (format nil "exit-block-~A-" block-name)))
	   (save-esp-variable (gensym (format nil "block-~A-save-esp-" block-name)))
	   (lexical-catch-tag-variable (gensym (format nil "block-~A-lexical-catch-tag-" block-name)))
	   (block-result-mode (case result-mode
				((:eax :eax :multiple-values :function :ebx :ecx :ignore)
				 result-mode)
				(t :eax)))
	   (block-returns-mode (case block-result-mode
				 (:function :multiple-values)
				 (:ignore :nothing)
				 (t block-result-mode)))
	   (block-env (make-instance 'lexical-exit-point-env
			:uplink env
			:funobj funobj
			:save-esp-variable save-esp-variable
			:lexical-catch-tag-variable lexical-catch-tag-variable
			:exit-label exit-block-label
			:exit-result-mode block-result-mode))
	   (save-esp-binding (make-instance 'located-binding
			       :name save-esp-variable))
	   (lexical-catch-tag-binding (make-instance 'located-binding
					:name lexical-catch-tag-variable)))
      (movitz-env-add-binding block-env save-esp-binding)
      (movitz-env-add-binding block-env lexical-catch-tag-binding)
      (movitz-env-load-declarations `((muerte.cl::ignorable ,save-esp-variable ,lexical-catch-tag-variable))
				 block-env nil)
      (setf (movitz-env-get block-name :block-name nil block-env)
	block-env)
      (compiler-values-bind (&code block-code &functional-p block-no-side-effects-p)
	  (compiler-call #'compile-form
	    :defaults forward
	    :result-mode block-result-mode
	    :form `(muerte.cl:progn ,@body)
	    :env block-env)
	(let ((maybe-store-esp-code
	       (when (and (not (eq block-result-mode :function))
			  (operators-present-in-code-p block-code '(:lexical-control-transfer) nil
						       :test (lambda (x) (eq block-env (fifth x)))))
		 `((:init-lexvar ,save-esp-binding
				 :init-with-register :esp
				 :init-with-type t)))))
	  (if (not (code-uses-binding-p block-code lexical-catch-tag-binding))
	      (compiler-values ()
		:code (append maybe-store-esp-code
			      block-code
			      (list exit-block-label))
		:returns block-returns-mode
		:functional-p block-no-side-effects-p)
	    (multiple-value-bind (new-code new-returns)
		(make-result-and-returns-glue :multiple-values block-returns-mode block-code)
	      (multiple-value-bind (stack-used wrapped-code)
		  (make-compiled-catch-wrapper lexical-catch-tag-variable
					       funobj block-env new-returns
					       new-code)
		(incf (stack-used block-env) stack-used)
		(setf (num-specials block-env) 1) ; block-env now has one dynamic slot
		(compiler-values ()
		  :code (append maybe-store-esp-code
				`((:movl :esp :eax)
				  (:addl :eax :eax)
				  (:xorl ,(ash (movitz-symbol-hash-key (movitz-read block-name)) 16) :eax)
				  (:init-lexvar ,lexical-catch-tag-binding
						:init-with-register :eax
						:init-with-type t))
				wrapped-code
				(list exit-block-label))
		  :returns block-returns-mode
		  :functional-p block-no-side-effects-p)))))))))


(define-special-operator return-from (&all all &form form &env env &funobj funobj)
  (destructuring-bind (block-name &optional result-form)
      (cdr form)
    (let ((block-env (movitz-env-get block-name :block-name nil env)))
      (assert block-env (block-name)
	"Block-name not found for return-from: ~S." block-name)
      (cond
       ((eq funobj (movitz-environment-funobj block-env))
	(compiler-values-bind (&code return-code &returns return-mode)
	    (compiler-call #'compile-form
	      :forward all
	      :form result-form
	      :result-mode (exit-result-mode block-env))
	  (compiler-values ()
	    :returns :non-local-exit
	    :code (append return-code
			  `((:lexical-control-transfer nil ,return-mode ,env ,block-env))))))
       ((not (eq funobj (movitz-environment-funobj block-env)))
	(compiler-call #'compile-form-unprotected
	  :forward all
	  :form `(muerte.cl:throw
		     ,(movitz-env-lexical-catch-tag-variable block-env)
		   ,result-form)))))))

(define-special-operator require (&form form)
  (let ((*require-dependency-chain*
	 (and (boundp '*require-dependency-chain*)
	      (symbol-value '*require-dependency-chain*))))
    (declare (special *require-dependency-chain*))
    (destructuring-bind (module-name &optional path-spec)
	(cdr form)
      (declare (ignore path-spec))
      (push module-name *require-dependency-chain*)
      (unless (member module-name (image-movitz-modules *image*))
	(when (member module-name (cdr *require-dependency-chain*))
	  (error "Circular Movitz module dependency chain: ~S"
		 (reverse (subseq *require-dependency-chain* 0
				  (1+ (position  module-name *require-dependency-chain* :start 1))))))
	(let* ((require-path (movitz-module-path form)))
	  (movitz-compile-file-internal require-path)
	  (unless (member module-name (image-movitz-modules *image*))
	    (error "Compiling file ~S didn't provide module ~S."
		   require-path module-name))))))
  (compiler-values ()))

(define-special-operator provide (&form form &funobj funobj &top-level-p top-level-p)
  (unless top-level-p
    (warn "Provide form not at top-level."))
  (destructuring-bind (module-name &key load-priority)
      (cdr form)
    (declare (special *default-load-priority*))
    (pushnew module-name (image-movitz-modules *image*))
    (when load-priority
      (setf *default-load-priority* load-priority))
    (let ((new-priority *default-load-priority*))
      (let ((old-tf (member module-name (image-load-time-funobjs *image*) :key #'second)))
	(cond
	 ((and new-priority old-tf)
	  (setf (car old-tf) (list funobj module-name new-priority)))
	 ((and new-priority (not old-tf))
	  (push (list funobj module-name new-priority)
		(image-load-time-funobjs *image*)))
	 (old-tf
	  (setf (car old-tf) (list funobj module-name (third (car old-tf)))))
	 (t (warn "No existing or provided load-time priority for module ~S, will not be loaded!"
		  module-name))))))
  (compiler-values ()))

(define-special-operator eval-when (&all forward &form form &top-level-p top-level-p)
  (destructuring-bind (situations &body body)
      (cdr form)
    (multiple-value-prog1
	(if (or (member :execute situations)
		(and (member :load-toplevel situations)
		     top-level-p))
	    (compiler-call #'compile-implicit-progn
	      :defaults forward
	      :top-level-p top-level-p
	      :form body)
	  (compiler-values ()))
      (when (member :compile-toplevel situations)
	(with-compilation-unit ()
	  (dolist (toplevel-form (translate-program body :muerte.cl :cl
						    :when :eval
						    :remove-double-quotes-p t))
	    (with-host-environment ()
	      (if *compiler-compile-eval-whens*
		  (funcall (compile () `(lambda () ,toplevel-form)))
		(eval toplevel-form)))))))))

(define-special-operator function (&funobj funobj &form form &result-mode result-mode &env env)
  (destructuring-bind (name)
      (cdr form)
    (flet ((function-of-symbol (name)
	     "Look up name in the local function namespace."
	     (let ((movitz-name (movitz-read name))
		   (register (case result-mode
			       ((:ebx :ecx :edx) result-mode)
			       (t :eax))))
	       (compiler-values ()
		 :code `((:load-constant ,movitz-name ,register)
			 (:movl (,register ,(bt:slot-offset 'movitz-symbol 'function-value))
				,register)
			 (:globally (:cmpl (:edi (:edi-offset unbound-function))
					   ,register))
			 (:je '(:sub-program ()
				(:load-constant ,movitz-name :edx)
				(:int 98))))
		 :modifies nil
		 :functional-p t
		 :type 'function
		 :returns register))))
      (etypecase name
	(null (error "Can't compile (function nil)."))
	(symbol
	 (multiple-value-bind (binding)
	     (movitz-operator-binding name env)
	   (etypecase binding
	     (null			; not lexically bound..
	      (function-of-symbol name))
	     (function-binding
	      (compiler-values ()
		:code (make-compiled-lexical-load binding result-mode)
		:type 'function
		:returns result-mode
		:functional-p t))
	     #+ignore
	     (funobj-binding
	      (let ((flet-funobj (funobj-binding-funobj binding)))
		(assert (null (movitz-funobj-borrowed-bindings flet-funobj)))
		(compiler-call #'compile-self-evaluating ; <name> is lexically fbound..
		  :env env
		  :funobj funobj
		  :result-mode result-mode
		  :form flet-funobj)))
	     #+ignore
	     ((or closure-binding borrowed-binding)
	      (compiler-values ()
		:code (make-compiled-lexical-load binding binding-env result-mode)
		:type 'function
		:returns result-mode
		:functional-p t)))))
	((cons (eql muerte.cl:setf))
	 (function-of-symbol (movitz-env-setf-operator-name
			      (muerte::translate-program (second name)
								:cl :muerte.cl))))
	((cons (eql muerte.cl:lambda))
	 (multiple-value-bind (lambda-forms lambda-declarations)
	     (parse-docstring-declarations-and-body (cddr name))
	   (let ((lambda-funobj
		  (make-compiled-funobj-pass1 '(:anonymous-lambda)
					      (cadr name)
					      lambda-declarations
					      `(muerte.cl:progn ,@lambda-forms)
					      env nil)))
	     (let ((lambda-binding (make-instance 'lambda-binding
				     :name (gensym "anonymous-lambda-")
				     :parent-funobj funobj
				     :funobj lambda-funobj)))
	       (movitz-env-add-binding (find-function-env env funobj) lambda-binding)
	       (let ((lambda-result-mode (accept-register-mode result-mode)))
		 (compiler-values ()
		   :type 'function
		   :functional-p t
		   :returns lambda-result-mode
		   :modifies nil
		   :code `((:load-lambda ,lambda-binding ,lambda-result-mode)))))
	     #+old-compiler
	     (cond
	      ((movitz-funobj-borrowed-bindings closure-funobj)
	       (compiler-values ()
		 :type 'function
		 :functional-p nil
		 :returns :edx
		 :modifies (movitz-funobj-borrowed-bindings closure-funobj)
		 :code (append
			(compiler-call #'compile-form
			  :env env
			  :funobj funobj
			  :result-mode :edx
			  :form `(muerte::copy-funobj ,closure-funobj))
			(loop for borrowing-binding in (movitz-funobj-borrowed-bindings closure-funobj)
			    as lended-binding = (borrowed-binding-target borrowing-binding)
			    append
			      `((:lend-lexical ,lended-binding ,borrowing-binding :edx))))))
	      ((null (movitz-funobj-borrowed-bindings closure-funobj))
	       (compiler-call #'compile-self-evaluating
		 :env env
		 :funobj funobj
		 :result-mode result-mode
		 :form closure-funobj))))))))))

(define-special-operator flet (&all forward &form form &env env &funobj funobj)
  (destructuring-bind (flet-specs &body declarations-and-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let* ((flet-env (make-local-movitz-environment env funobj
						   :type 'operator-env
						   :declarations declarations))
	     (init-code
	      (loop for (flet-name flet-lambda-list . flet-dd-body) in flet-specs
		  as flet-binding =
		    (multiple-value-bind (flet-body flet-declarations flet-docstring)
			(parse-docstring-declarations-and-body flet-dd-body)
		      (declare (ignore flet-docstring))
		      (make-instance 'function-binding
			:name flet-name
			:parent-funobj funobj
			:funobj (make-compiled-funobj-pass1 (list 'muerte.cl::flet
								  (movitz-funobj-name funobj)
								  flet-name)
							    flet-lambda-list
							    flet-declarations
							    (list* 'muerte.cl:block
								   (compute-function-block-name flet-name)
								   flet-body)
							    env nil)))
		  do (movitz-env-add-binding flet-env flet-binding)
		  collect `(:local-function-init ,flet-binding))))
	(compiler-values-bind (&all body-values &code body-code)
	    (compiler-call #'compile-implicit-progn
	      :defaults forward
	      :form body
	      :env flet-env)
	  (compiler-values (body-values)
	    :code (append init-code body-code)))))))

(define-special-operator progv (&all all &form form &funobj funobj &env env &result-mode result-mode)
  (destructuring-bind (symbols-form values-form &body body)
      (cdr form)
    (compiler-values-bind (&code body-code &returns body-returns)
	(let ((body-env (make-instance 'with-things-on-stack-env
			  :uplink env
			  :funobj funobj
			  :stack-used t
			  :num-specials t)))
	  ;; amount of stack used and num-specials is not known until run-time.
	  (compiler-call #'compile-implicit-progn
	    :env body-env
	    :result-mode (case result-mode
			   (:push :eax)
			   (:function :multiple-values)
			   (t result-mode))
	    :form body
	    :forward all))
      (compiler-values ()
	:returns (if (eq :push body-returns) :eax body-returns)
	:code (append (make-compiled-two-forms-into-registers symbols-form :ebx
							      values-form :eax
							      funobj env)
		      (with-labels (progv (no-more-symbols no-more-values loop zero-specials))
			`((:xorl :ecx :ecx) ; count number of bindings (fixnum)
			  (:locally (:pushl (:edi (:edi-offset dynamic-env)))) ; first tail
			  (:cmpl :edi :ebx)
			  (:je '(:sub-program (,zero-specials)
				 ;; Insert dummy binding
				 (:pushl :edi) ; biding value
				 (:globally (:pushl (:edi (:edi-offset unbound-value)))) ;  [[ binding tag ]]
				 (:pushl :edi) ; binding name
				 (:pushl :esp)
				 (:addl 4 :ecx)
				 (:jmp ',no-more-symbols)))
			  ,loop
			  (:cmpl :edi :ebx) ; (endp symbols)
			  (:je ',no-more-symbols) ;  .. (go no-more-symbols)
			  (:globally (:movl (:edi (:edi-offset unbound-value)) :edx))
			  (:cmpl :edi :eax) ; (endp values)
			  (:je ',no-more-values) ; .. (go no-more-values)
			  (:movl (:eax -1) :edx)
			  (:movl (:eax 3) :eax) ; (pop values)
			  ,no-more-values
			  (:pushl :edx)	; push (car values) [[ binding value ]]
			  (:globally (:pushl (:edi (:edi-offset unbound-value)))) ;  [[ binding tag ]]
			  (:pushl (:ebx -1)) ; push (car symbols) [[ binding name ]]
			  (:movl (:ebx 3) :ebx) ; (pop symbols)
			  (:addl 4 :ecx)
			  ;; (:jc '(:sub-program (too-many-symbols) (:int 71)))
			  (:pushl :esp)	; push next tail
			  (:jmp ',loop)
			  ,no-more-symbols
			  (:popl :eax)	; remove extra pre-pushed tail
			  (:movl :ecx :edx)
			  (:locally (:call (:edi ,(bt:slot-offset 'movitz-run-time-context
								  'dynamic-variable-install))))
			  (:locally (:movl :esp (:edi (:edi-offset dynamic-env)))) ; install env
			  ;; ecx = N/fixnum
			  ;; (:shll 4 :ecx) ; ecx = 16*N
			  ;; (:leal (:esp :ecx -4) :eax) ; eax = esp + 16*N - 4
			  (:pushl :edx)	; Save number of bindings.
			  #+ignore (:pushl :eax))) ; push address of first binding's tail
		      body-code
		      (when (eq body-returns :push)
			`((:popl :eax))) ; glue :push => :eax
		      `((:movl (:esp) :edx) ; number of bindings
			(:movl (:esp (:edx 4)) :edx) ; previous dynamic-env
			(:locally (:call (:edi ,(bt:slot-offset 'movitz-run-time-context
								'dynamic-variable-uninstall))))
			(:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
			(:popl :edx)	; number of bindings
			(:leal (:esp (:edx 4)) :esp))
		      #+ignore
		      `((:popl :edx)	; pop address of first binding's tail
			(:locally (:popl (:edi (:edi-offset dynamic-env))))))))))

(define-special-operator labels (&all forward &form form &env env &funobj funobj)
  (destructuring-bind (labels-specs &body declarations-and-body)
      (cdr form)
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let* ((labels-env (make-local-movitz-environment env funobj
						     :type 'operator-env
						     :declarations declarations))
	     (labels-bindings
	      (loop for (labels-name) in labels-specs
		  do (check-type labels-name symbol)
		  collecting
		    (movitz-env-add-binding labels-env (make-instance 'function-binding
						      :name labels-name
						      :funobj (make-instance 'movitz-funobj-pass1)
						      :parent-funobj funobj))))
	     (init-code
	      (loop for (labels-name labels-lambda-list . labels-dd-body) in labels-specs
		  as labels-binding in labels-bindings
		  do (multiple-value-bind (labels-body labels-declarations labels-docstring)
			 (parse-docstring-declarations-and-body labels-dd-body)
		       (declare (ignore labels-docstring))
		       (make-compiled-funobj-pass1 (list 'muerte.cl::labels
							 (movitz-funobj-name funobj)
							 labels-name)
						   labels-lambda-list
						   labels-declarations
						   (list* 'muerte.cl:block
							  (compute-function-block-name labels-name)
							  labels-body)
						   labels-env nil
						   :funobj (function-binding-funobj labels-binding)))
		  collect `(:local-function-init ,labels-binding))))
	(compiler-values-bind (&all body-values &code body-code)
	    (compiler-call #'compile-implicit-progn
	      :defaults forward
	      :form body
	      :env labels-env)
	  (compiler-values (body-values)
	    :code (append init-code body-code)))))))

(define-special-operator catch (&all forward &form form &funobj funobj &env env)
  (destructuring-bind (tag &rest forms)
      (cdr form)
    (let ((catch-env (make-instance 'simple-dynamic-env :uplink env :funobj funobj)))
      (compiler-values-bind (&all body-values &code body-code &returns body-returns)
	  (compiler-call #'compile-form
	    :env catch-env
	    :result-mode :multiple-values
	    :defaults forward
	    :form `(muerte.cl:progn ,@forms))
	(multiple-value-bind (stack-used code)
	    (make-compiled-catch-wrapper tag funobj env body-returns body-code)
	  (incf (stack-used catch-env) stack-used)
	  (compiler-values (body-values)
	    :returns body-returns
	    :type '(values &rest t)
	    :code code))))))

(defun make-compiled-catch-wrapper (tag-form funobj env body-returns body-code)
  (assert (member body-returns '(:multiple-values :non-local-exit)))
  (values 4				; stack-used, must be added to body-code's env.
	  (with-labels (catch (label-set exit-point))
	    (append `((:declare-label-set ,label-set (,exit-point))
		      (:locally (:pushl (:edi (:edi-offset dynamic-env)))) ; push dynamic-env
		      (:pushl ',label-set))
		    (compiler-call #'compile-form
		      :env env
		      :with-stack-used 2
		      :funobj funobj
		      :form tag-form
		      :result-mode :push)
		    `((:pushl :ebp)	; push stack frame
		      (:locally (:movl :esp (:edi (:edi-offset dynamic-env))))) ; install catch
		    body-code
		    `(,exit-point
		      (:movl (:esp 12) :edx)
		      (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
		      (:popl :ebp)
		      (:leal (:esp 12) :esp)
		      )))))

(define-special-operator unwind-protect (&all all &form form &env env)
  (destructuring-bind (protected-form &body cleanup-forms)
      (cdr form)
    (let* ((continuation-env (make-instance 'let-env
			       :uplink env
			       :funobj (movitz-environment-funobj env)))
	   (next-continuation-step-binding
	    (movitz-env-add-binding continuation-env
				    (make-instance 'located-binding
				      :name (gensym "up-next-continuation-step-"))))
	   (unwind-protect-env (make-instance 'unwind-protect-env
				 :cleanup-form (cons 'muerte.cl:progn cleanup-forms)
				 :uplink continuation-env
				 :funobj (movitz-environment-funobj env))))
      (with-labels (unwind-protect (cleanup-label cleanup-entry continue continue-label))
	(compiler-values ()
	  :returns :multiple-values
	  :code (append
		 ;; install default continuation dynamic-env..
		 `((:locally (:pushl (:edi (:edi-offset dynamic-env)))) ; uplink
		   (:declare-label-set ,continue-label (,continue))
		   (:pushl ',continue-label)
		   (:locally (:pushl (:edi (:edi-offset unbound-value))))
		   (:pushl :ebp)
		   (:locally (:movl :esp (:edi (:edi-offset dynamic-env)))))
		 ;; install unwind-protect dynamic-env..
		 `((:locally (:pushl (:edi (:edi-offset dynamic-env))))
		   (:declare-label-set ,cleanup-label (,cleanup-entry))
		   (:pushl ',cleanup-label) ; jumper index
		   (:globally (:pushl (:edi (:edi-offset unwind-protect-tag)))) ; tag
		   (:pushl :ebp)	; stack-frame
		   (:locally (:movl :esp (:edi (:edi-offset dynamic-env))))) ; install up-env
		 ;; Execute protected form..
		 (compiler-call #'compile-form
		   :env unwind-protect-env
		   :with-stack-used t
		   :forward all
		   :result-mode :multiple-values
		   :form protected-form)
		 ;; From now on, take care not to touch current-values from protected-form.
		 `((:leal (:esp 16) :edx) ; default final continuation
		   (:locally (:movl :edx (:edi (:edi-offset raw-scratch0))))
		   ,cleanup-entry
		   (:movl (:esp 12) :edx) ; pop out of unwind-protect
		   (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
		   (:popl :ebp)
		   (:leal (:esp 12) :esp)
		   (:locally (:pushl (:edi (:edi-offset raw-scratch0))))) ; push final-continuation
		 ;; Execute cleanup-forms.
		 (compiler-call #'compile-form-unprotected
		   :forward all
		   :env continuation-env
		   :with-stack-used t
		   :result-mode :multiple-values
		   :form `(muerte::with-cloak (:multiple-values)
			    ;; Inside here we don't have to mind current-values.
			    (muerte::with-inline-assembly (:returns :nothing)
			      ;; First, find next-continuation-step..
			      (:locally (:movl (:edi (:edi-offset raw-scratch0)) :eax)) ; final-cont..
			      (:locally (:call (:edi (:edi-offset dynamic-unwind-next))))
			      (:locally (:bound (:edi (:edi-offset stack-bottom)) :eax))
			      (:store-lexical ,next-continuation-step-binding :eax :type t))
			    ,@cleanup-forms))
		 `((:load-lexical ,next-continuation-step-binding :edx)
		   (:locally (:popl (:edi (:edi-offset raw-scratch0)))) ; pop final continuation
		   (:locally (:movl :esi (:edi (:edi-offset scratch1))))
		   (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
		   (:movl :edx :esp)	; enter non-local jump stack mode (possibly).
			  
		   (:movl (:esp) :edx)	; target stack-frame EBP
		   (:movl (:edx -4) :esi) ; get target funobj into EDX
			  
		   (:movl (:esp 8) :edx) ; target jumper number
		   (:jmp (:esi :edx ,(slot-offset 'movitz-funobj 'constant0))))
		 `(,continue
		   (:movl (:esp 12) :edx)
		   (:locally (:movl :edx (:edi (:edi-offset dynamic-env))))
		   (:popl :ebp)
		   (:leal (:esp 12) :esp))))))))


(define-special-operator if (&all all &form form &env env &result-mode result-mode)
  (destructuring-bind (test-form then-form &optional else-form)
      (cdr form)
    (compiler-values-bind (&all then)
	(compiler-call #'compile-form-unprotected
	  :forward all
	  :form then-form)
      (compiler-values-bind (&all else)
	  (compiler-call #'compile-form-unprotected
	    :forward all
	    :form else-form)
	#+ignore (warn "p1: ~S/~S/~S, p2: ~S/~S/~S"
		       (then :producer) (then :final-form) (then :modifies)
		       (else :producer) (else :final-form) (else :modifies))
	(cond
	 ((and (eq result-mode :ignore)
	       (then :functional-p)
	       (else :functional-p))
	  (compiler-call #'compile-form-unprotected
	    :forward all
	    :form test-form))
	 #+ignore
	 ((and (valid-finals (then :final-form) (else :final-form))
	       (equal (then :final-form) (else :final-form)))
	  (warn "if's then and else are equal: ~S both were ~S." form (then :final-form))
	  (compiler-call #'compile-form-unprotected
	    :forward all
	    :form `(muerte.cl:progn ,test-form ,then-form)))
	 ;; ((
	 #+ignore
	 ((and (typep (then :final-form) 'movitz-immediate-object)
	       (typep (else :final-form) 'movitz-immediate-object))
	  (let ((then-value (movitz-immediate-value (then :final-form)))
		(else-value (movitz-immediate-value (else :final-form)))
		(true-label (gensym "if-true-")))
	    (warn "immediate if: ~S vs. ~S"
		  then-value else-value)
	    (compiler-values-bind (&all test)
		(compiler-call #'compile-form
		  :forward all
		  :form test-form
		  :result-mode (cons :boolean-branch-on-true true-label))
	      (compiler-values (test)
		:code (append (test :code)
			      (make-immediate-move then-value :eax)
			      (make-immediate-move else-value :eax)
			      (list true-label))
		:returns :eax))))
	 (t (compiler-call #'compile-form-unprotected
	      :forward all
	      :form `(muerte::compiled-cond (,test-form ,then-form) (t ,else-form)))))))))

(define-special-operator the (&all all &form form)
  (destructuring-bind (value-type sub-form)
      (cdr form)
    (compiler-values-bind (&all sub-form)
	(compiler-call #'compile-form-unprotected
	  :forward all
	  :form sub-form)
      (compiler-values (sub-form)
	:type value-type))))
