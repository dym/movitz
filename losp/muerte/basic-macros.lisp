;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      basic-macros.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: basic-macros.lisp,v 1.7 2004/04/13 16:40:53 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/basic-macros)

;; First of all we must define DEFMACRO..
(muerte::defmacro-compile-time muerte.cl:defmacro (name lambda-list &body macro-body)
  (`(muerte.cl:progn
      (muerte::defmacro-compile-time ,name ,lambda-list ,macro-body)
      ',name)))

(muerte.cl:defmacro muerte.cl:in-package (name)
  `(progn
     (eval-when (:compile-toplevel)
       (in-package ,(movitz::movitzify-package-name name)))))

(in-package muerte)

(defmacro defmacro (name lambda-list &body macro-body)
  `(progn
     (defmacro-compile-time ,name ,lambda-list ,macro-body)
     #+ignore
     (eval-when (:compile-toplevel)
       (let ((name (intern (symbol-name ',name))))
	 (when (eq (symbol-package name)
		   (find-package 'muerte.common-lisp))
	   ;; (warn "setting ~S" name)
	   (setf (movitz:movitz-env-get name 'macro-expansion)
	     (list* 'lambda ',lambda-list
		    ',macro-body)))))
     ',name))

(defmacro defun (function-name lambda-list &body body)
  "Define a function."
;;;  (warn "defun ~S.." function-name)
  (multiple-value-bind (real-body declarations docstring)
      (movitz::parse-docstring-declarations-and-body body 'cl:declare)
    (let ((block-name (compute-function-block-name function-name)))
      `(progn
	 (make-named-function ,function-name ,lambda-list
			      ,declarations ,docstring
			      (block ,block-name ,@real-body))
	 ',function-name))))

(defmacro defun-by-proto (function-name proto-name &rest parameters)
  `(define-prototyped-function ,function-name ,proto-name ,@parameters))

(defmacro define-compiler-macro (name lambda-list &body body)
  `(progn
     (muerte::define-compiler-macro-compile-time ,name ,lambda-list ,body)
     ',name))

(defmacro defpackage (package-name &rest options)
  (pushnew '(:use) options :key #'car)
  (let ((uses (cdr (assoc :use options))))
    (when (or (null uses)
	      (member :muerte.cl uses :test #'string=)
	      (member :muerte.common-lisp uses :test #'string=))
      (push '(:shadowing-import-from :common-lisp nil) options)))
  `(eval-when (:compile-toplevel)
     (defpackage ,package-name ,@options)))

(defmacro cond (&rest clauses)
  (if (null clauses)
      nil
    (destructuring-bind (test-form &rest then-forms)
	(car clauses)
      (if (null then-forms)
	  (let ((cond-test-var (gensym "cond-test-var-")))
	    `(let ((,cond-test-var ,test-form))
	       (if ,cond-test-var
		   ,cond-test-var
		 (cond ,@(rest clauses)))))
	`(if ,test-form
	     (progn ,@then-forms)
	   (cond ,@(rest clauses)))))))

(define-compiler-macro cond (&body cond-body)
  (cons 'compiled-cond cond-body))

(defmacro if (test-form then-form &optional else-form)
  `(cond (,test-form ,then-form) (t ,else-form)))

(define-compiler-macro if (test-form then-form &optional else-form &environment env)
  (when (and (movitz:movitz-constantp then-form env) (movitz:movitz-constantp else-form env))
    (warn "if: ~S // ~S" then-form else-form))
  (if else-form
      `(compiled-cond (,test-form ,then-form) (t ,else-form))
    `(compiled-cond (,test-form ,then-form))))

(defmacro throw (tag result-form)
  `(exact-throw ,tag 0 ,result-form))

(defmacro when (test-form &rest forms)
  `(cond (,test-form ,@forms)))

(defmacro unless (test-form &rest forms)
  `(cond ((not ,test-form) ,@forms)))

(defmacro declaim (&rest declaration-specifiers)
  `(muerte::declaim-compile-time ,@declaration-specifiers))

(defmacro defparameter (name initial-value &optional docstring &environment env)
  (declare (ignore docstring))
  `(progn
     (declaim (special ,name))
     ;; (muerte::compile-time-setq ,name ,initial-value)
     (setq ,name ,initial-value)))

(define-compiler-macro defparameter (&whole form name initial-value
				     &optional docstring &environment env)
  (declare (ignore docstring))
  (if (not (movitz:movitz-constantp initial-value env))
      form
    (let ((mname (translate-program name :cl :muerte.cl)))
      (setf (movitz::movitz-symbol-value (movitz:movitz-read mname))
	(movitz:movitz-eval initial-value env))
      `(declaim (special ,name)))))

(defmacro defvar (name &optional (value nil valuep) documentation)
  (if (not valuep)
      `(declaim (special ,name))
    `(defparameter ,name ,value ,documentation)))

(defmacro define-compile-time-variable (name value)
  `(progn
     (eval-when (:compile-toplevel)
       (defparameter ,name ,value)
       ;; (setf (symbol-value ',name) ,value)
       (pushnew ',name (movitz::image-compile-time-variables movitz::*image*)))
     (defparameter ,name (get-global-property ',name))))

(defmacro let* (var-list &body body)
  (labels ((expand (rest-vars body)
	     (if (null rest-vars)
		 body
	       `((let (,(car rest-vars))
		   ,@(expand (cdr rest-vars) body))))))
    (if (endp var-list)
	`(let () ,@body)
      (car (expand var-list body)))))

(defmacro or (&rest forms)
  (cond
   ((null forms) nil)
   ((null (cdr forms))
    (first forms))
   (t (cons 'cond (maplist (lambda (x)
			     (if (rest x)
				 (list (car x))
			       (list t (car x))))
			   forms)))))

(defmacro and (&rest forms)
  (cond
   ((null forms) t)
   ((null (cdr forms))
    (first forms))
   (t `(when ,(first forms) (and ,@(rest forms))))))

(define-compiler-macro and (&rest forms)
  (case (length forms)
    (0 t)
    (1 (first forms))
    (2 `(compiled-cond (,(first forms) ,(second forms))))
    (t `(compiled-cond ((and ,@(butlast forms))
			,@(last forms))))))

(defmacro psetq (&rest pairs)
  (assert (evenp (length pairs)) (pairs)
    "Uneven arguments to PSETQ: ~S." pairs)
  (case (length pairs)
    (0 nil)
    (2 `(setq ,(first pairs) ,(second pairs)))
    (t (multiple-value-bind (setq-specs let-specs)
	   (loop for (var form) on pairs by #'cddr
	       as temp-var = (gensym)
	       collect (list temp-var form) into let-specs
	       collect var into setq-specs
	       collect temp-var into setq-specs
	       finally (return (values setq-specs let-specs)))
	 `(let ,(butlast let-specs)
	    (setq ,@(last pairs 2) ,@(butlast setq-specs 2)))))))
  
(defmacro return (&optional (result-form nil result-form-p))
  (if result-form-p
      `(return-from nil ,result-form)
    `(return-from nil)))

(define-compiler-macro do (var-specs (end-test-form &rest result-forms) &body declarations-and-body)
  (flet ((var-spec-let-spec (var-spec)
	   (cond
	    ((symbolp var-spec)
	     var-spec)
	    ((cddr var-spec)
	     (subseq var-spec 0 2))
	    (t var-spec)))
	 (var-spec-var (var-spec)
	   (if (symbolp var-spec) var-spec (car var-spec)))
	 (var-spec-step-form (var-spec)
	   (and (listp var-spec)
		(= 3 (list-length var-spec))
		(or (third var-spec)
		    '(quote nil)))))
    (multiple-value-bind (body declarations)
	(movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
      (let* ((loop-tag (gensym "do-loop"))
	     (start-tag (gensym "do-start")))
	`(block nil
	   (let ,(mapcar #'var-spec-let-spec var-specs)
	     (declare ,@declarations (loop-tag ,loop-tag))
	     (tagbody
	       ,(unless (and (movitz:movitz-constantp end-test-form)
			     (not (movitz::movitz-eval end-test-form)))
		  `(go ,start-tag))
	       ,loop-tag
	       ,@body
	       (psetq ,@(loop for var-spec in var-specs
			    as step-form = (var-spec-step-form var-spec)
			    when step-form
			    append (list (var-spec-var var-spec) step-form)))
	       ,start-tag
	       (unless ,end-test-form (go ,loop-tag)))
	     ,@result-forms))))))

(defmacro do* (var-specs (end-test-form &rest result-forms) &body declarations-and-body)
  (flet ((var-spec-let-spec (var-spec)
	   (cond
	    ((symbolp var-spec)
	     var-spec)
	    ((cddr var-spec)
	     (subseq var-spec 0 2))
	    (t var-spec)))
	 (var-spec-var (var-spec)
	   (if (symbolp var-spec) var-spec (car var-spec)))
	 (var-spec-step-form (var-spec)
	   (and (listp var-spec)
		(= 3 (list-length var-spec))
		(or (third var-spec)
		    '(quote nil)))))
    (multiple-value-bind (body declarations)
	(movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
      (let* ((loop-tag (gensym "do*-loop"))
	     (start-tag (gensym "do*-start")))
	`(block nil
	   (let* ,(mapcar #'var-spec-let-spec var-specs)
	     (declare ,@declarations)
	     (tagbody
	       (go ,start-tag)
	       ,loop-tag
	       ,@body
	       (setq ,@(loop for var-spec in var-specs
			   as step-form = (var-spec-step-form var-spec)
			   when step-form
			   append (list (var-spec-var var-spec) step-form)))
	       ,start-tag
	       (unless ,end-test-form (go ,loop-tag)))
	     ,@result-forms))))))

(define-compiler-macro do* (var-specs (end-test-form &rest result-forms) &body declarations-and-body)
  (flet ((var-spec-let-spec (var-spec)
	   (if (symbolp var-spec) var-spec (subseq var-spec 0 2)))
	 (var-spec-var (var-spec)
	   (if (symbolp var-spec) var-spec (car var-spec)))
	 (var-spec-step-form (var-spec)
	   (and (listp var-spec)
		(= 3 (list-length var-spec))
		(or (third var-spec)
		    '(quote nil)))))
    (multiple-value-bind (body declarations)
	(movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
      (let* ((loop-tag (gensym "do*-loop"))
	     (start-tag (gensym "do*-start")))
	`(block nil
	   (let* ,(mapcar #'var-spec-let-spec var-specs)
	     (declare ,@declarations (loop-tag ,loop-tag))
	     (tagbody
	       (go ,start-tag)
	       ,loop-tag
	       ,@body
	       (setq ,@(loop for var-spec in var-specs
			   as step-form = (var-spec-step-form var-spec)
			   when step-form
			   append (list (var-spec-var var-spec) step-form)))
	       ,start-tag
	       (unless ,end-test-form (go ,loop-tag)))
	     ,@result-forms))))))


(defmacro case (keyform &rest clauses)
  (flet ((otherwise-clause-p (x)
	   (member (car x) '(t otherwise))))
    (let ((key-var (make-symbol "case-key-var")))
      `(let ((,key-var ,keyform))
	 (cond
	  ,@(loop for clause-head on clauses
		as clause = (first clause-head)
		as keys =  (first clause)
		as forms = (rest clause)
			   ;; do (warn "clause: ~S, op: ~S" clause (otherwise-clause-p clause))
		if (and (endp (rest clause-head)) (otherwise-clause-p clause))
		collect (cons t forms)
		else if (otherwise-clause-p clause)
		do (error "Case's otherwise clause must be the last clause.")
		else if (atom keys)
		collect `((eql ,key-var ',keys) ,@forms)
		else collect `((or ,@(mapcar #'(lambda (c)
						 `(eql ,key-var ',c))
					     keys))
			       ,@forms)))))))

(define-compiler-macro case (keyform &rest clauses)
  (case (length clauses)
    (0 keyform)
    (1 (let ((clause (first clauses)))
	 (case (car clause)
	   ((nil) keyform)
	   ((t otherwise)
	    `(progn keyform ,@(cdr clause)))
	   (t (if (atom (car clause))
		  `(when (eql ,keyform ',(car clause))
		     ,@(cdr clause))
		`(compiled-case ,keyform ,@clauses))))))
    (t `(compiled-case ,keyform ,@clauses))))

(defmacro ecase (keyform &rest clauses)
  ;; "Not quite implemented.."
  `(case ,keyform ,@clauses (t (error "~S fell through an ecase where the legal cases were ~S"
				      ,keyform
				      ',(mapcar #'first clauses)))))

(defmacro movitz-accessor (object-form type slot-name)
  `(with-inline-assembly (:returns :register :side-effects nil)
     (:compile-form (:result-mode :eax) ,object-form)
     (:movl (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
				   (find-symbol (string slot-name) :movitz)))
	    (:result-register))))

(defmacro setf-movitz-accessor ((object-form type slot-name) value-form)
  `(with-inline-assembly (:returns :eax :side-effects t)
     (:compile-two-forms (:eax :ebx) ,value-form ,object-form)
     (:movl :eax (:ebx ,(bt:slot-offset (find-symbol (string type) :movitz)
					(find-symbol (string slot-name) :movitz))))))

(defmacro movitz-accessor-u16 (object-form type slot-name)
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,object-form)
     (:movzxw (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
				     (find-symbol (string slot-name) :movitz)))
	      :ecx)
     (:leal ((:ecx #.movitz::+movitz-fixnum-factor+) :edi ,(- (movitz::image-nil-word movitz::*image*)))
	    :eax)))

(defmacro set-movitz-accessor-u16 (object-form type slot-name value)
  `(with-inline-assembly (:returns :eax)
     (:compile-two-forms (:eax :ecx) ,object-form ,value)
     (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
     (:movw :cx (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
				       (find-symbol (string slot-name) :movitz))))
     (:leal ((:ecx #.movitz::+movitz-fixnum-factor+) :edi ,(- (movitz::image-nil-word movitz::*image*)))
	    :eax)))


(define-compiler-macro not (x)
  `(muerte::inlined-not ,x))

(define-compiler-macro null (x)
  `(muerte::inlined-not ,x))

(define-compiler-macro eq (&whole form &environment env x y)
  (cond
   ((movitz:movitz-constantp y env)
    (let ((y (movitz::eval-form y env)))
      (cond
       ((movitz:movitz-constantp x env)
	(warn "constant eq!: ~S" form)
	(eq y (movitz::eval-form x env)))
       ((eq y nil)
	`(muerte::inlined-not ,x))
       ((eql y 0)
	`(with-inline-assembly-case (:side-effects nil)
	   (do-case ((:boolean-branch-on-true :boolean-branch-on-false)
		     :boolean-zf=1)
	     (:compile-form (:result-mode :eax) ,x)
	     (:testl :eax :eax))
	   (do-case (t :boolean-cf=1)
	     (:compile-form (:result-mode :eax) ,x)
	     (:cmpl 1 :eax))))
       ((typep y '(or symbol (unsigned-byte 29)))
	`(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	   (:compile-form (:result-mode :eax) ,x)
	   (:load-constant ,y :eax :op :cmpl)))
       (t `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	     (:compile-two-forms (:eax :ebx) ,x ,y)
	     (:cmpl :eax :ebx))))))
   ((and (movitz:movitz-constantp x env)
	 (typep (movitz::eval-form x env)
		'(or symbol (unsigned-byte 30))))
    `(eq ,y ,x))
   (t `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	 (:compile-two-forms (:eax :ebx) ,x ,y)
	 (:cmpl :eax :ebx)))))

(define-compiler-macro eql (&whole form x y)
  `(eq ,x ,y))

(define-compiler-macro values (&rest sub-forms)
  `(inline-values ,@sub-forms))

#+ignore
(define-compiler-macro values (&whole form &rest sub-forms)
  (case (length sub-forms)
    (0 `(with-inline-assembly (:returns :multiple-values :side-effects nil :type (values))
	  (:movl :edi :eax)
	  (:xorl :ecx :ecx)
	  (:stc)))
    (1 `(with-inline-assembly (:returns :eax :side-effects nil :type (values t))
	  (:compile-form (:result-mode :eax) ,(first sub-forms))))
    (2 `(with-inline-assembly (:returns :multiple-values :side-effects nil :type (values t t))
	  (:compile-two-forms (:eax :ebx) ,(first sub-forms) ,(second sub-forms))
	  (:xorl :ecx :ecx)
	  (:movb 2 :cl)
	  (:stc)))
    (t form)))

(defmacro multiple-value-list (form)
  `(multiple-value-call #'list ,form))

(defmacro nth-value (n form)
  `(nth ,n (multiple-value-list ,form)))

(define-compiler-macro nth-value (n form)
  `(compiled-nth-value ,n ,form))

(defmacro prog1 (first-form &rest rest-forms)
  ;; This definition of PROG1 is not as inefficient as it looks.
  ;; The combination of VALUES and M-V-PROG1 will lead to reasonable code.
  `(values (multiple-value-prog1 ,first-form ,@rest-forms)))

(defmacro prog2 (first-form second-form &rest rest-forms)
  `(progn ,first-form (prog1 ,second-form ,@rest-forms)))

(defmacro prog (variable-list &body declarations-and-body)
  (multiple-value-bind (body declarations)
      (movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
    `(block nil (let ,variable-list (declare ,@declarations) (tagbody ,@body)))))

(defmacro prog* (variable-list &body declarations-and-body)
  (multiple-value-bind (body declarations)
      (movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
    `(block nil (let* ,variable-list (declare ,@declarations) (tagbody ,@body)))))

(defmacro multiple-value-setq (vars form)
  (let ((tmp-vars (loop repeat (length vars) collect (gensym))))
    `(multiple-value-bind ,tmp-vars ,form
       (setq ,@(loop for v in vars and tmp in tmp-vars collect v collect tmp)))))

;;;(defmacro declaim (&rest declarations)
;;;  (movitz::movitz-env-load-declarations declarations nil :declaim)
;;;  (values))

(define-compiler-macro defconstant (name initial-value &optional documentation)
  (declare (ignore documentation))
  (check-type name symbol)
  `(progn
     (eval-when (:compile-toplevel)
       (let* ((movitz-name (movitz::translate-program ',name :cl :muerte.cl))
	      (movitz-symbol (movitz::movitz-read movitz-name))
	      (movitz-value (movitz::translate-program (movitz::movitz-eval ',initial-value)
						  :cl :muerte.cl)))
	 (when (and (movitz:movitz-constantp ',name)
		    (not (equalp (movitz::movitz-eval ',name) movitz-value)))
	   (warn "Redefining constant variable ~S from ~S to ~S."
		 ',name
		 (movitz::movitz-eval ',name)
		 movitz-value))
	 (proclaim `(special ,movitz-name))
	 (setf (movitz::movitz-symbol-value movitz-symbol) (movitz::movitz-read movitz-value)
	       (symbol-value movitz-name) movitz-value)))
     (declaim (muerte::constant-variable ,name))))

(defmacro define-symbol-macro (symbol expansion)
  (check-type symbol symbol "a symbol-macro symbol")
  `(progn
     (eval-when (:compile-toplevel)
       (movitz::movitz-env-add-binding nil (make-instance 'movitz::symbol-macro-binding
					:name ',symbol
					:expander (lambda (form env)
						    (declare (ignore form env))
						    (movitz::translate-program ',expansion
									     :cl :muerte.cl)))))
     ',symbol))

  

(defmacro inline-malloc (size &key (tag :other) other-tag wide-other-tag)
  (assert (not (and (not other-tag) wide-other-tag)))
  `(with-inline-assembly (:returns :eax :side-effects t)
     ,@(if (integerp size)
	   `((:movl ,size :ebx))
	 `((:compile-form (:result-mode :ebx) ,size)
	   (:shrl ,movitz::+movitz-fixnum-shift+ :ebx)))
     (:globally (:call (:edi (:edi-offset malloc))))
     (:addl ,(if (integerp tag) tag (movitz::tag tag)) :eax)
     ,@(when (and (eq tag :other) other-tag (not wide-other-tag))
	 `((:movb ,(movitz::tag other-tag) (:eax -2))))
     ,@(when (and (eq tag :other) other-tag wide-other-tag)
	 `((:movw ,(dpb wide-other-tag (byte 8 8) (movitz::tag other-tag)) (:eax -2))))))

(defmacro check-type (place type &optional type-string)
  (declare (ignore type-string))
  `(let ((place-value ,place))
     (unless (typep place-value ',type)
       (error "Place ~A is not of type ~A, its value is {~Z}."
	      ',place ',type place-value))))

(define-compiler-macro check-type (place type &optional type-string &environment env)
  (declare (ignore type-string))
  (cond
   ((movitz:movitz-constantp place env)
    (assert (typep (movitz::eval-form place env) type))
    nil)
   (t (if (member type '(standard-gf-instance  function pointer
			 integer fixnum cons symbol character null list
			 string vector simple-vector vector-u8 vector-u16))
	  `(unless (typep ,place ',type)
	     (with-inline-assembly (:returns :non-local-exit)
	       (:int 66)))
	`(let ((place-value ,place))
	   (unless (typep place-value ',type)
	     (error "Place ~A is not of type ~A, its value is ~Z."
		    ',place ',type place-value)))))))

(defmacro assert (test-form &optional places datum-form &rest argument-forms)
  (declare (ignore places))
  (cond
   (datum-form
    `(progn
       (unless ,test-form
	 (error ,datum-form ,@argument-forms)
	 nil)))
   (t `(progn
	 (unless ,test-form
	   (error "The assertion ~A failed." ',test-form))
	 nil))))

(define-compiler-macro car (x)
  `(let ((cell ,x))
     (with-inline-assembly-case (:side-effects nil)
       (do-case (t :register)
	 (:cons-get :car (:lexical-binding cell) (:result-register))))))

(define-compiler-macro cdr (x)
  `(let ((cell ,x))
     (with-inline-assembly-case (:side-effects nil)
       (do-case (t :register)
	 (:cons-get :cdr (:lexical-binding cell) (:result-register))))))

(define-compiler-macro cadr (x)
  `(car (cdr ,x)))

(define-compiler-macro cddr (x)
  `(cdr (cdr ,x)))

(define-compiler-macro (setf car) (value cell &environment env)
  (if (and (movitz:movitz-constantp value env)
	   (eq nil (movitz::eval-form value env)))
      `(with-inline-assembly (:returns :edi)
	 (:compile-form (:result-mode :eax) ,cell)
	 (:leal (:eax -1) :ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 66)))
	 (:movl :edi (:eax -1)))
    `(with-inline-assembly (:returns :eax)
       (:compile-two-forms (:eax :ebx) ,value ,cell)
       (:leal (:ebx -1) :ecx)
       (:testb 7 :cl)
       (:jnz '(:sub-program () (:int 66)))
       (:movl :eax (:ebx -1)))))

(define-compiler-macro (setf cdr) (value cell &environment env)
  (if (and (movitz:movitz-constantp value env)
	   (eq nil (movitz::eval-form value env)))
      `(with-inline-assembly (:returns :edi)
	 (:compile-form (:result-mode :eax) ,cell)
	 (:leal (:eax -1) :ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 66)))
	 (:movl :edi (:eax 3)))
    `(with-inline-assembly (:returns :eax)
       (:compile-two-forms (:eax :ebx) ,value ,cell)
       (:leal (:ebx -1) :ecx)
       (:testb 7 :cl)
       (:jnz '(:sub-program () (:int 66)))
       (:movl :eax (:ebx 3)))))

(define-compiler-macro rplaca (cons object)
  `(with-inline-assembly (:returns :eax)
     (:compile-two-forms (:eax :ebx) ,cons ,object)
     (:leal (:eax -1) :ecx)
     (:testb 7 :cl)
     (:jnz '(:sub-program () (:int 66)))
     (:movl :ebx (:eax -1))))

(define-compiler-macro rplacd (cons object)
  `(with-inline-assembly (:returns :eax)
     (:compile-two-forms (:eax :ebx) ,cons ,object)
     (:leal (:eax -1) :ecx)
     (:testb 7 :cl)
     (:jnz '(:sub-program () (:int 66)))
     (:movl :ebx (:eax 3))))

(define-compiler-macro endp (x)
  `(let ((cell ,x))
     (with-inline-assembly-case (:side-effects nil)
       (do-case (t :same)
	 (:endp (:lexical-binding cell) (:returns-mode))))))

(define-compiler-macro cons (x y)
  `(with-inline-assembly (:returns :eax :side-effects nil :type cons)
     (:compile-two-forms (:eax :ebx) ,x ,y)
     (:globally (:call (:edi (:edi-offset fast-cons))))))

#+ignore
(define-compiler-macro apply (&whole form function &rest args)
  (if (and nil (consp function) (eq 'function (first function)) (symbolp (second function)))
      `(apply ',(second function) ,@args) ; we prefer 'foo over #'foo.
    form))

(define-compiler-macro funcall (&whole form function &rest arguments)
  (or (and (listp function)
	   (eq 'muerte.cl:function (first function))
	   (let ((fname (second function)))
	     (or (and (symbolp fname)
		      `(,fname ,@arguments))
		 (and (listp fname)
		      (eq 'muerte.cl:setf (first fname))
		      `(,(movitz::movitz-env-setf-operator-name (movitz::translate-program (second fname)
										    :cl :muerte.cl))
			,@arguments)))))
      (case (length arguments)
	(0 `(funcall%0ops ,function))
	(1 `(funcall%1ops ,function ,(first arguments)))
	(2 `(funcall%2ops ,function ,(first arguments) ,(second arguments)))
	(3 `(funcall%3ops ,function ,(first arguments) ,(second arguments) ,(third arguments)))
	(t form))))

(define-compiler-macro funcall%0ops (&whole form function)
  `(with-inline-assembly-case ()
     (do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
       (:compile-form (:result-mode :edx) ,function)
       (:leal (:edx -7) :ecx)
       (:andb 7 :cl)
       (:jnz 'not-symbol)
       (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
       (:jmp 'funobj-ok)
      not-symbol
       (:cmpb 7 :cl)
       (:jne '(:sub-program (not-funobj)
	       (:int 69)))
       (:cmpb ,(movitz::tag :funobj) (:edx -2))
       (:jne 'not-funobj)
       (:movl :edx :esi)
      funobj-ok
       (:xorl :ecx :ecx)
       (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector))))))

(define-compiler-macro compiler-error (&rest args)
  (apply 'error args))

(define-compiler-macro funcall%1ops (&whole form function argument)
  `(compiler-typecase ,function
     ((or nil null)
      (compiler-error "Can't compile funcall of NIL."))
     (function
      (with-inline-assembly-case ()
	(do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	  (:compile-two-forms (:edx :eax) ,function ,argument)
	  (:movl :edx :esi)
	  (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))))
     (symbol
      (with-inline-assembly-case ()
	(do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	  (:compile-two-forms (:edx :eax) ,function ,argument)
	  (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
	  (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))))
     ((or symbol function)
      (with-inline-assembly-case ()
	(do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	  (:compile-two-forms (:edx :eax) ,function ,argument)
	  (:leal (:edx -5) :ecx)
	  (:andl 5 :ecx)
	  (:movl :edx :esi)
	  (:jnz 'funobj-ok)		; not a symbol, so it must be a funobj.
	  (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
	 funobj-ok
	  (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))))
     (t (with-inline-assembly-case ()
	  (do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	    (:compile-two-forms (:edx :eax) ,function ,argument)
	    (:leal (:edx -7) :ecx)
	    (:testb 7 :cl)
	    (:jnz 'not-symbol)
	    (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
	    (:jmp 'funobj-ok)
	   not-symbol
	    (:leal (:edx -6) :ecx)
	    (:testb 7 :cl)
	    (:jne '(:sub-program (not-funobj)
		    (:int 69)))
	    (:cmpb ,(movitz::tag :funobj) (:edx -2))
	    (:jne 'not-funobj)
	    (:movl :edx :esi)
	   funobj-ok
	    (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))))))

(define-compiler-macro funcall%2ops (function arg0 arg1)
  (let ((function-var (gensym)))
    `(let ((,function-var ,function))
       (with-inline-assembly-case ()
	 (do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	   (:compile-two-forms (:eax :ebx) ,arg0 ,arg1)
	   (:compile-form (:result-mode :edx) ,function-var)
	   (:leal (:edx -7) :ecx)
	   (:andb 7 :cl)
	   (:jnz 'not-symbol)
	   (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
	   (:jmp 'funobj-ok)
	  not-symbol
	   (:cmpb 7 :cl)
	   (:jnz '(:sub-program (not-funobj)
		   (:int 69)))
	   (:cmpb ,(movitz::tag :funobj) (:edx -2))
	   (:jne 'not-funobj)
	   (:movl :edx :esi)
	  funobj-ok
	   (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op))))))))

(define-compiler-macro funcall%3ops (function arg0 arg1 arg2)
  (let ((function-var (gensym)))
    `(let ((,function-var ,function))
       (with-inline-assembly-case ()
	 (do-case (t :multiple-values :labels (not-symbol not-funobj funobj-ok))
	   (:compile-arglist () ,arg0 ,arg1 ,arg2)
	   (:compile-form (:result-mode :edx) ,function-var)
	   (:leal (:edx -7) :ecx)
	   (:andb 7 :cl)
	   (:jnz 'not-symbol)
	   (:movl (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)) :esi)
	   (:jmp 'funobj-ok)
	  not-symbol
	   (:cmpb 7 :cl)
	   (:jnz '(:sub-program (not-funobj)
		   (:int 69)))
	   (:cmpb ,(movitz::tag :funobj) (:edx -2))
	   (:jne 'not-funobj)
	   (:movl :edx :esi)
	  funobj-ok
	   (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op))))))))

(define-compiler-macro funcall%unsafe%1ops (function arg0)
  `(with-inline-assembly (:returns :multiple-values)
     (:compile-two-forms (:eax :esi) ,arg0 ,function)
     (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))))

(define-compiler-macro funcall%unsafe%2ops (function arg0 arg1)
  `(with-inline-assembly (:returns :multiple-values)
     (:compile-form (:result-mode :push) ,function)
     (:compile-two-forms (:eax :ebx) ,arg0 ,arg1)
     (:popl :esi)
     (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op)))))

(define-compiler-macro funcall%unsafe%3ops (function arg0 arg1 arg2)
  `(let ((fn ,function))
     (with-inline-assembly (:returns :multiple-values)
       (:compile-arglist () ,arg0 ,arg1 ,arg2)
;;;     (:compile-form (:result-mode :push) ,function)
;;;     (:compile-form (:result-mode :push) ,arg0)
;;;     (:compile-two-forms (:ebx :ecx) ,arg1 ,arg2)
;;;     (:popl :eax)
;;;     (:popl :esi)
;;;     (:pushl :ecx)
       (:compile-form (:result-mode :esi) fn)
       (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op))))))

(define-compiler-macro funcall%unsafe (function &rest args)
  (case (length args)
    (0 `(with-inline-assembly (:returns :multiple-values)
	  (:compile-form (:result-mode :esi) ,function)
	  (:xorl :ecx :ecx)
	  (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))))
    (1 `(funcall%unsafe%1ops ,function ,(first args)))
    (2 `(funcall%unsafe%2ops ,function ,(first args) ,(second args)))
    (3 `(funcall%unsafe%3ops ,function ,(first args) ,(second args) ,(third args)))
    (t `(funcall ,function ,@args))))

(defmacro with-funcallable ((name &optional (function-form name)) &body body)
  (let ((function (gensym "with-function-")))
    `(let ((,function (ensure-funcallable ,function-form)))
       (macrolet ((,name (&rest args) `(funcall%unsafe ,',function ,@args)))
	 ,@body))))

(defmacro lambda (&whole form)
  `(function ,form))

(defmacro backquote (form)
  (typecase form
    (list
     (if (eq 'backquote-comma (car form))
	 (cadr form)
       (cons 'append
	     (loop for sub-form-head on form
		 as sub-form = (and (consp sub-form-head)
				    (car sub-form-head))
		 collecting
		   (cond
		    ((atom sub-form-head)
		     (list 'quote sub-form-head))
		    ((atom sub-form)
		     (list 'quote (list sub-form)))
		    (t (case (car sub-form)
			 (backquote-comma
			  (list 'list (cadr sub-form)))
			 (backquote-comma-at
			  (cadr sub-form))
			 (t (list 'list (list 'backquote sub-form))))))))))
    (array
     (error "Array backquote not implemented."))
    (t (list 'quote form))))

;;;(defmacro defun+movitz (name &rest args)
;;;  (flet ((make-compile-side-name (x)
;;;	   (if (find-symbol (symbol-name x) :common-lisp)
;;;	       (intern (format nil "~A-~A" '#:movitz x))
;;;	     x)))
;;;    (if (symbolp name)
;;;	`(progn
;;;	   (eval-when (:compile-toplevel)
;;;	     (defun ,(make-compile-side-name name) ,@args))
;;;	   (defun ,name ,@args))
;;;      `(progn
;;;	 (eval-when (:compile-toplevel)
;;;	   (defun (,(first name) ,(make-compile-side-name (second name))) ,@(cddr name)
;;;		  ,@args))
;;;	 (defun ,name ,@args)))))


(define-compiler-macro first (x)
  `(car ,x))
(define-compiler-macro second (x)
  `(cadr ,x))
(define-compiler-macro third (x)
  `(caddr ,x))
(define-compiler-macro rest (x)
  `(cdr ,x))

(define-compiler-macro find-class (&whole form &environment env symbol &optional (errorp t))
  (declare (ignore errorp))
  (if (not (movitz:movitz-constantp symbol env))
      form
    (case (movitz::translate-program (movitz::eval-form symbol env) :muerte.cl :cl)
      ((t) `(load-global-constant the-class-t))
      (fixnum '(load-global-constant the-class-fixnum))
      (null `(load-global-constant the-class-null))
      (symbol '(load-global-constant the-class-symbol))
      (cons '(load-global-constant the-class-cons))
      (t form))))

(define-compiler-macro class-of (object)
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,object)
     (:movl :eax :ecx)
     (:andl #x7 :ecx)
     (:call (:edi (:ecx 4) ,(movitz::global-constant-offset 'fast-class-of)))))

(define-compiler-macro without-gc (&body body)
  `(multiple-value-prog1
       (progn (with-inline-assembly (:returns :nothing) (:std))
	      ,@body)
     (with-inline-assembly (:returns :nothing) (:cld))))

;;;

(defmacro std-instance-reader (slot instance-form)
  (let ((slot (intern (symbol-name slot) :movitz)))
    `(with-inline-assembly-case ()
       (do-case (:ecx)
	 (:warn "std-instance-reader ~S for ecx!" ',slot)
	 (:not-implemented))
       (do-case (t :register)
	 (:compile-form (:result-mode :register) ,instance-form)
	 (:leal ((:result-register) ,(- (movitz::tag :other)))
		:ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 68)))
	 (:movl ((:result-register) ,(bt:slot-offset 'movitz::movitz-std-instance slot))
		(:result-register))))))

(defmacro std-instance-writer (slot value instance-form)
  (let ((slot (intern (symbol-name slot) :movitz)))
    `(with-inline-assembly-case ()
       (do-case (t :eax)
	 (:compile-two-forms (:eax :ebx) ,value ,instance-form)
	 (:leal (:ebx ,(- (movitz::tag :other)))
		:ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 68)))
	 (:movl :eax
		(:ebx ,(bt:slot-offset 'movitz::movitz-std-instance slot)))))))

(define-compiler-macro std-instance-class (instance)
  `(std-instance-reader class ,instance))

(define-compiler-macro (setf std-instance-class) (value instance)
  `(std-instance-writer class ,value ,instance))

(define-compiler-macro std-instance-slots (instance)
  `(std-instance-reader slots ,instance))

(define-compiler-macro (setf std-instance-slots) (value instance)
  `(std-instance-writer slots ,value ,instance))

(define-compiler-macro standard-instance-access (instance location)
  `(svref (std-instance-slots ,instance) ,location))

(define-compiler-macro with-stack-check (&body body)
  `(let ((before (with-inline-assembly (:returns :eax)
		   (:movl :esp :ecx)
		   (:leal ((:ecx 2)) :eax))))
     ,@body
     (let ((delta (- before (with-inline-assembly (:returns :eax)
			      (:movl :esp :ecx)
			      (:leal ((:ecx 2)) :eax)))))
       (warn "stack delta: ~D" delta))))

(defmacro with-symbol-mutex ((sym &key (recursive t)) &body body)
  "Not implemented."
  (declare (ignore sym recursive))
  `(progn ,@body))


(defmacro with-inline-assembly ((&key returns (side-effects t) (type t)) &body program)
  `(with-inline-assembly-case (:side-effects ,side-effects :type ,type)
     (do-case (t ,returns)
       ,@program)))

(defmacro numargs-case (&rest args)
  (declare (ignore args))
  (error "numargs-case at illegal position."))

(defmacro movitz-backquote (expression)
  (declare (ignore expression))
  `(warn "movitz-backquote!"))

(define-compiler-macro spin-wait-pause ()
  "Insert a pause instruction, which improves performance of
busy-waiting loop on P4."
  '(with-inline-assembly (:returns :nothing)
    (:pause)))

(defmacro spin-wait-pause ())

(defmacro capture-reg8 (reg)
  `(with-inline-assembly (:returns :eax)
     (:movzxb ,reg :eax)
     (:shll ,movitz::+movitz-fixnum-shift+ :eax)))

(defmacro asm (&rest prg)
  "Insert a single assembly instruction that returns noting."
  `(with-inline-assembly (:returns :nothing)
     ,prg))

(defmacro asm1 (&rest prg)
  "Insert a single assembly instruction that returns a value in eax."
  `(with-inline-assembly (:returns :eax)
     ,prg))

(defmacro load-global-constant (name &key thread-local)
  (if thread-local
      `(with-inline-assembly (:returns :eax)
	 (:locally (:movl (:edi (:edi-offset ,name)) :eax)))
    `(with-inline-assembly (:returns :eax)
       (:globally (:movl (:edi (:edi-offset ,name)) :eax)))))

(defmacro load-global-constant-u32 (name &key thread-local)
  (if thread-local
      `(with-inline-assembly (:returns :untagged-fixnum-ecx)
	 (:locally (:movl (:edi (:edi-offset ,name)) :ecx)))
    `(with-inline-assembly (:returns :untagged-fixnum-ecx)
       (:globally (:movl (:edi (:edi-offset ,name)) :ecx)))))

;;;(define-compiler-macro (setf %runtime-context-slot) (value slot-name)
;;;  `(with-inline-assembly (:returns :eax)
;;;     (:compile-form (:result-mode :eax) ,value)
;;;     (:movl :eax (:edi ,(movitz::global-constant-offset (movitz::eval-form slot-name))))))

(define-compiler-macro halt-cpu ()
  (let ((infinite-loop-label (make-symbol "infinite-loop")))
    `(with-inline-assembly (:returns :nothing)
       ,infinite-loop-label
       (:movl #xabbabeef :eax)
       (:halt)
       (:jmp ',infinite-loop-label))))

(defmacro function-name-or-nil ()
  (let ((function-name-not-found-label (gensym)))
    `(with-inline-assembly (:returns :eax)
       (:movl :edi :eax)
       ;; Check if EDX is a symbol
       (:xorb ,(movitz::tag :symbol) :dl)
       (:testb 7 :dl)
       (:jnz ',function-name-not-found-label)
       (:xorb ,(movitz::tag :symbol) :dl)
       ;; Check if symbol's function-value is eq to our current funobj (in ESI).
       (:cmpl :esi (:edx ,(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value)))
       (:jne ',function-name-not-found-label)
       (:movl :edx :eax)
       ,function-name-not-found-label)))

(defmacro word-nibble (word-form nibble)
  (check-type nibble (integer 0 7))
  `(with-inline-assembly (:returns :untagged-fixnum-eax)
     (:compile-form (:result-mode :eax) ,word-form)
     (:shrl ,(* 4 nibble) :eax)
     (:andl #xf :eax)))

(require :muerte/setf)

