;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      basic-macros.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: basic-macros.lisp,v 1.79 2009-11-10 20:19:57 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/basic-macros)

(in-package muerte)

(defmacro defun (function-name lambda-list &body body)
  "Define a function."
  (multiple-value-bind (real-body declarations docstring)
      (movitz::parse-docstring-declarations-and-body body 'cl:declare)
    (let ((block-name (compute-function-block-name function-name)))
      `(progn
	 (make-named-function ,function-name
			      ,lambda-list
			      ,declarations
			      ,docstring
			      (block ,block-name ,@real-body))
	 ',function-name))))

(defmacro defun-by-proto (function-name proto-name &rest parameters)
  `(define-prototyped-function ,function-name ,proto-name ,@parameters))

(defmacro define-compiler-macro (name lambda-list &body body)
  `(progn
     (muerte::define-compiler-macro-compile-time ,name ,lambda-list ,body)
     ',name))

(defmacro define-primitive-function (function-name lambda-list docstring &body body)
  (declare (ignore lambda-list))
  (assert (stringp docstring) (docstring)
    "Mandatory docstring for define-primitive-function.")
  `(make-primitive-function ,function-name ,docstring
			    ,(cons 'cl:progn body)))

(defmacro defpackage (package-name &rest options)
  (let ((uses (union (if (not (assoc :use options))
			 (list 'muerte.cl)
			 (cdr (assoc :use options)))
		     (when (find-package package-name)
		       (mapcar #'package-name (package-use-list package-name))))))
    (setf uses (mapcar (lambda (use)
			 (if (member use (cons :common-lisp (package-nicknames :common-lisp))
				     :test #'string=)
			     :muerte.cl
			     use))
		       uses))
    (when (or (member :muerte.cl uses :test #'string=)
	      (member :muerte.common-lisp uses :test #'string=))
      (push '(:shadowing-import-from :common-lisp nil) options))
    (let ((movitz-options (cons (cons :use uses)
				(remove :use options :key #'car))))
      `(eval-when (:compile-toplevel)
	(defpackage ,package-name ,@movitz-options)))))

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

(define-compiler-macro if (test-form then-form &optional else-form &environment env)
  (when (and (movitz:movitz-constantp then-form env) (movitz:movitz-constantp else-form env))
    (warn "if: ~S // ~S" then-form else-form))
  (if else-form
      `(compiled-cond (,test-form ,then-form) (t ,else-form))
    `(compiled-cond (,test-form ,then-form))))

(defmacro/cross-compilation throw (tag result-form)
  (let ((tag-var (gensym "throw-tag-")))
    `(let ((,tag-var ,tag))
       (exact-throw (find-catch-tag ,tag-var)
		    ,result-form
		    (error 'throw-error :tag ,tag-var)))))

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

(defmacro/cross-compilation define-compile-time-variable (name value)
  (let ((the-value (eval value)))
    `(progn
       (eval-when (:compile-toplevel)
	 (define-symbol-macro ,name
	     (getf (movitz::image-compile-time-variables movitz::*image*)
		   ',name))
	 (setf ,name (or ,name ',the-value)))
       (eval-when (:load-toplevel :excute)
	 (defvar ,name 'uninitialized-compile-time-variable)))))

(defmacro/cross-compilation let* (var-list &body declarations-and-body)
  (multiple-value-bind (body declarations)
      (movitz::parse-declarations-and-body declarations-and-body 'cl:declare)
    (labels ((expand (rest-vars body)
	       (if (null rest-vars)
		   body
		 `((let (,(car rest-vars))
		     (declare ,@declarations)
		     ,@(expand (cdr rest-vars) body))))))
      (if (endp var-list)
	  `(let () ,@body)
	(car (expand var-list body))))))

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
	   (do (ss ls (p pairs))
	       ((endp p)
		(values (nreverse ss)
			(nreverse ls)))
	     (let ((var (pop p))
		   (form (pop p))
		   (temp-var (gensym)))
	       (push (list temp-var form) ls)
	       (push var ss)
	       (push temp-var ss)))
	 `(let ,let-specs
	    (setq ,@setq-specs))))))

(defmacro return (&optional (result-form nil result-form-p))
  (if result-form-p
      `(return-from nil ,result-form)
    `(return-from nil)))

(defmacro do (var-specs (end-test-form &rest result-forms) &body declarations-and-body)
  (flet ((var-spec-let-spec (var-spec)
	   (cond
	     ((symbolp var-spec)
	      var-spec)
	     ((cddr var-spec)
	      (subseq var-spec 0 2))
	     (t var-spec)))
	 (var-spec-var (spec)
	   (if (symbolp spec) spec (car spec)))
	 (var-spec-step-form (var-spec)
	   (and (listp var-spec)
		(= 3 (list-length var-spec))
		(or (third var-spec)
		    '(quote nil)))))
    (multiple-value-bind (body declarations)
	(parse-declarations-and-body declarations-and-body)
      (let* ((loop-tag (gensym "do-loop"))
	     (start-tag (gensym "do-start")))
	`(block nil
	   (let ,(mapcar #'var-spec-let-spec var-specs)
	     (declare ,@declarations)
	     (tagbody
		(go ,start-tag)
		,loop-tag
		,@body
		(psetq ,@(mapcan (lambda (var-spec)
				   (let ((step-form (var-spec-step-form var-spec)))
				     (when step-form
				       (list (var-spec-var var-spec)
					     step-form))))
				 var-specs))
		,start-tag
		(unless ,end-test-form (go ,loop-tag)))
	     ,@result-forms))))))

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
	(parse-declarations-and-body declarations-and-body 'cl:declare)
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
	(parse-declarations-and-body declarations-and-body)
      (let* ((loop-tag (gensym "do*-loop"))
	     (start-tag (gensym "do*-start")))
	`(block nil
	   (let* ,(mapcar #'var-spec-let-spec var-specs)
	     (declare ,@declarations)
	     (tagbody
		(go ,start-tag)
		,loop-tag
		,@body
		(setq ,@(mapcan (lambda (var-spec)
				  (let ((step-form (var-spec-step-form var-spec)))
				    (when step-form
				      (list (var-spec-var var-spec)
					    step-form))))
				var-specs))
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
  (let ((key-var (make-symbol "case-key-var")))
    `(let ((,key-var ,keyform))
       (cond
	 ,@(mapcar (lambda (clause)
		     (destructuring-bind (keys . forms)
			 clause
		       (let ((forms (or forms '(nil))))
                         (cond
                           ((or (eq keys 't)
                                (eq keys 'otherwise))
                            `(t ,@forms))
                           ((not (listp keys))
                            `((eql ,key-var ',keys) ,@forms))
                           (t `((or ,@(mapcar (lambda (k)
                                                `(eql ,key-var ',k))
                                              keys))
                                ,@forms))))))
		   clauses)))))

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
  (let ((ecase-var (gensym))) 	 
    `(let ((,ecase-var ,keyform)) 	 
       (case ,ecase-var 	 
	 ,@clauses 	 
	 (t (ecase-error ,ecase-var 	 
			 ',(mapcan (lambda (clause) 	 
				     (let ((x (car clause))) 	 
				       (if (atom x) 	 
					   (list x) 	 
					   (copy-list x)))) 	 
				   clauses)))))))

(define-compiler-macro asm-register (register-name)
  (if (member register-name '(:eax :ebx :ecx :untagged-fixnum-ecx :edx))
      `(with-inline-assembly (:returns ,register-name) ())
    `(with-inline-assembly (:returns :eax)
       (:movl ,register-name :eax))))

(defmacro/cross-compilation movitz-accessor (object-form type slot-name)
  (warn "movitz-accesor deprecated.")
  `(with-inline-assembly (:returns :register :side-effects nil)
     (:compile-form (:result-mode :eax) ,object-form)
     (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
      :movl (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
				   (find-symbol (string slot-name) :movitz)))
	    (:result-register))))

(defmacro/cross-compilation setf-movitz-accessor ((object-form type slot-name) value-form)
  (warn "setf-movitz-accesor deprecated.")
  `(with-inline-assembly (:returns :eax :side-effects t)
     (:compile-two-forms (:eax :ebx) ,value-form ,object-form)
     (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
      :movl :eax (:ebx ,(bt:slot-offset (find-symbol (string type) :movitz)
					(find-symbol (string slot-name) :movitz))))))

;; (defmacro movitz-accessor-u16 (object-form type slot-name)
;;   `(with-inline-assembly (:returns :eax)
;;      (:compile-form (:result-mode :eax) ,object-form)
;;      (:movzxw (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
;; 				     (find-symbol (string slot-name) :movitz)))
;; 	      :ecx)
;;      (:leal ((:ecx #.movitz::+movitz-fixnum-factor+) :edi ,(- (movitz::image-nil-word movitz::*image*)))
;; 	    :eax)))

;; (defmacro set-movitz-accessor-u16 (object-form type slot-name value)
;;   `(with-inline-assembly (:returns :eax)
;;      (:compile-two-forms (:eax :ecx) ,object-form ,value)
;;      (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
;;      (:movw :cx (:eax ,(bt:slot-offset (find-symbol (string type) :movitz)
;; 				       (find-symbol (string slot-name) :movitz))))
;;      (:leal ((:ecx #.movitz::+movitz-fixnum-factor+) :edi ,(- (movitz::image-nil-word movitz::*image*)))
;; 	    :eax)))

(define-compiler-macro movitz-type-word-size (type &environment env)
  (if (not (movitz:movitz-constantp type env))
      (error "Non-constant movitz-type-word-size call.")
    (movitz::movitz-type-word-size (intern (symbol-name (movitz:movitz-eval type env))
					   :movitz))))

(define-compiler-macro movitz-type-slot-offset (type slot &environment env)
  (if (not (and (movitz:movitz-constantp type env)
		(movitz:movitz-constantp slot env)))
      (error "Non-constant movitz-type-slot-offset call.")
    (bt:slot-offset (intern (symbol-name (movitz:movitz-eval type env)) :movitz)
		    (intern (symbol-name (movitz:movitz-eval slot env)) :movitz))))

(define-compiler-macro movitz-type-location-offset (type slot &environment env)
  (if (not (and (movitz:movitz-constantp type env)
		(movitz:movitz-constantp slot env)))
      (error "Non-constant movitz-type-slot-offset call.")
    (truncate (+ -6 (bt:slot-offset (intern (symbol-name (movitz:movitz-eval type env)) :movitz)
				    (intern (symbol-name (movitz:movitz-eval slot env)) :movitz)))
	      4)))

(define-compiler-macro not (x)
  `(muerte::inlined-not ,x))

(define-compiler-macro null (x)
  `(muerte::inlined-not ,x))

(define-compiler-macro eq (&whole form &environment env x y)
  (cond
   ((movitz:movitz-constantp y env)
    (let ((y (movitz:movitz-eval y env)))
      (cond
       ((movitz:movitz-constantp x env)
	(warn "constant eq!: ~S" form)
	(eq y (movitz:movitz-eval x env)))
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
   ((movitz:movitz-constantp x env)
    `(eq ,y ',(movitz:movitz-eval x env)))
   (t `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	 (:compile-two-forms (:eax :ebx) ,x ,y)
	 (:cmpl :eax :ebx)))))

(define-compiler-macro eql (x y)
  `(let ((x ,x) (y ,y))
     (eql%b x y)))

(define-compiler-macro values (&rest sub-forms)
  `(inline-values ,@sub-forms))

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
  (let ((tmp-vars (mapcar (lambda (v)
			    (declare (ignore v))
			    (gensym))
			  vars)))
    `(multiple-value-bind ,tmp-vars ,form
       (setq ,@(mapcan #'list vars tmp-vars)))))

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

(define-compile-time-variable *symbol-macros* (make-hash-table :test #'eq))

(defmacro/cross-compilation define-symbol-macro (symbol expansion)
  (check-type symbol symbol "a symbol-macro symbol")
  `(progn
     (eval-when (:compile-toplevel)
       (movitz::movitz-env-add-binding nil (make-instance 'movitz::symbol-macro-binding
                                            :name ',symbol
                                            :expander (lambda (form env)
                                                        (declare (ignore form env))
                                                        (movitz::translate-program ',expansion
                                                         :cl :muerte.cl)))))
     (setf (gethash ',symbol *symbol-macros*) ',expansion)
     ',symbol))

(defmacro check-type (place type &optional type-string)
  (if (not (stringp type-string))
      `(let ((place-value ,place))
	 (unless (typep place-value ',type)
	   (check-type-failed place-value ',type ',place)))
    `(let ((place-value ,place))
       (unless (typep place-value ',type)
	 (check-type-failed place-value ',type ',place ,type-string)))))

(define-compiler-macro check-type (&whole form place type &optional type-string &environment env)
  (declare (ignore type-string))
  (cond
   ((movitz:movitz-constantp place env)
    (assert (typep (movitz::eval-form place env) type))
    nil)
   (t (if (member type '(standard-gf-instance function pointer atom
			 integer fixnum positive-fixnum cons symbol character null list
			 string vector simple-vector vector-u8 vector-u16))
	  `(with-inline-assembly (:returns :nothing :labels (check-type-failed retry-check-type))
	    retry-check-type
	     (:compile-form (:result-mode (:boolean-branch-on-false . check-type-failed))
			    (typep ,place ',type))
	     (:jnever '(:sub-program (check-type-failed)
			(:compile-form (:result-mode :edx) (quote ,type))
			(:compile-form (:result-mode :ignore)
			 (setf ,place (with-inline-assembly (:returns :eax)
					(:int 60))))
			(:jmp 'retry-check-type))))
	form))))

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
     (with-inline-assembly-case (:side-effects t)
       (do-case (t :register)
	 (:cons-get :car (:lexical-binding cell) (:result-register))))))

(define-compiler-macro cdr (x)
  `(let ((cell ,x))
     (with-inline-assembly-case (:side-effects t)
       (do-case (t :register)
	 (:cons-get :cdr (:lexical-binding cell) (:result-register))))))

(define-compiler-macro cadr (x)
  `(car (cdr ,x)))

(define-compiler-macro cddr (x)
  `(cdr (cdr ,x)))

(define-compiler-macro caddr (x)
  `(car (cdr (cdr ,x))))

(define-compiler-macro cadddr (x)
  `(car (cdr (cdr (cdr ,x)))))

(define-compiler-macro cdar (x)
  `(cdr (car ,x)))
			     
(define-compiler-macro rest (x) `(cdr ,x))
(define-compiler-macro first (x) `(car ,x))
(define-compiler-macro second (x) `(cadr ,x))
(define-compiler-macro third (x) `(caddr ,x))
(define-compiler-macro fourth (x) `(cadddr ,x))

(define-compiler-macro (setf car) (value cell &environment env)
  (if (and (movitz:movitz-constantp value env)
	   (eq nil (movitz::eval-form value env)))
      `(with-inline-assembly (:returns :edi)
	 (:compile-form (:result-mode :eax) ,cell)
	 (:leal (:eax -1) :ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 61)))
	 (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	  :movl :edi (:eax -1)))
    `(with-inline-assembly (:returns :eax)
       (:compile-two-forms (:eax :ebx) ,value ,cell)
       (:leal (:ebx -1) :ecx)
       (:testb 7 :cl)
       (:jnz '(:sub-program ()
	       (:movl :ebx :eax)
	       (:xorl :ecx :ecx)
	       (:int 69)))
       (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	:movl :eax (:ebx -1)))))

(define-compiler-macro (setf cdr) (value cell &environment env)
  (if (and (movitz:movitz-constantp value env)
	   (eq nil (movitz::eval-form value env)))
      `(with-inline-assembly (:returns :edi)
	 (:compile-form (:result-mode :eax) ,cell)
	 (:leal (:eax -1) :ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 61)))
	 (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	  :movl :edi (:eax 3)))
    `(with-inline-assembly (:returns :eax)
       (:compile-two-forms (:eax :ebx) ,value ,cell)
       (:leal (:ebx -1) :ecx)
       (:testb 7 :cl)
       (:jnz '(:sub-program ()
	       (:movl :ebx :eax)
	       (:xorl :ecx :ecx)
	       (:int 69)))
       (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	:movl :eax (:ebx 3)))))

(define-compiler-macro rplaca (cons object)
  `(with-inline-assembly (:returns :eax)
     (:compile-two-forms (:eax :ebx) ,cons ,object)
     (:leal (:eax -1) :ecx)
     (:testb 7 :cl)
     (:jnz '(:sub-program ()
	     (:xorl :ecx :ecx)
	     (:int 69)))
     (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
      :movl :ebx (:eax -1))))

(define-compiler-macro rplacd (cons object)
  `(with-inline-assembly (:returns :eax)
     (:compile-two-forms (:eax :ebx) ,cons ,object)
     (:leal (:eax -1) :ecx)
     (:testb 7 :cl)
     (:jnz '(:sub-program ()
	     (:xorl :ecx :ecx)
	     (:int 69)))
     (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
      :movl :ebx (:eax 3))))

(define-compiler-macro endp (x)
  `(let ((cell ,x))
     (with-inline-assembly-case (:side-effects nil)
       (do-case (t :same)
	 (:endp (:lexical-binding cell) (:returns-mode))))))

(define-compiler-macro cons (car cdr)
  `(compiled-cons ,car ,cdr))

(define-compiler-macro list (&whole form &rest elements &environment env)
  (case (length elements)
    (0 nil)
    (1 `(cons ,(car elements) nil))
    (t form)))


(defmacro/cross-compilation with-unbound-protect (x &body error-continuation &environment env)
  (cond
   ((movitz:movitz-constantp x env)
    `(values ,x))
   (movitz::*compiler-use-into-unbound-protocol*
    (let ((unbound-continue (gensym "unbound-continue-")))
      `(with-inline-assembly (:returns :register)
	 (:compile-form (:result-mode :register) ,x)
	 (:cmpl -1 (:result-register))
	 (:jo '(:sub-program (unbound)
		(:compile-form (:result-mode :eax) (progn ,@error-continuation))
		(:jmp ',unbound-continue)))
	 ,unbound-continue)))
   (t (let ((var (gensym)))
	`(let ((,var ,x))
	   (if (not (eq ,var (load-global-constant new-unbound-value)))
	       ,var
	     (progn ,@error-continuation)))))))

(define-compiler-macro current-run-time-context ()
  `(with-inline-assembly (:returns :register)
     (:locally (:movl (:edi (:edi-offset self)) (:result-register)))))

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
       (:movl (:edx (:offset movitz-symbol function-value)) :esi)
       (:jmp 'funobj-ok)
      not-symbol
       (:cmpb 7 :cl)
       (:jne '(:sub-program (not-funobj)
               (:movb 1 :cl)
	       (:int 69)))
       (:cmpb ,(movitz:tag :funobj) (:edx ,movitz:+other-type-offset+))
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
                    (:movb 1 :cl)
		    (:int 69)))
	    (:cmpb ,(movitz::tag :funobj) (:edx ,movitz:+other-type-offset+))
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
                   (:movb 1 :cl)
		   (:int 69)))
	   (:cmpb ,(movitz::tag :funobj) (:edx ,movitz:+other-type-offset+))
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
                   (:movb 1 :cl)
		   (:int 69)))
	   (:cmpb ,(movitz::tag :funobj) (:edx ,movitz:+other-type-offset+))
	   (:jne 'not-funobj)
	   (:movl :edx :esi)
	  funobj-ok
	   (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op)))
	   (:leal (:esp 4) :esp))))))

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
       (:compile-form (:result-mode :esi) fn)
       (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op)))
       (:leal (:esp 4) :esp))))

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

(defmacro/cross-compilation backquote (form)
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

(define-compiler-macro find-class (&whole form &environment env symbol &optional (errorp t) (environment nil envp))
  (declare (ignore errorp environment))
  (if (or envp (not (movitz:movitz-constantp symbol env)))
      form
    (let* ((type (movitz:movitz-eval symbol env))
	   (movitz-type (movitz-program type))
	   (cl-type (host-program type)))
      (cond
       ((eq t cl-type)
	`(load-global-constant the-class-t))
       ((member movitz-type (movitz::image-classes-map movitz:*image*))
	`(with-inline-assembly (:returns :register)
	   (:globally (:movl (:edi (:edi-offset classes)) (:result-register)))
	   (:movl ((:result-register) ,(movitz::class-object-offset movitz-type))
		  (:result-register))))
       (t (warn "unknown find-class: ~S [~S] [~S]" cl-type
		(and (symbolp cl-type) (symbol-package cl-type))
		(and (symbolp movitz-type) (symbol-package movitz-type)))
	  form))
      #+ignore
      (case cl-type
	((t) `(load-global-constant the-class-t))
	(fixnum '(load-global-constant the-class-fixnum))
	(null `(load-global-constant the-class-null))
	(symbol '(load-global-constant the-class-symbol))
	(cons '(load-global-constant the-class-cons))
	(t form)))))

(define-compiler-macro class-of (object)
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,object)
     (:movl :eax :ecx)
     (:andl #x7 :ecx)
     (:call (:edi (:ecx 4) ,(movitz::global-constant-offset 'fast-class-of)))))

(defmacro/cross-compilation std-instance-reader (slot instance-form)
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
	 (:jnz '(:sub-program () (:int 66)))
	 (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
	  :movl ((:result-register) ,(bt:slot-offset 'movitz::movitz-std-instance slot))
		(:result-register))))))

(defmacro/cross-compilation std-instance-writer (slot value instance-form)
  (let ((slot (intern (symbol-name slot) :movitz)))
    `(with-inline-assembly-case ()
       (do-case (t :eax)
	 (:compile-two-forms (:eax :ebx) ,value ,instance-form)
	 (:leal (:ebx ,(- (movitz::tag :other)))
		:ecx)
	 (:testb 7 :cl)
	 (:jnz '(:sub-program () (:int 66)))
	 (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	  :movl :eax (:ebx ,(bt:slot-offset 'movitz::movitz-std-instance slot)))))))

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


(defmacro with-inline-assembly ((&key returns (side-effects t) (type t) labels) &body program)
  `(with-inline-assembly-case (:side-effects ,side-effects :type ,type)
     (do-case (t ,returns :labels ,labels)
       ,@program)))

(defmacro numargs-case (&rest args)
  (declare (ignore args))
  (error "numargs-case at illegal position."))

(defmacro movitz-backquote (expression)
  (un-backquote expression 0))

(define-compiler-macro spin-wait-pause ()
  "Insert a pause instruction, which improves performance of
busy-waiting loop on P4."
  '(with-inline-assembly (:returns :nothing)
    (:pause)))

(defmacro spin-wait-pause ())

;; (defmacro capture-reg8 (reg)
;;   `(with-inline-assembly (:returns :eax)
;;      (:movzxb ,reg :eax)
;;      (:shll ,movitz::+movitz-fixnum-shift+ :eax)))

(define-compiler-macro asm (&rest prg)
  "Insert a single assembly instruction that returns noting."
  `(with-inline-assembly (:returns :nothing)
     ,prg))

(define-compiler-macro asm1 (&rest prg)
  "Insert a single assembly instruction that returns a value in eax."
  `(with-inline-assembly (:returns :eax)
     ,prg))

(defmacro load-global-constant (name &key thread-local)
  (if thread-local
      `(with-inline-assembly (:returns :register)
	 (:locally (:movl (:edi (:edi-offset ,name)) (:result-register))))
    `(with-inline-assembly (:returns :register)
       (:globally (:movl (:edi (:edi-offset ,name)) (:result-register))))))

(defmacro load-global-constant-u32 (name &key thread-local)
  (if thread-local
      `(with-inline-assembly (:returns :untagged-fixnum-ecx)
	 (:locally (:movl (:edi (:edi-offset ,name)) :ecx)))
    `(with-inline-assembly (:returns :untagged-fixnum-ecx)
       (:globally (:movl (:edi (:edi-offset ,name)) :ecx)))))

(define-compiler-macro halt-cpu (&optional eax-form)
  (let ((infinite-loop-label (make-symbol "infinite-loop")))
    `(with-inline-assembly (:returns :nothing)
       ,@(when eax-form
	   `((:compile-form (:result-mode :eax) ,eax-form)))
       ,infinite-loop-label
       (:halt)
       (:jmp ',infinite-loop-label))))

(define-compiler-macro function-name-or-nil ()
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
  `(with-inline-assembly (:returns :untagged-fixnum-ecx)
     (:compile-form (:result-mode :eax) ,word-form)
     (:movl :eax :ecx)
     (:shrl ,(* 4 nibble) :ecx)
     (:andl #xf :ecx)))

(define-compiler-macro boundp (symbol)
  `(with-inline-assembly-case ()
     (do-case (t :boolean-zf=0 :labels (boundp-done boundp-restart))
       (:compile-form (:result-mode :ebx) ,symbol)
       boundp-restart
       (:leal (:ebx ,(- (movitz:tag :null))) :ecx)
       (:testb 5 :cl)
       (:jne '(:sub-program ()
	       (:movl :ebx :eax)
	       (:load-constant symbol :edx)
	       (:int 60)
	       (:movl :eax :ebx)
	       (:jmp 'boundp-restart)))
       (:call-local-pf dynamic-variable-lookup)
       (:globally (:cmpl (:edi (:edi-offset new-unbound-value)) :eax)))))

(defmacro define-global-variable (name init-form &optional docstring)
  "A global variable will be accessed by ignoring local bindings."
  `(progn
     (defparameter ,name ,init-form ,docstring)
     (define-symbol-macro ,name (%symbol-global-value ',name))))

(define-compiler-macro assembly-register (register)
  `(with-inline-assembly (:returns :eax)
     (:movl ,register :eax)))

(defmacro with-allocation-assembly
    ((size-form &key object-register size-register fixed-size-p labels) &body code)
  (assert (eq object-register :eax))
  (assert (or fixed-size-p (eq size-register :ecx)))
  (let ((size-var (gensym "malloc-size-")))
    `(let ((,size-var ,size-form))
       (with-inline-assembly (:returns :eax :labels (retry-alloc retry-jumper ,@labels))
	 (:declare-label-set retry-jumper (retry-alloc))
	 ;; Set up atomically continuation.
	 (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
	 (:pushl 'retry-jumper)
	 ;; ..this allows us to detect recursive atomicallies.
	 (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
	 (:pushl :ebp)
	retry-alloc
	 (:movl (:esp) :ebp)
	 (:load-lexical (:lexical-binding ,size-var) :eax)
	 (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
	 ;; Now inside atomically section.
	 (:call-local-pf cons-pointer)
	 ,@code
	 ,@(when fixed-size-p
	     `((:load-lexical (:lexical-binding ,size-var) :ecx)))
	 (:call-local-pf cons-commit)
	 (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	 (:leal (:esp 16) :esp)))))

(defmacro with-non-pointer-allocation-assembly
    ((size-form &key object-register size-register fixed-size-p labels) &body code)
  (assert (eq object-register :eax))
  (assert (or fixed-size-p (eq size-register :ecx)))
  (let ((size-var (gensym "malloc-size-")))
    `(let ((,size-var ,size-form))
       (with-inline-assembly (:returns :eax :labels (retry-alloc retry-jumper ,@labels))
	 (:declare-label-set retry-jumper (retry-alloc))
	 ;; Set up atomically continuation.
	 (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
	 (:pushl 'retry-jumper)
	 ;; ..this allows us to detect recursive atomicallies.
	 (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
	 (:pushl :ebp)
	retry-alloc
	 (:movl (:esp) :ebp)
	 (:load-lexical (:lexical-binding ,size-var) :eax)
	 (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
	 ;; Now inside atomically section.
	 (:call-local-pf cons-non-pointer)
	 ,@code
	 ,@(when fixed-size-p
	     `((:load-lexical (:lexical-binding ,size-var) :ecx)))
	 (:call-local-pf cons-commit-non-pointer)
	 (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	 (:leal (:esp 16) :esp)))))

(defmacro with-non-header-allocation-assembly
    ((size-form &key object-register size-register fixed-size-p labels) &body code)
  (assert (eq object-register :eax))
  (assert (or fixed-size-p (eq size-register :ecx)))
  (let ((size-var (gensym "malloc-size-")))
    `(let ((,size-var ,size-form))
       (with-inline-assembly (:returns :eax :labels (retry-alloc retry-jumper ,@labels))
	 (:declare-label-set retry-jumper (retry-alloc))
	 ;; Set up atomically continuation.
	 (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
	 (:pushl 'retry-jumper)
	 ;; ..this allows us to detect recursive atomicallies.
	 (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
	 (:pushl :ebp)
	retry-alloc
	 (:movl (:esp) :ebp)
	 (:load-lexical (:lexical-binding ,size-var) :eax)
	 (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
	 ;; Now inside atomically section.
	 (:call-local-pf cons-non-header)
	 ,@code
	 ,@(when fixed-size-p
	     `((:load-lexical (:lexical-binding ,size-var) :ecx)))
	 (:call-local-pf cons-commit-non-header)
	 (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	 (:leal (:esp 16) :esp)))))

(define-compiler-macro cli ()
  `(with-inline-assembly (:returns :nothing) (:cli)))

(define-compiler-macro sti ()
  `(with-inline-assembly (:returns :nothing) (:sti)))


(defmacro check-the (type form)
  (let ((x (gensym "check-the-")))
    `(the ,type (let ((,x ,form)) (check-type ,x ,type) ,x))))

(require :muerte/setf)

