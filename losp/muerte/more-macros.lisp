;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      more-macros.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Jun  7 15:05:57 2002
;;;;                
;;;; $Id: more-macros.lisp,v 1.18 2004/08/23 13:49:40 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/setf)
(provide :muerte/more-macros)

(in-package muerte)

(defmacro pop (&environment env place)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't pop a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars)))
      `(let ,(mapcar #'list tmp-vars tmp-var-init-forms)
	 (let ((,store-var ,getter-form))
	   (prog1
	       (car ,store-var)
	     (setq ,store-var (cdr ,store-var))
	     ,setter-form))))))

(define-compiler-macro pop (&whole form &environment env place)
  (if (and (symbolp place)
	   (typep (movitz::movitz-binding place env) 'movitz::lexical-binding))
      `(with-inline-assembly (:returns :ebx)
	 (:compile-form (:result-mode :eax) ,place)
	 (:globally (:call (:edi (:edi-offset fast-cdr-car))))
	 (:lexical-store ,place :eax))
      #+ignore
      `(prog1 (car ,place)
	 (setq ,place (cdr ,place)))
    form))

(defmacro push (&environment env item place)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't push a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (item-var (gensym "push-item-")))
      `(let ((,item-var ,item)
	     ,@(mapcar #'list tmp-vars tmp-var-init-forms))
	 (let ((,store-var (cons ,item-var ,getter-form)))
	   ,setter-form)))))

#+ignore
(define-compiler-macro push (&whole form &environment env item place)
  (if (and (symbolp place)
	   (not (typep (movitz::movitz-binding place env) 'movitz::symbol-macro-binding)))
      `(setq ,place (cons ,item ,place))
    form))
  
(defmacro pushnew (&environment env item place &key (key ''identity) (test ''eq) test-not)
  (when test-not
    (error "Test-not not supported."))
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't pushnew a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (item-var (gensym "push-item-")))
      `(let ((,item-var ,item)
	     ,@(mapcar #'list tmp-vars tmp-var-init-forms))
	 (let ((old-value ,getter-form))
	   (if (not (member ,item-var old-value :key ,key :test ,test))
	       (let ((,store-var (cons ,item-var old-value)))
		 ,setter-form)
	     old-value))))))
  
(defmacro remf (&environment env place indicator)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't remf a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (indicator-var (gensym "remf-indicator-")))
      `(let (,@(mapcar #'list tmp-vars tmp-var-init-forms)
	     (,indicator-var ,indicator))
	 (let ((p ,getter-form))
	   (cond
	    ((null p) nil)
	    ((eq ,indicator-var (car p))
	     (let ((,store-var (cddr p)))
	       ,setter-form)
	     t)
	    (t (do ((x (cdr p) (cddr x))
		    (y (cddr p) (cddr y)))
		   ((null y) nil)
		 (when (eq ,indicator-var (car y))
		   (setf (cdr x) (cddr y))
		   (return t))))))))))

(define-compiler-macro dotimes (&whole form-decline (var count-form &optional result-form)
				&body declarations-and-body)
  (if (not (movitz:movitz-constantp count-form))
      form-decline
    (let ((count (movitz::eval-form count-form)))
      (check-type count (integer 0 *))
      (cond
       ((= 0 count)
	nil)
       ((= 1 count)
	`(let ((,var 0))
	   ,@declarations-and-body
	   ,result-form))
       (t `(do ((,var 0 (1+ ,var)))
	       ((>= ,var ,count-form) ,result-form)
	     (declare (type (integer 0 ,count-form) ,var))
	     ,@declarations-and-body))))))

(defmacro dotimes ((var count-form &optional result-form) &body declarations-and-body)
  (let ((count-var (gensym)))
    `(do ((,count-var ,count-form)
	  (,var 0 (1+ ,var)))
	 ((<= ,count-var ,var) ,result-form)
       ,@declarations-and-body)))

(defmacro dolist ((var list-form &optional result-form) &body declarations-and-body)
  (let ((cons-var (gensym "dolist-cons-")))
    `(do ((,cons-var ,list-form))
	 ((null ,cons-var) ,result-form)
       (let ((,var (pop ,cons-var)))
	 ,@declarations-and-body))))

(defmacro letf* (bindings &body body &environment env)
  "Does what one might expect, saving the old values and setting the generalized
  variables to the new values in sequence.  Unwind-protects and get-setf-method
  are used to preserve the semantics one might expect in analogy to let*,
  and the once-only evaluation of subforms."
  (labels ((do-bindings
            (bindings)
            (cond ((null bindings) body)
                  (t (multiple-value-bind (dummies vals newval setter getter)
			 (get-setf-expansion (caar bindings) env)
                       (let ((save (gensym)))
                         `((let* (,@(mapcar #'list dummies vals)
                                  (,(car newval) ,(cadar bindings))
                                  (,save ,getter))
                             (unwind-protect
                               (progn ,setter
                                      ,@(do-bindings (cdr bindings)))
                               (setq ,(car newval) ,save)
                               ,setter)))))))))
    (car (do-bindings bindings))))

(defmacro with-letf (clauses &body body)
  "Each clause is (<place> &optional <value-form> <prev-var>).
Execute <body> with alternative values for each <place>.
Note that this scheme does not work well with respect to multiple threads.
XXX This should actually be using get-setf-expansion etc. to deal with
proper evaluation of the places' subforms."
  (let ((place-value-save (loop for (place . value-save) in clauses
			      if value-save
			      collect (list place `(progn ,(first value-save))
					    (or (second value-save) (gensym)))
			      else collect (list place nil (gensym)))))
    `(let (,@(loop for (place nil save-var) in place-value-save
		 collect `(,save-var ,place)))
       (unwind-protect
	   (progn (setf ,@(loop for (place value) in place-value-save
			      append `(,place ,value)))
		  ,@body)
	 (setf ,@(loop for (place nil save) in place-value-save
		     append `(,place ,save)))))))

(defmacro with-alternative-fdefinitions (clauses &body body)
  "Each clause is (<name> <definition>). Execute <body> with alternative
fdefinitions for each <name>. Note that this scheme does not work well with
respect to multiple threads."
  (let ((tmp-name-def (loop for (name def) in clauses
			  collect (list (gensym) name def))))
    `(let (,@(loop for (tmp name) in tmp-name-def collect `(,tmp (fdefinition ',name))))
       (macrolet ((previous-fdefinition (&whole form name)
		    (case name
		      ,@(loop for (tmp name) in tmp-name-def
			    collect `(,name ',tmp))
		      (t form))))
	 (unwind-protect
	     (progn (setf ,@(loop for (nil name def) in tmp-name-def
				append `((fdefinition ',name) ,def)))
		    ,@body)
	   (setf ,@(loop for (tmp name) in tmp-name-def
		       append `((fdefinition ',name) ,tmp))))))))

(defmacro eof-or-lose (stream eof-errorp eof-value)
  `(if ,eof-errorp
       (error 'end-of-file :stream ,stream)
       ,eof-value))


(defmacro with-bochs-tracing ((&optional (value 1)) &body body)
  "Bochs magic."
  `(let ((old-flags (muerte::%run-time-context-slot 'bochs-flags)))
     (unwind-protect
	 (progn
	   (setf (muerte::%run-time-context-slot 'bochs-flags) ,value)
	   ,@body)
       (setf (muerte::%run-time-context-slot 'bochs-flags) old-flags))))

  
  

(defmacro handler-bind (bindings &body forms)
  (if (null bindings)
      `(progn ,@forms)
    (labels ((make-handler (binding)
	       (destructuring-bind (type handler)
		   binding
		 (cond
		  #+ignore
		  ((and (listp handler)
			(eq 'lambda (first handler))
			(= 1 (length (second handler))))
		   `(cons t (lambda (x)
			      (when (typep x ',type)
				(let ((,(first (second handler)) x))
				  ,@(cddr handler)))
			      nil)))
		  #+ignore
		  ((and (listp handler)
			(eq 'function (first handler))
			(listp (second handler))
			(eq 'lambda (first (second handler)))
			(= 1 (length (second (second handler)))))
		   (make-handler (list type (second handler))))
		  (t `(cons ',type ,handler))))))
      `(let ((*active-condition-handlers*
	      (cons (list ,@(mapcar #'make-handler #+ignore (lambda (binding)
							      `(cons ',(first binding)
								     ,(second binding)))
				    bindings))
		    *active-condition-handlers*)))
	 ,@forms))))

(defmacro handler-case (expression &rest clauses)
  (multiple-value-bind (normal-clauses no-error-clauses)
      (loop for clause in clauses
	  if (eq :no-error (car clause))
	  collect clause into no-error-clauses
	  else collect clause into normal-clauses
	  finally (return (values normal-clauses no-error-clauses)))
    (case (length no-error-clauses)
      (0 (let ((block-name (gensym "handler-case-block-"))
	       (var-name (gensym "handler-case-var-"))
	       (temp-name (gensym "handler-case-temp-var-"))
	       (specs (mapcar (lambda (clause)
				(list clause (gensym "handler-case-clause-tag-")))
			      normal-clauses)))
	   `(block ,block-name
	      (let (,var-name)
		(tagbody
		  (handler-bind ,(mapcar (lambda (clause-spec)
					   (let* ((clause (first clause-spec))
						  (go-tag (second clause-spec))
						  (typespec (first clause)))
					     `(,typespec (lambda (,temp-name)
							   (setq ,var-name ,temp-name)
							   (go ,go-tag)))))
				  specs)
		    (return-from ,block-name ,expression))
		  ,@(mapcan (lambda (clause-spec)
			      (let* ((clause (first clause-spec))
				     (go-tag (second clause-spec))
				     (var (first (second clause)))
				     (body (cddr clause)))
				(if (not var)
				    `(,go-tag (return-from ,block-name
						(let () ,@body)))
				  `(,go-tag (return-from ,block-name
					      (let ((,var ,var-name))
						,@body))))))
			    specs))))))
      (t (error "Too many no-error clauses.")))))

(defmacro ignore-errors (&body body)
  `(handler-case (progn ,@body)
     (error (c) (values nil c))))

(defmacro with-accessors (slot-entries instance-form &body declarations-and-forms)
  (let ((instance-variable (gensym "with-accessors-instance-")))
    `(let ((,instance-variable ,instance-form))
       (declare (ignorable ,instance-variable))
       (symbol-macrolet ,(loop for (variable-name accessor-name) in slot-entries
			     collecting `(,variable-name (,accessor-name ,instance-variable)))
	 ,@declarations-and-forms))))

(defmacro with-slots (slot-entries instance-form &body declarations-and-forms)
  (let ((object-var (gensym "with-slots-object-")))
    `(symbol-macrolet ,(mapcar (lambda (entry)
				 (let ((var (if (atom entry) entry (car entry)))
				       (slot (if (atom entry) entry (cadr entry))))
				   `(,var (slot-value ,object-var ',slot))))
			       slot-entries)
       (let ((,object-var ,instance-form))
	 ,@declarations-and-forms))))


(define-compiler-macro %bignum-bigits (x)
  `(with-inline-assembly (:returns :eax :type (unsigned-byte 14))
     (:compile-form (:result-mode :eax) ,x)
     (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length))
	      :eax)
     (:testb 3 :al)			; Just to be sure..
     (:jnz '(:sub-program () (:int 63)))))

(defmacro with-simple-restart ((name format-control &rest format-arguments)
					    &body body)
  `(with-basic-restart (,name 'with-simple-restart nil nil
			      ,format-control ,@format-arguments)
     ,@body))

(define-compiler-macro %run-time-context-slot (&whole form &environment env slot-name
					       &optional (context '(current-run-time-context)))
  (if (not (and (movitz:movitz-constantp slot-name env)
		(equal context '(current-run-time-context))))
      form
    (let ((slot-name (movitz::eval-form slot-name env)))
      (ecase (bt:binary-slot-type 'movitz::movitz-run-time-context
				  (intern (symbol-name slot-name) :movitz))
	(movitz::word
	 `(with-inline-assembly (:returns :eax)
	    (:locally (:movl (:edi (:edi-offset ,slot-name)) :eax))))
	(movitz::code-vector-word
	 `(with-inline-assembly (:returns :eax)
	    (:locally (:movl (:edi (:edi-offset ,slot-name)) :eax))
	    (:subl ,movitz::+code-vector-word-offset+ :eax)))
	(movitz::lu32
	 `(with-inline-assembly (:returns :untagged-fixnum-ecx)
	    (:locally (:movl (:edi (:edi-offset ,slot-name)) :ecx))))))))

(define-compiler-macro malloc-pointer-words (words)
  `(with-inline-assembly (:returns :eax :type pointer)
     (:compile-form (:result-mode :eax) ,words)
     (:call-local-pf malloc-pointer-words)))

(define-compiler-macro malloc-non-pointer-words (words)
  `(with-inline-assembly (:returns :eax :type pointer)
     (:compile-form (:result-mode :eax) ,words)
     (:call-local-pf malloc-non-pointer-words)))

(define-compiler-macro read-time-stamp-counter ()
  `(with-inline-assembly-case ()
     (do-case (:register :same)
       (:std)
       (:rdtsc)
       (:movl :edi :edx)
       (:leal ((:eax ,movitz:+movitz-fixnum-factor+)) (:result-register))
       (:cld))
     (do-case (t :multiple-values)
       (:compile-form (:result-mode :multiple-values) (no-macro-call read-time-stamp-counter)))))

(defmacro without-interrupts (&body body)
  (let ((var (gensym "interrupts-enabled-p-")))
    `(let ((,var (logbitp ,(position :if +eflags-map+) (eflags))))
       (unwind-protect (progn (cli) ,@body)
	 (when ,var (sti))))))


;;; Some macros that aren't implemented, and we want to give compiler errors.

(defmacro define-unimplemented-macro (name)
  `(defmacro ,name (&rest args)
     (declare (ignore args))
     (with-simple-restart (continue "Proceed with a NIL expansion for ~S." ',name)
       (error "Macro ~S is not implemented yet." ',name))))

(define-unimplemented-macro with-open-file)
(define-unimplemented-macro restart-case)
