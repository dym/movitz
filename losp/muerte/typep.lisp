;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      typep.lisp
;;;; Description:   Implements TYPEP and TYPECASE.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Dec  8 11:07:53 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: typep.lisp,v 1.60 2008-04-27 19:45:43 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/typep)

(in-package muerte)


(defmacro typecase (keyform &rest clauses)
  (flet ((otherwise-clause-p (x)
	   (member (car x) '(t otherwise))
	   #+ignore
	   (member (car x) (mapcar #'intern '(t otherwise)))))
    (let ((key-var (make-symbol "typecase-key-var")))
      `(let ((,key-var ,keyform))
	 (cond ,@(loop for clause-head on clauses
		     as clause = (first clause-head)
		     as type = (first clause)
		     as forms = (rest clause)
;;;		     do (warn "clause: ~S" clause)
		     if (and (endp (rest clause-head)) (otherwise-clause-p clause))
		     collect (cons t forms)
		     else if (otherwise-clause-p clause)
		     do (error "Typecase's otherwise clause must be the last clause.")
		     else collect `((typep ,key-var ',type) ,@forms)))))))

(defmacro etypecase (keyform &rest clauses)
  (let ((key-var (make-symbol "etypecase-key-var-")))
    `(let ((,key-var ,keyform))
       (typecase ,key-var ,@clauses
		 (t (etypecase-error ,key-var ',(loop for c in clauses collect (car c))))))))

(define-compile-time-variable *simple-typespecs*
    ;; map symbol typespecs to typep-functions.
    (make-hash-table :test #'eq))

(define-compile-time-variable *compound-typespecs*
    ;; map compound typespecs to typep-functions.
    (make-hash-table :test #'eq))

(define-compile-time-variable *derived-typespecs*
    ;; map compound typespecs to typep-functions.
    (make-hash-table :test #'eq))

(eval-when (:compile-toplevel)
  (defvar *compiler-derived-typespecs*
      (make-hash-table :test #'eq)))


(define-compiler-macro typep (&whole form object type-specifier &environment env)
  (flet ((make-tag-typep (tag-name)
	   `(with-inline-assembly (:returns :boolean-zf=1)
	      (:compile-form (:result-mode :eax) ,object)
	      (:leal (:eax ,(cl:- (movitz:tag tag-name))) :ecx)
	      (:testb 7 :cl)))
	 (make-other-typep (tag-name &optional hi-byte)
	   (let ((cmp (if (not hi-byte)
			  `(:cmpb ,(movitz:tag tag-name)
				  (:eax ,movitz:+other-type-offset+))
			`(:cmpw ,(dpb hi-byte (byte 8 8) (movitz:tag tag-name))
				(:eax ,movitz:+other-type-offset+)))))
	     `(with-inline-assembly-case ()
		(do-case (:boolean-branch-on-false)
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(cl:- (movitz:tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:branch-when :boolean-zf=0)
		  ,cmp
		  (:branch-when :boolean-zf=0))
		(do-case (:boolean-branch-on-true :same :labels (other-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(cl:- (movitz:tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'other-typep-failed)
		  ,cmp
		  (:branch-when :boolean-zf=1)
		 other-typep-failed)
		(do-case (t :boolean-zf=1 :labels (other-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,movitz:+other-type-offset+) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'other-typep-failed)
		  ,cmp
		 other-typep-failed))))
	 (make-basic-vector-typep (element-type)
	   (assert (= 1 (- (bt:slot-offset 'movitz::movitz-basic-vector 'movitz::element-type)
			   (bt:slot-offset 'movitz::movitz-basic-vector 'movitz::type))))
	   (let ((type-code (dpb (bt:enum-value 'movitz::movitz-vector-element-type element-type)
				 (byte 8 8)
				 (movitz:tag :basic-vector))))
	     `(with-inline-assembly-case ()
		(do-case (:boolean-branch-on-false)
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:branch-when :boolean-zf=0)
		  (:cmpw ,type-code (:eax ,movitz:+other-type-offset+))
		  (:branch-when :boolean-zf=0))
		(do-case (:boolean-branch-on-true :same :labels (vector-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-failed)
		  (:cmpw ,type-code (:eax ,movitz:+other-type-offset+))
		  (:branch-when :boolean-zf=1)
		 vector-typep-failed)
		(do-case (t :boolean-zf=1 :labels (vector-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-failed)
		  (:cmpw ,type-code (:eax ,movitz:+other-type-offset+))
		 vector-typep-failed))))
	 (make-vector-typep (element-type)
	   (assert (= 1 (- (bt:slot-offset 'movitz::movitz-basic-vector 'movitz::element-type)
			   (bt:slot-offset 'movitz::movitz-basic-vector 'movitz::type))))
	   (let ((basic-type-code
		  (dpb (bt:enum-value 'movitz::movitz-vector-element-type element-type)
		       (byte 8 8)
		       (movitz:tag :basic-vector)))
		 (indirect-type-code
		  (logior (ash (movitz:tag :basic-vector) 0)
			  (ash (bt:enum-value 'movitz::movitz-vector-element-type :indirects) 8)
			  (ash (bt:enum-value 'movitz::movitz-vector-element-type element-type) 24))))
	     `(with-inline-assembly-case ()
		(do-case (:boolean-branch-on-false :same :labels (vector-typep-no-branch))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:branch-when :boolean-zf=0)
		  (:movl (:eax ,movitz:+other-type-offset+) :ecx)
		  (:cmpw ,basic-type-code :cx)
		  (:je 'vector-typep-no-branch)
		  (:cmpl ,indirect-type-code :ecx)
		  (:branch-when :boolean-zf=0)
		 vector-typep-no-branch)
		(do-case (:boolean-branch-on-true :same :labels (vector-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-failed)
		  (:movl (:eax ,movitz:+other-type-offset+) :ecx)
		  (:cmpw ,basic-type-code :cx)
		  (:branch-when :boolean-zf=1)
		  (:cmpl ,indirect-type-code :ecx)
		  (:branch-when :boolean-zf=1)
		 vector-typep-failed)
		(do-case (t :boolean-zf=1 :labels (vector-typep-done))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-done)
		  (:movl (:eax ,movitz:+other-type-offset+) :ecx)
		  (:cmpw ,basic-type-code :cx)
		  (:je 'vector-typep-done)
		  (:cmpl ,indirect-type-code :ecx)
		 vector-typep-done))))
	 (make-function-typep (funobj-type)
	   (assert (= 1 (- (bt:slot-offset 'movitz::movitz-funobj 'movitz::funobj-type)
			   (bt:slot-offset 'movitz::movitz-funobj 'movitz::type))))
	   (let ((type-code (dpb (bt:enum-value 'movitz::movitz-funobj-type funobj-type)
				 (byte 8 8)
				 (movitz:tag :funobj))))
	     `(with-inline-assembly-case ()
		(do-case (:boolean-branch-on-false)
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:branch-when :boolean-zf=0)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::type)))
		  (:branch-when :boolean-zf=0))
		(do-case (:boolean-branch-on-true :same :labels (function-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jne 'function-typep-failed)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::type)))
		  (:branch-when :boolean-zf=1)
		 function-typep-failed)
		(do-case (t :boolean-zf=1 :labels (function-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jne 'function-typep-failed)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::type)))
		 function-typep-failed)))))
    (if (not (movitz:movitz-constantp type-specifier env))
	form
      (let ((type (movitz::translate-program (movitz::eval-form type-specifier env)
					     :muerte.cl :cl)))
	(or (cond
	     ((symbolp type)
	      (case type
		((t) 't)
		((nil) 'nil)
		(null `(not ,object))
		((fixnum)
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:testb ,movitz::+movitz-fixnum-zmask+ :al)))
		((bignum)
		 (make-other-typep :bignum))
		((positive-bignum)
		 (make-other-typep :bignum 0))
		((negative-bignum)
		 (make-other-typep :bignum #xff))
		((ratio)
		 (make-other-typep :ratio))
		((integer)
		 `(with-inline-assembly-case ()
		    (do-case (t :boolean-zf=1 :labels (done))
		      (:compile-form (:result-mode :eax) ,object)
		      (:testb ,movitz:+movitz-fixnum-zmask+ :al)
		      (:jz 'done)
		      (:leal (:eax ,(- (movitz:tag :other))) :ecx)
		      (:testb 7 :cl)
		      (:jnz 'done)
		      (:cmpb ,(movitz:tag :bignum)
			     (:eax ,movitz:+other-type-offset+))
		     done)))
		(symbol
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:leal (:eax -5) :ecx)
		    (:testb 5 :cl)))	; tags 5 (000) and 7 (010) are symbols.
		(symbol-not-nil
		 (make-tag-typep :symbol))
		(cons (make-tag-typep :cons))
		(tag0 (make-tag-typep :tag0))
		(tag1 (make-tag-typep :tag1))
		(tag2 (make-tag-typep :tag2))
		(tag3 (make-tag-typep :tag3))
		(tag4 (make-tag-typep :tag4))
		(tag5 (make-tag-typep :tag5))
		(tag6 (make-tag-typep :tag6))
		(tag7 (make-tag-typep :tag7))
		(basic-restart (make-tag-typep :basic-restart))
		(pointer
		 (assert (equal (mapcar 'movitz::tag '(:cons :other :symbol))
				'(1 6 7)))
		 `(with-inline-assembly-case ()
		    (do-case (t :boolean-zf=0 :labels (done))
		      (:compile-form (:result-mode :eax) ,object)
		      (:testb ,movitz::+movitz-fixnum-zmask+ :al)
		      (:jz 'done)
		      (:leal (:eax 6) :ecx) ; => cons:7, other:4, symbol:5, fixnum:6
		      (:testb #b100 :cl)
		     done)))
		(std-instance 
		 (make-other-typep :std-instance)
		 #+ignore (make-tag-typep :std-instance))
		(macro-function
		 (make-function-typep :macro-function))
		(standard-gf-instance
		 (make-function-typep :generic-function))
		(list
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:leal (:eax -1) :ecx)
		    (:testb 3 :cl)))	; tags 1 (cons, 001) and 5 (null, 101) are lists.
		(atom
		 `(with-inline-assembly (:returns :boolean-zf=0)
		    (:compile-form (:result-mode :eax) ,object)
		    (:leal (:eax -1) :ecx)
		    (:testb 7 :cl)))	; tag 1 is not atom.
		(character
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:cmpb ,(movitz:tag :character) :al)))
		((function compiled-function)
		 (make-other-typep :funobj))
		((vector)
		 (make-other-typep :basic-vector))
		(stack-vector
		 (make-basic-vector-typep :stack))
		(indirect-vector
		 (make-basic-vector-typep :indirects))
		(simple-vector
		 (make-basic-vector-typep :any-t))
		(simple-string
		 (make-basic-vector-typep :character))
		(string
		 (make-vector-typep :character))
		(simple-bit-vector
		 (make-basic-vector-typep :bit))
		(bit-vector
		 (make-vector-typep :bit))
		(code-vector
		 (make-basic-vector-typep :code))
		(unbound-value
		 `(with-inline-assembly (:returns :boolean-overflow)
		    (:compile-form (:result-mode :eax) ,object)
		    (:cmpl -1 :eax)))
		(run-time-context
		 (make-other-typep :run-time-context))
		(structure-object
		 (make-other-typep :defstruct))
		(t (let ((deriver-function (gethash type *compiler-derived-typespecs*)))
		     (when deriver-function
		       `(typep ,object ',(funcall deriver-function)))))))
	     ((consp type)
	      (let ((deriver-function (gethash (translate-program (car type) :cl :muerte.cl)
					       *compiler-derived-typespecs*)))
		(if deriver-function
		    `(typep ,object ',(apply deriver-function (cdr type)))
		  (case (car type)
		    ((simple-array array)
		     (let ((et (second type))
			   (dim (if (listp (third type))
				    (length (third type))
				  (or (third type) '*))))
		       (if (not (eql dim 1))
			   form
			 (cond
			  ((eq et '*)
			   (make-other-typep :basic-vector))
			  ((movitz:movitz-subtypep et '(unsigned-byte 8))
			   (make-basic-vector-typep :u8))
			  ((movitz:movitz-subtypep et '(unsigned-byte 16))
			   (make-basic-vector-typep :u16))
			  ((movitz:movitz-subtypep et '(unsigned-byte 32))
			   (make-basic-vector-typep :u32))
			  ((movitz:movitz-subtypep et 'character)
			   (make-basic-vector-typep :character))
			  (t (make-basic-vector-typep :any-t))))))
		    ((integer)
		     (destructuring-bind (&optional (lower-limit '*) (upper-limit '*))
			 (cdr type)
		       (let* ((lower-limit (if (eq lower-limit '*) nil lower-limit))
			      (upper-limit (if (eq upper-limit '*) nil upper-limit)))
			 (assert (or (null lower-limit)
				     (null upper-limit)
				     (<= lower-limit upper-limit)) ()
			   "The lower limit must be smaller than the upper limit.")
			 ;; (warn "upper: ~S, loweR: ~S" upper-limit lower-limit)
			 (cond
			  ((and (null lower-limit) (null upper-limit))
			   `(typep ,object 'integer))
			  ((null lower-limit)
			   `(let ((x ,object))
			      (and (typep x 'integer) (<= x ,upper-limit))))
			  ((and (null upper-limit)
				(= (1+ movitz:+movitz-most-positive-fixnum+) lower-limit))
			   `(with-inline-assembly-case ()
			      (do-case (t :boolean-zf=1 :labels (plusp-ok))
			(:compile-form (:result-mode :eax) ,object)
				(:leal (:eax ,(- (movitz:tag :other))) :ecx)
				(:testb 7 :cl)
				(:jnz 'plusp-ok)
				(:cmpw ,(movitz:tag :bignum 0)
				       (:eax ,movitz:+other-type-offset+))
			       plusp-ok)))
			  ((and (null upper-limit) (= 0 lower-limit))
			   `(with-inline-assembly-case ()
			      (do-case (t :boolean-zf=1 :labels (plusp-ok))
				(:compile-form (:result-mode :eax) ,object)
				(:testl ,(logxor #xffffffff
						 (ash movitz:+movitz-most-positive-fixnum+
						      movitz:+movitz-fixnum-shift+))
					:eax)
				(:jz 'plusp-ok)
				(:leal (:eax ,(- (movitz:tag :other))) :ecx)
				(:testb 7 :cl)
				(:jnz 'plusp-ok)
				(:cmpw ,(movitz:tag :bignum 0)
				       (:eax ,movitz:+other-type-offset+))
			       plusp-ok)))
			  ((null upper-limit)
			   `(let ((x ,object))
			      (and (typep x 'integer) (>= x ,lower-limit))))
			  ((= lower-limit upper-limit)
			   `(eql ,object ,lower-limit))
			  ((or (not (<= movitz:+movitz-most-negative-fixnum+
					upper-limit
					movitz:+movitz-most-positive-fixnum+))
			       (not (<= movitz:+movitz-most-negative-fixnum+
					lower-limit
					movitz:+movitz-most-positive-fixnum+)))
			   `(let ((x ,object))
			      (and (typep x 'integer)
				   (<= ,lower-limit x ,upper-limit))))
			  ((and (= lower-limit 0)
				(= 1 (logcount (1+ upper-limit))))
			   `(with-inline-assembly (:returns :boolean-zf=1)
			      (:compile-form (:result-mode :eax) ,object)
			      (:testl ,(logxor #xffffffff
					       (* movitz:+movitz-fixnum-factor+ upper-limit))
				      :eax)))
			  ((= 1 (logcount (1+ (- upper-limit lower-limit))))
			   `(with-inline-assembly (:returns :boolean-zf=1)
			      (:compile-form (:result-mode :ecx) ,object)
			      (:subl ,(* movitz:+movitz-fixnum-factor+ lower-limit)
				     :ecx)
			      (:testl ,(logxor #xffffffff
					       (* movitz:+movitz-fixnum-factor+
						  (- upper-limit lower-limit)))
				      :ecx)))
			  ((= lower-limit 0)
			   `(with-inline-assembly-case ()
			      (do-case (t :boolean-cf=1 :labels (not-fixnum))
				(:compile-form (:result-mode :eax) ,object)
				(:testb ,movitz:+movitz-fixnum-zmask+ :al) ; CF<=0
				(:jnz 'not-fixnum)
				(:cmpl ,(* (1+ upper-limit) movitz:+movitz-fixnum-factor+)
				       :eax)
			       not-fixnum)))
			  (t `(with-inline-assembly-case ()
				(do-case (t :boolean-cf=1 :labels (not-fixnum))
				  (:compile-form (:result-mode :eax) ,object)
				  (:testb ,movitz:+movitz-fixnum-zmask+ :al) ; CF<=0
				  (:jnz 'not-fixnum)
				  (:subl ,(* lower-limit movitz:+movitz-fixnum-factor+) :eax)
				  (:cmpl ,(* (- upper-limit lower-limit -1)
					     movitz:+movitz-fixnum-factor+)
					 :eax)
				 not-fixnum)))))))
		    ((eql)
		     `(eql ,object ',(cadr type)))
		    ((satisfies)
		     (destructuring-bind (predicate-name)
			 (cdr type)
		       (check-type predicate-name symbol "a satisfies predicate-name")
		       `(,predicate-name ,object)))
		    ((cons)
		     (destructuring-bind (&optional (car t) (cdr t))
			 (cdr type)
		       (let ((car (if (eq car '*) t car))
			     (cdr (if (eq cdr '*) t cdr)))
			 `(let ((typep-object ,object))
			    (and (typep typep-object 'cons)
				 (typep (car typep-object) ',car)
				 (typep (cdr typep-object) ',cdr))))))
		    ((not)
		     (assert (and (cadr type) (not (cddr type))))
		     `(not (typep ,object ',(cadr type))))
		    ((or and)
		     `(let ((typep-object ,object))
			(,(car type)
			 ,@(loop for subtype in (cdr type)
			       collect `(typep typep-object ',subtype)))))
		    (t (warn "compiling typep ~S [~A]" type
			     (package-name (symbol-package (car type))))))))))
	    form)))))

(defmacro define-typep (tname lambda &body body)
  (let ((fname (with-standard-io-syntax
		 (format nil "~A-~A" 'typep tname))))
    `(progn
       (eval-when (:compile-toplevel)
	 (setf (gethash (intern ,(symbol-name tname))
			*compound-typespecs*)
	   (intern ,fname)))
       (defun ,(intern fname) ,lambda ,@body))))

(defmacro define-simple-typep ((tname fname) &optional lambda &body body)
  `(progn
     (eval-when (:compile-toplevel)
       (setf (gethash (intern ,(symbol-name tname))
		      *simple-typespecs*)
	 (intern ,(symbol-name fname))))
     ,@(when body
	 `((define-compiler-macro ,fname (x)
	     (list 'typep x '',tname))
	   (defun ,fname ,lambda ,@body)))))

(defmacro deftype (&whole form name lambda &body body)
  (let ((fname (intern (with-standard-io-syntax
			 (format nil "~A-~A" 'deftype name)))))
    `(progn
       (eval-when (:compile-toplevel)
	 (unless (find-symbol (symbol-name (cadr ',form)) :common-lisp)
	   #+ignore (eq (symbol-package (cadr ',form)) (find-package :common-lisp))
	   (eval ',form))
	 (setf (gethash (translate-program ',name :cl :muerte.cl)
			*compiler-derived-typespecs*)
	   (lambda ,lambda ,@body))
	 (setf (gethash (intern ,(symbol-name name))
			*derived-typespecs*)
	   ',fname))
       (defun ,fname ,lambda ,@body))))

(defun expand-type (type-specifier)
  (typecase type-specifier
    (symbol
     (let ((typep-function (gethash type-specifier *derived-typespecs*)))
       (when typep-function
	 (funcall typep-function))))
    (cons
     (let ((typep-function (gethash (car type-specifier) *derived-typespecs*)))
       (when typep-function
	 (apply typep-function (cdr type-specifier)))))))

(defun typep (object type-specifier)
  (block nil
    (typecase type-specifier
      (symbol
       (let ((typep-function (gethash type-specifier *simple-typespecs*)))
	 (when typep-function
	   (return (funcall typep-function object))))
       (let ((typep-function (gethash type-specifier *derived-typespecs*)))
	 (when typep-function
	   (return (typep object (funcall typep-function)))))
       (let ((class (find-class type-specifier nil)))
	 (when class
	   (return (and (member class (class-precedence-list  (class-of object)))
			t)))))
      (cons
       (let ((typep-function (gethash (car type-specifier) *compound-typespecs*)))
	 (when typep-function
	   (return (apply typep-function object (cdr type-specifier)))))
       (let ((typep-function (gethash (car type-specifier) *derived-typespecs*)))
	 (when typep-function
	   (return (typep object (apply typep-function (cdr type-specifier)))))))
      (std-instance
       (when (member (find-class 'class) (class-precedence-list (class-of type-specifier)))
	 (return (and (member type-specifier (class-precedence-list (class-of object)))
		      t)))))
    (error "~S is not a type specifier." type-specifier)))


(define-simple-typep (nil false) (x)
  "The empty type."
  (declare (ignore x))
  nil)

(define-simple-typep (t true) (x)
  "The full type."
  (declare (ignore x))
  t)

(define-simple-typep (symbol symbolp) (obj)
  (typep obj 'symbol))

(define-compiler-macro symbolp (obj)
  `(typep ,obj 'symbol))

(define-simple-typep (keyword keywordp) (obj)
  (and (symbolp obj)
       (eq (symbol-package obj)
	   (find-package 'keyword))))

(define-simple-typep (list listp) (obj)
  (typep obj 'list))

(define-simple-typep (cons consp) (obj)
  (typep obj 'cons))

(define-simple-typep (vector vectorp) (obj)
  (typep obj 'vector))

(define-simple-typep (simple-vector simple-vector-p) (obj)
  (typep obj 'simple-vector))

(define-simple-typep (simple-string simple-string-p) (obj)
  (typep obj 'simple-string))

(define-simple-typep (simple-bit-vector simple-bit-vector-p) (obj)
  (typep obj 'simple-bit-vector))

(define-simple-typep (pointer pointerp) (obj)
  (typep obj 'pointer))

(define-typep cons (x &optional (car '*) (cdr '*))
  (and (typep x 'cons)
       (or (eq '* car) (typep (car x) car))
       (or (eq '* cdr) (typep (cdr x) cdr))))

(deftype vector (&optional (element-type '*) (size '*))
  (if (eq size '*)
      `(array ,element-type 1)
    `(array ,element-type (,size))))

(define-typep array (x &optional (element-type '*) (dimension-spec '*))
  (and (typep x 'array)
       (or (eq element-type '*)
	   (do ((xet (array-element-type x))
		(aet element-type (expand-type aet)))
	       ((eq nil aet) nil)
	     (when (equal xet aet) (return t))))
       (or (eq dimension-spec '*)
	   (if (typep dimension-spec 'integer)
	       (eql dimension-spec (array-rank x))
	     (and (eql (length dimension-spec) (array-rank x))
		  (every (lambda (xdim adim)
			   (or (eq xdim '*) (eql xdim adim)))
			 dimension-spec
			 (array-dimensions x)))))))
(defun bit-vector-p (x)
  (typep x 'bit-vector))

(defun arrayp (x)
  (typep x 'array))      

(define-simple-typep (atom atom) (x)
  (typep x 'atom))

(define-compiler-macro atom (obj)
  `(typep ,obj 'atom))

(define-simple-typep (integer integerp) (x)
  (typep x 'integer))

;; Additional number types in integer.lisp.

(define-simple-typep (null null) (x)
  (typep x 'null))

(define-simple-typep (tag3 tag3p) (obj)
  (typep obj 'tag3))

(define-simple-typep (tag5 tag5p) (obj)
  (typep obj 'tag5))

(define-simple-typep (tag6 tag6p) (obj)
  (typep obj 'tag6))

(define-simple-typep (string stringp) (x)
  (typep x 'string))

(define-typep string (x &optional (size '*))
  (and (typep x 'string)
       (or (eq size '*)
	   (eq size (length x)))))

(define-simple-typep (character characterp) (x)
  (typep x 'character))

(define-simple-typep (fixnum fixnump) (x)
  (typep x 'fixnum))

(define-simple-typep (bignum bignump) (x)
  (typep x 'bignum))

(define-simple-typep (rational rationalp) (x)
  (typep x '(or fixnum bignum ratio)))

(define-simple-typep (number numberp) (x)
  (typep x 'rational))

(define-simple-typep (function functionp) (x)
  (typep x 'function))

(define-simple-typep (compiled-function compiled-function-p) (x)
  (typep x 'compiled-function))

(define-simple-typep (macro-function macro-function-p) (x)
  (typep x 'macro-function))

(define-simple-typep (hash-table hash-table-p))
(define-simple-typep (package packagep))

(define-simple-typep (code-vector code-vector-p) (x)
  (typep x 'code-vector))

;;;

(define-typep and (x &rest types)
  (declare (dynamic-extent types))
  (dolist (type types t)
    (unless (typep x type)
      (return nil))))

(define-typep or (x &rest types)
  (declare (dynamic-extent types))
  (dolist (type types nil)
    (when (typep x type)
      (return t))))

(define-typep member (x &rest members)
  (declare (dynamic-extent members))
  (dolist (member members nil)
    (when (eql x member)
      (return t))))

(define-typep satisfies (x predicate)
  (check-type predicate symbol "a function name.")
  (funcall predicate x))

(define-typep eql (x y)
  (eql x y))

(define-simple-typep (boolean booleanp) (x)
  (or (eq x t) (eq x nil)))

(define-typep not (x type)
  (not (typep x type)))

(deftype boolean ()
  '(member nil t))

(deftype bit ()
  '(integer 0 1))

(deftype float ()
  'real)

(deftype short-float ()
  'real)

(deftype long-float ()
  'real)

(deftype single-float ()
  'real)

(deftype double-float ()
  'real)

(defun type-of (x)
  (class-name (class-of x)))

(defun coerce (object result-type)
  "=> result"
  (labels
      ((c (object result-type actual-type)
	 (cond
	  ((typep object result-type)
	   object)
	  ((member result-type '(list array vector simple-vector string simple-string))
	   (map result-type #'identity object))
	  ((and (consp result-type)
		(eq (car result-type) 'vector))
	   (let* ((p (cdr result-type))
		  (et (if p (pop p) t))
		  (size (if p (pop p) nil)))
	     (make-array (or size (length object))
			 :initial-contents object
			 :element-type et)))
	  ((not (eq nil result-type))
	   (c object (expand-type result-type) actual-type))
	  (t (error "Don't know how to coerce ~S to ~S." object actual-type)))))
    (c object result-type result-type)))

