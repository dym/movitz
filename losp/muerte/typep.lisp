;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromsø, Norway
;;;; 
;;;; Filename:      typep.lisp
;;;; Description:   Implements TYPEP and TYPECASE.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Dec  8 11:07:53 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: typep.lisp,v 1.1 2004/01/13 11:05:06 ffjeld Exp $
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
  `(typecase ,keyform ,@clauses
	     (t (error "~S fell through an etypecase where the legal types were ~S."
		       ,keyform
		       ',(loop for c in clauses
			     if (listp (car c))
			     append (car c)
			     else collect (car c))))))

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
	 (make-other-typep (tag-name)
	   `(with-inline-assembly-case ()
	      (do-case (:boolean-branch-on-false)
		(:compile-form (:result-mode :eax) ,object)
		(:leal (:eax ,(cl:- (movitz:tag :other))) :ecx)
		(:testb 7 :cl)
		(:branch-when :boolean-zf=0)
		(:cmpb ,(movitz:tag tag-name)
		       (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		(:branch-when :boolean-zf=0))
	      (do-case (:boolean-branch-on-true :same :labels (other-typep-failed))
		(:compile-form (:result-mode :eax) ,object)
		(:leal (:eax ,(cl:- (movitz:tag :other))) :ecx)
		(:testb 7 :cl)
		(:jnz 'other-typep-failed)
		(:cmpb ,(movitz:tag tag-name)
		       (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		(:branch-when :boolean-zf=1)
		other-typep-failed)
	      (do-case (t :boolean-zf=1 :labels (other-typep-failed))
		(:compile-form (:result-mode :eax) ,object)
		(:leal (:eax ,(cl:- (movitz:tag :other))) :ecx)
		(:testb 7 :cl)
		(:jnz 'other-typep-failed)
		(:cmpb ,(movitz:tag tag-name)
		       (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		other-typep-failed)))
	 (make-vector-typep (element-type)
	   (assert (= 1 (- (bt:slot-offset 'movitz::movitz-vector 'movitz::element-type)
			   (bt:slot-offset 'movitz::movitz-vector 'movitz::type))))
	   (let ((type-code (dpb (bt:enum-value 'movitz::movitz-vector-element-type element-type)
				 (byte 8 8)
				 (movitz:tag :vector))))
	     `(with-inline-assembly-case ()
		(do-case (:boolean-branch-on-false)
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:branch-when :boolean-zf=0)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		  (:branch-when :boolean-zf=0))
		(do-case (:boolean-branch-on-true :same :labels (vector-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-failed)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		  (:branch-when :boolean-zf=1)
		  vector-typep-failed)
		(do-case (t :boolean-zf=1 :labels (vector-typep-failed))
		  (:compile-form (:result-mode :eax) ,object)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz 'vector-typep-failed)
		  (:cmpw ,type-code
			 (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		  vector-typep-failed))))
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
		((fixnum integer number)
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:testb ,movitz::+movitz-fixnum-zmask+ :al)))
		(symbol
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:leal (:eax -5) :ecx)
		    (:testb 5 :cl)))	; tags 5 (000) and 7 (010) are symbols.
		(symbol-not-nil
		 (make-tag-typep :symbol))
		(cons (make-tag-typep :cons))
		(tag2 (make-tag-typep :tag2))
		(tag3 (make-tag-typep :tag3))
		(tag4 (make-tag-typep :tag4))
		(tag5 (make-tag-typep :null))
		(tag6 (make-tag-typep :other))
		(std-instance 
		 (make-other-typep :std-instance)
		 #+ignore (make-tag-typep :std-instance))
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
		    (:testb 7 :cl))) ; tag 1 is not atom.
		(character
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,object)
		    (:cmpb ,(movitz::tag :character) :al)))
		((function compiled-function)
		 (make-other-typep :funobj))
		((vector array)
		 (make-other-typep :vector))
		(simple-vector
		 (make-vector-typep :any-t))
		(string
		 (make-vector-typep :character))
		(vector-u8
		 (make-vector-typep :u8))
		(vector-u16
		 (make-vector-typep :u16))
		(run-time-context
		 (make-other-typep :run-time-context))
		(structure-object
		 (make-other-typep :defstruct))
		(t (let ((deriver-function (gethash type *compiler-derived-typespecs*)))
		     (when deriver-function
		       `(typep ,object ',(funcall deriver-function)))))))
	     ((consp type)
	      (case (car type)
		((not)
		 (assert (and (cadr type) (not (cddr type))))
		 `(not (typep ,object ',(cadr type))))
		((or and)
		 `(let ((typep-object ,object))
		    (,(car type)
		     ,@(loop for subtype in (cdr type)
			   collect `(typep ,object ',subtype)))))
		((not and or)
		 (warn "typep compilermacro: ~S" type)))))
	    form)))))

(defmacro define-typep (tname lambda &body body)
  (let ((fname (format nil "~A-~A" 'typep tname)))
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

(defmacro deftype (name lambda &body body)
  (let ((fname (intern (format nil "~A-~A" 'deftype name))))
    `(progn
       (eval-when (:compile-toplevel)
	 (setf (gethash ',name *compiler-derived-typespecs*)
	   (lambda ,lambda ,@body))
	 (setf (gethash (intern ,(symbol-name name))
			*derived-typespecs*)
	   ',fname))
       (defun ,fname ,lambda ,@body))))

(defun typep (object type-specifier)
  (block nil
    (etypecase type-specifier
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

(define-typep cons (x &optional (car '*) (cdr '*))
  (and (typep x 'cons)
       (or (eq '* car) (typep (car x) car))
       (or (eq '* cdr) (typep (cdr x) cdr))))

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
  (declare (ignore x))
  nil)

(define-simple-typep (number numberp) (x)
  "Currently, only integer numbers are supported."
  (integerp x))

(define-simple-typep (function functionp) (x)
  (typep x 'function))

(define-simple-typep (hash-table hash-table-p))
(define-simple-typep (package packagep))

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

(defun type-of (x)
  (class-name (class-of x)))
;;;  (typecase x
;;;    (null 'null)
;;;    (cons 'cons)
;;;    (symbol 'symbol)
;;;    (integer 'integer)
;;;    (structure-object
;;;     (structure-object-name x))
;;;    (t t)))



;;;(defun subtypep (type-1 type-2)
;;;  (cond
;;;   ((eq type-1 type-2)
;;;    t)
;;;   ((or (atom type-1) (atom type-2))
;;;    nil)
;;;   ((equal type-1 type-2)
;;;    t)
;;;   (t (case (car type-2)
;;;	(integer
;;;	 (let ((low2 (second type-2))
;;;	       (hi2 (third type-2)))
;;;	   (case (car type-1)
	     
