;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      arrays.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Feb 11 23:14:04 2001
;;;;                
;;;; $Id: arrays.lisp,v 1.30 2004/07/07 17:37:15 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(require :muerte/memref)
(provide :muerte/arrays)

(in-package muerte)

(defun vector-element-type (object)
  (memref object #.(bt:slot-offset 'movitz::movitz-vector 'movitz::element-type) 0
	  :unsigned-byte8))

(defmacro vector-double-dispatch ((s1 s2) &rest clauses)
  (flet ((make-double-dispatch-value (et1 et2)
	   (+ (* #x100 (bt:enum-value 'movitz::movitz-vector-element-type et1))
	      (bt:enum-value 'movitz::movitz-vector-element-type et2))))
    `(progn
       #+ignore
       (warn "vdd: ~X" (+ (* #x100 (vector-element-type ,s1))
	      (vector-element-type ,s2)))
       (case (+ (ash (vector-element-type ,s1) 8)
		(vector-element-type ,s2))
	 ,@(loop for (keys . forms) in clauses
	       if (atom keys)
	       collect (cons keys forms)
	       else
	       collect (cons (make-double-dispatch-value (first keys) (second keys))
			     forms))))))

(define-compiler-macro vector-element-type (object)
  `(memref ,object 0
	   #.(bt:slot-offset 'movitz::movitz-vector 'movitz::element-type)
	   :unsigned-byte8))

(defun (setf vector-element-type) (numeric-element-type vector)
  (check-type vector vector)
  (setf (memref vector #.(bt:slot-offset 'movitz::movitz-vector 'movitz::element-type) 0
		:unsigned-byte8)
    numeric-element-type))

(defun array-element-type (array)
  (ecase (vector-element-type array)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :any-t)
       t)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :character)
       'character)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u8)
       'muerte::u8)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u16)
       '(unsigned-byte 16))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u32)
       '(unsigned-byte 32))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :code)
       'code)))

;;;(defmacro vector-dimension (vector)
;;;  `(movitz-accessor-u16 ,vector movitz-vector num-elements))

(defun array-dimension (array axis-number)
  (etypecase array
    (basic-vector
     (assert (zerop axis-number))
     (movitz-accessor array movitz-basic-vector num-elements))
    #+ignore
    (vector
     (assert (zerop axis-number))
     (vector-dimension array))))

(defun shrink-vector (vector new-size)
  (set-movitz-accessor-u16 vector movitz-vector num-elements new-size)
  vector)


;;;(define-compiler-macro vector-fill-pointer (vector)
;;;  `(movitz-accessor-u16 ,vector movitz-vector fill-pointer)
;;;  #+ignore `(with-inline-assembly (:returns :untagged-fixnum-ecx)
;;;	      (:compile-form (:result-mode :eax) ,vector)
;;;	      (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-vector 'movitz::fill-pointer))
;;;		       :ecx)))
;;;
;;;(defun vector-fill-pointer (vector)
;;;  (vector-fill-pointer vector))

(define-compiler-macro %basic-vector-has-fill-pointer-p (vector)
  "Does the basic-vector have a fill-pointer?"
  `(with-inline-assembly (:returns :boolean-zf=1)
     (:compile-form (:result-mode :eax) ,vector)
     (:testl ,(logxor #xffffffff (1- (expt 2 14)))
	     (:eax ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)))))

(define-compiler-macro %basic-vector-fill-pointer (vector)
  "Return the basic-vector's fill-pointer. The result is only valid if
%basic-vector-has-fill-pointer-p is true."
  `(with-inline-assembly (:returns :register)
     (:compile-form (:result-mode :register) ,vector)
     (:movzxw ((:result-register)
	       ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::fill-pointer))
	      (:result-register))))

(defun array-has-fill-pointer-p (array)
  (etypecase array
    (basic-vector
     (%basic-vector-has-fill-pointer-p array))
    (vector t)
    (array nil)))
  
(defun fill-pointer (vector)
  (etypecase vector
    (basic-vector
     (assert (%basic-vector-has-fill-pointer-p vector) (vector)
       "Vector has no fill-pointer.")
     (%basic-vector-fill-pointer vector))))


(defun (setf fill-pointer) (new-fill-pointer vector)
  (etypecase vector
    (basic-vector
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	       (:compile-two-forms (:eax :ebx) new-fill-pointer vector)
	       (:testb ,movitz:+movitz-fixnum-zmask+ :al)
	       (:jnz 'illegal-fill-pointer)
	       (:movl (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		      :ecx)
	       (:testl ,(logxor #xffffffff (1- (expt 2 14))) :ecx)
	       (:jnz '(:sub-program ()
		       (:compile-form (:result-mode :ignore)
			(error "Vector has no fill-pointer."))))
	       (:cmpl :eax :ecx)
	       (:jc '(:sub-program (illegal-fill-pointer)
		       (:compile-form (:result-mode :ignore)
			(error "Illegal fill-pointer: ~W." new-fill-pointer))))
	       (:movw :ax (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::fill-pointer))))))
       (do-it)))
    #+ignore
    (vector
     (assert (<= new-fill-pointer (vector-dimension vector)))
     (setf (memref vector #.(bt:slot-offset 'movitz::movitz-vector 'movitz::fill-pointer) 0
		   :unsigned-byte16)
       new-fill-pointer))))

(defun vector-aref%unsafe (vector index)
  "No type-checking of <vector> or <index>."
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) vector)
    (:compile-form (:result-mode :ebx) index)
    (:movzxb (:eax -1) :ecx)
    (:testl :ecx :ecx)			; element-type 0?
    (:jnz 'not-any-t)
    #.(cl:if (cl:plusp (cl:- movitz::+movitz-fixnum-shift+ 2))
	  `(:sarl ,(cl:- movitz::+movitz-fixnum-shift+ 2) :ebx)
	:nop)
    (:movl (:eax :ebx 2) :eax)
    (:jmp 'done)

    not-any-t
    (:shrl #.movitz::+movitz-fixnum-shift+ :ebx)
    (:decl :ecx)			; element-type 1?
    (:jnz 'not-character)
    (:movb (:eax :ebx 2) :bl)
    (:xorl :eax :eax)
    (:movb :bl :ah)
    (:movb #.(movitz::tag :character) :al)
    (:jmp 'done)
    
    not-character
    (:decl :ecx)
    (:jnz '(:sub-program (not-u8) (:int 62) (:jmp (:pc+ -4))))
    (:movzxb (:eax :ebx 2) :eax)
    (:shll #.movitz::+movitz-fixnum-shift+ :eax)
    
    done))

(defun (setf vector-aref%unsafe) (value vector index)
  (with-inline-assembly (:returns :ebx)
    (:compile-form (:result-mode :ebx) value)
    (:compile-form (:result-mode :eax) vector)
    (:compile-form (:result-mode :ecx) index)

    (:movzxb (:eax -1) :edx)
    (:testl :edx :edx)			; element-type 0?
    (:jnz 'not-any-t)

    #.(cl:if (cl:plusp (cl:- movitz::+movitz-fixnum-shift+ 2))
	  `(:sarl ,(cl:- movitz::+movitz-fixnum-shift+ 2) :ebx)
	:nop)
    
    (:movl :ebx (:eax :ecx 2))
    (:jmp 'done)

    not-any-t
    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (:decl :edx)			; element-type 1?
    (:jnz 'not-character)
    (:movb :bh (:eax :ecx 2))
    (:jmp 'done)
    
    not-character
    (:decl :edx)
    (:jnz '(:sub-program (not-u8) (:int 62) (:jmp (:pc+ -4))))
    (:shll #.(cl:- 8 movitz::+movitz-fixnum-shift+) :ebx)
    (:movb :bh (:eax :ecx 2))
    (:shrl #.(cl:- 8 movitz::+movitz-fixnum-shift+) :ebx)

    done))


(defun aref (array &rest subscripts)
  (numargs-case
   (2 (array index)
      (etypecase array
	(basic-vector
	 (macrolet
	     ((do-it ()
		`(with-inline-assembly (:returns :eax)
		   (:declare-label-set basic-vector-dispatcher
				       (any-t character u8 unknown u32 unknown code unknown))
		   (:compile-two-forms (:eax :ebx) array index)
		   (:movl (:eax ,movitz:+other-type-offset+) :ecx)
		   (:cmpb ,(movitz:tag :basic-vector) :cl)
		   (:jne '(:sub-program (not-vector)
			   (:compile-form (:result-mode :ignore)
			    (error "Not an array: ~S." array))))
		   (:testb ,movitz:+movitz-fixnum-zmask+ :bl)
		   (:jnz '(:sub-program (illegal-index)
			   (:compile-form (:result-mode :ignore)
			    (error "Illegal index: ~S." index))))
		   (:shrl 8 :ecx)
		   (:andl 7 :ecx)
		   (:cmpl :ebx
			  (:eax ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)))
		   (:jbe '(:sub-program (out-of-bounds)
			   (:compile-form (:result-mode :ignore)
			    (error "Index ~D is beyond vector length ~D."
			     index
			     (memref array
			      ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
			      0 :lisp)))))
		   (:jmp (:esi (:ecx 4) 'basic-vector-dispatcher
			       ,(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)))
		   
		   (() () '(:sub-program (unknown) (:int 100)))
		  u32
		   (:movl (:eax :ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			  :ecx)
		   (:call-global-constant box-u32-ecx)
		   (:jmp 'return)
		  u8 code
		   (:movl :ebx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movzxb (:eax :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			    :ecx)
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
		   (:jmp 'return)
		  character
		   (:movl :ebx :ecx)
		   (:movl :eax :ebx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movl ,(movitz:tag :character) :eax)
		   (:movb (:ebx :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			  :ah)
		   (:jmp 'return)
		  any-t
		   (:movl (:eax :ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			  :eax)
		  return)))
	   (do-it)))))
   (t (vector &rest subscripts)
      (declare (ignore vector subscripts))
      (error "Multi-dimensional arrays not implemented."))))

(defun (setf aref) (value vector &rest subscripts)
  (numargs-case
   (3 (value vector index)
      (etypecase vector
	(basic-vector
	 (macrolet
	     ((do-it ()
		`(with-inline-assembly (:returns :eax)
		   (:compile-two-forms (:eax :ebx) value vector)
		   (:leal (:ebx ,(- (movitz:tag :other))) :ecx)
		   (:compile-form (:result-mode :edx) index)
		   (:testb 7 :cl)
		   (:jnz '(:sub-program (not-a-vector)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a vector: ~S" vector))))
		   (:movl (:ebx ,movitz:+other-type-offset+) :ecx)
		   (:andl #xffff :ecx)
		   (:testb ,movitz:+movitz-fixnum-zmask+ :dl)
		   (:jnz '(:sub-program (not-an-index)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a vector index: ~S" index))))
		   ;; t?
		   (:cmpl ,(movitz:basic-vector-type-tag :any-t) :ecx)
		   (:jne 'not-any-t-vector)
		   (:movl :eax
			  (:ebx :edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)

		  not-any-t-vector
		   ;; Character?
		   (:cmpl ,(movitz:basic-vector-type-tag :character) :ecx)
		   (:jne 'not-character-vector)
		   (:cmpb ,(movitz:tag :character) :al)
		   (:jne '(:sub-program (not-a-character)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a character: ~S" value))))
		   (:movl :edx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movb :ah (:ebx :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)

		  not-character-vector
		   ;; u8?
		   (:cmpl ,(movitz:basic-vector-type-tag :u8) :ecx)
		   (:jne 'not-u8-vector)
		   (:testl ,(logxor #xffffffff (* #xff movitz:+movitz-fixnum-factor+))
			   :eax)
		   (:jne '(:sub-program (not-an-u8)
			   (:compile-form (:result-mode :ignore)
			    (error "Not an (unsigned-byte 8): ~S" value))))
		   (:shll ,(- 8 movitz:+movitz-fixnum-shift+) :eax)
		   (:movl :edx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movb :ah (:ebx :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)

		  not-u8-vector
		   (:cmpl ,(movitz:basic-vector-type-tag :u32) :ecx)
		   (:jne 'not-u32-vector)
		   (:call-global-constant unbox-u32)
		   (:movl :eax
			  (:ebx :edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)

		  not-u32-vector
		   (:compile-form (:result-mode :ignore)
				  (error "Not a vector: ~S" vector))
		  return)
		))
	   (do-it)))))
   (t (value vector &rest subscripts)
      (declare (ignore value vector subscripts))
      (error "Multi-dimensional arrays not implemented."))))


;;; simple-vector accessors

(define-compiler-macro svref%unsafe (simple-vector index)
  `(memref ,simple-vector 2 ,index :lisp))

(define-compiler-macro (setf svref%unsafe) (value simple-vector index)
  `(setf (memref ,simple-vector 2 ,index :lisp) ,value))

(defun svref%unsafe (simple-vector index)
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) simple-vector index)
    (:movl (:eax :ebx #.(bt:slot-offset 'movitz:movitz-vector 'movitz::data)) :eax)))

(defun (setf svref%unsafe) (value simple-vector index)
  (setf (svref%unsafe simple-vector index) value))

(defun svref (simple-vector index)
  (etypecase simple-vector
    (basic-vector
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	       (:compile-two-forms (:eax :ebx) simple-vector index)
	       (:leal (:eax ,(- (movitz::tag :other))) :ecx)
	       (:testb 7 :cl)
	       (:jne '(:sub-program (not-basic-simple-vector)
		       (:compile-form (:result-mode :ignore)
			(error "Not a simple-vector: ~S." simple-vector))))
	       (:movl (:eax ,movitz:+other-type-offset+) :ecx)
	       (:testb ,movitz:+movitz-fixnum-zmask+ :bl)
	       (:jnz '(:sub-program (illegal-index)
		       (:compile-form (:result-mode :ignore)
			(error "Illegal index: ~S." index))))
	       (:cmpw ,(movitz:basic-vector-type-tag :any-t) :cx)
	       (:jne 'not-basic-simple-vector)
	       (:movl (:eax :ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
		      :eax)
	       )))
       (do-it)))))
    

(defun (setf svref) (value simple-vector index)
  (etypecase simple-vector
    (basic-vector
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	       (:compile-two-forms (:ebx :edx) simple-vector index)
	       (:leal (:ebx ,(- (movitz::tag :other))) :ecx)
	       (:testb 7 :cl)
	       (:jne '(:sub-program (not-basic-simple-vector)
		       (:compile-form (:result-mode :ignore)
			(error "Not a simple-vector: ~S." simple-vector))))
	       (:movl (:ebx ,movitz:+other-type-offset+) :ecx)
	       (:testb ,movitz:+movitz-fixnum-zmask+ :dl)
	       (:jnz '(:sub-program (illegal-index)
		       (:compile-form (:result-mode :ignore)
			(error "Illegal index: ~S." index))))
	       (:compile-form (:result-mode :eax) value)
	       (:cmpw ,(movitz:basic-vector-type-tag :any-t) :cx)
	       (:jne 'not-basic-simple-vector)
	       (:movl :eax
		      (:ebx :edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))))))
       (do-it)))))

;;; string accessors

(defun char (string index)
  (check-type string string)
  (assert (below index (array-dimension string 0)))
  (memref string 2 index :character))

(defun (setf char) (value string index)
  (assert (below index (array-dimension string 0)))
  (setf (memref string 2 index :character) value))

(defun schar (string index)
  (check-type string string)
  (assert (below index (length string)))
  (memref string 2 index :character))

(defun (setf schar) (value string index)
  (check-type string string)
  (assert (below index (length string)))
  (setf (aref string index) value))

(define-compiler-macro char%unsafe (string index)
  `(memref ,string 2 ,index :character))

(defun char%unsafe (string index)
  (char%unsafe string index))

(define-compiler-macro (setf char%unsafe) (value string index)
  `(setf (memref ,string 2 ,index :character) ,value))

(defun (setf char%unsafe) (value string index)
  (setf (char%unsafe string index) value))

;;; u8 accessors

(define-compiler-macro u8ref%unsafe (vector index)
  `(memref ,vector 2 ,index :unsigned-byte8))

(defun u8ref%unsafe (vector index)
  (u8ref%unsafe vector index))

(define-compiler-macro (setf u8ref%unsafe) (value vector index)
  `(setf (memref ,vector 2 ,index :unsigned-byte8) ,value))

(defun (setf u8ref%unsafe) (value vector index)
  (setf (u8ref%unsafe vector index) value))

;;; u32 accessors

(define-compiler-macro u32ref%unsafe (vector index)
  `(memref ,vector 2 ,index :unsigned-byte32))

(defun u32ref%unsafe (vector index)
  (u32ref%unsafe vector index))

(define-compiler-macro (setf u32ref%unsafe) (value vector index)
  `(setf (memref ,vector 2 ,index :unsigned-byte32) ,value))

(defun (setf u32ref%unsafe) (value vector index)
  (setf (u32ref%unsafe vector index) value)
  value)

;;; fast vector access

(defun subvector-accessors (vector start end)
  "Check that vector is a vector, that start and end are within vector's bounds,
and return accessors for that subsequence (fast & unsafe accessors, that is)."
  (check-type vector vector)
  (when (and start end)
    (assert (<= 0 start end))
    (assert (<= end (array-dimension vector 0))))
  (case (vector-element-type vector)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :any-t)
       (values #'svref%unsafe #'(setf svref%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :character)
       (values #'char%unsafe #'(setf char%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u8)
       (values #'u8ref%unsafe #'(setf u8ref%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u32)
       (values #'u32ref%unsafe #'(setf u32ref%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :code)
       (values #'u8ref%unsafe #'(setf u8ref%unsafe)))
    (t (warn "don't know about vector's element-type: ~S" vector)
       (values #'aref #'(setf aref)))))

(defmacro with-subvector-accessor ((name vector-form &optional start end) &body body)
  "Installs name as an accessor into vector-form, bound by start and end."
  (let ((reader (gensym "sub-vector-reader-"))
	(writer (gensym "sub-vector-writer-"))
	(vector (gensym "sub-vector-")))
    `(let ((,vector ,vector-form))
       (multiple-value-bind (,reader ,writer)
	   (subvector-accessors ,vector ,start ,end)
	 (declare (ignorable ,reader ,writer))
	 (macrolet ((,name (index)
		      `(accessor%unsafe (,',reader ,',writer) ,',vector ,index)))
	   ,@body)))))

(defmacro accessor%unsafe ((reader writer) &rest args)
  (declare (ignore writer))
  `(funcall%unsafe ,reader ,@args))

(define-setf-expander accessor%unsafe ((reader writer) &rest args)
  ;; should collect tmp-vars from args, most probably..
  (let ((store-var (gensym "accessor%unsafe-store-")))
    (values nil nil (list store-var)
	    `(funcall%unsafe ,writer ,store-var ,@args)
	    `(funcall%unsafe ,reader ,@args))))

(defun make-basic-vector%character (dimensions fill-pointer initial-element initial-contents)
  (let ((array (malloc-data-words (truncate (+ dimensions 3) 4))))
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
		  0 :lisp)
      dimensions)
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte32)
      #.(movitz:basic-vector-type-tag :character))	 
    (check-type array string)
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimensions)))
    (cond
     (initial-element
      (check-type initial-element character)
      (dotimes (i dimensions)
	(setf (char array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%u32 (dimensions fill-pointer initial-element initial-contents)
  (let ((array (malloc-data-words dimensions)))
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
		  0 :lisp)
      dimensions)
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte32)
      #.(movitz:basic-vector-type-tag :u32))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimensions)))
    (cond
     (initial-element
      ;; (check-type initial-element (unsigned-byte 32))
      (dotimes (i dimensions)
	(setf (u32ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%u8 (dimensions fill-pointer initial-element initial-contents)
  (let ((array (malloc-data-words (truncate (+ dimensions 3) 4))))
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
		  0 :lisp)
      dimensions)
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte32)
      #.(movitz:basic-vector-type-tag :u8))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimensions)))
    (cond
     (initial-element
      (check-type initial-element (unsigned-byte 8))
      (dotimes (i dimensions)
	(setf (u8ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%code (dimensions fill-pointer initial-element initial-contents)
  (let ((array (malloc-data-words (truncate (+ dimensions 3) 4))))
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
		  0 :lisp)
      dimensions)
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte32)
      #.(movitz:basic-vector-type-tag :code))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimensions)))
    (cond
     (initial-element
      (check-type initial-element (unsigned-byte 8))
      (dotimes (i dimensions)
	(setf (u8ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%t (dimensions fill-pointer initial-element initial-contents)
  (check-type dimensions (and fixnum (integer 0 *)))
  (let ((array (malloc-words dimensions)))
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
		  0 :lisp)
      dimensions)
    (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
		  0 :unsigned-byte16)
      #.(movitz:basic-vector-type-tag :any-t))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimensions)))
    (cond
     (initial-contents
      (replace array initial-contents))
     (initial-element
      (dotimes (i dimensions)
	(setf (svref%unsafe array i) initial-element))))
    array))

(defun make-array (dimensions &key element-type initial-element initial-contents adjustable
				   fill-pointer displaced-to displaced-index-offset)
  (declare (ignore adjustable displaced-to displaced-index-offset))
  (etypecase dimensions
    (cons
     (error "Multi-dimensional arrays not supported."))
    (integer
     (cond
      ;; These should be replaced by subtypep sometime.
      ((eq element-type 'character)
       (make-basic-vector%character dimensions fill-pointer initial-element initial-contents))
      ((member element-type '(u8 (unsigned-byte 8)) :test #'equal)
       (make-basic-vector%u8 dimensions fill-pointer initial-element initial-contents))
      ((member element-type '(u32 (unsigned-byte 32)) :test #'equal)
       (make-basic-vector%u32 dimensions fill-pointer initial-element initial-contents))
      ((eq element-type 'code)
       (make-basic-vector%code dimensions fill-pointer initial-element initial-contents))
      (t (make-basic-vector%t dimensions fill-pointer initial-element initial-contents)
	 #+ignore
	 (let ((array (malloc-words dimensions)))
	   (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements)
			 0 :lisp)
	     dimensions)
	   (setf (memref array #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::type)
			 0 :unsigned-byte16)
	     #.(movitz:basic-vector-type-tag :any-t))
	   (setf (fill-pointer array)
	     (case fill-pointer
	       ((nil t) dimensions)
	       (t fill-pointer)))
	   (cond
	    (initial-contents
	     (replace array initial-contents))
	    (initial-element
	     (dotimes (i dimensions)
	       (setf (svref%unsafe array i) initial-element))))
	   array))))))

(defun vector (&rest objects)
  "=> vector"
  (declare (dynamic-extent objects))
  (let* ((length (length objects))
	 (vector (make-array length)))
    (do ((i 0 (1+ i))
	 (p objects (cdr p)))
	((endp p))
      (setf (svref vector i) (car p)))
    vector))

(defun vector-push (new-element vector)
  (check-type vector vector)
  (let ((p (fill-pointer vector)))
    (declare (type (unsigned-byte 16) p))
    (when (< p (array-dimension vector 0))
      (setf (aref vector p) new-element
	    (fill-pointer vector) (1+ p))
      p)))

(defun vector-pop (vector)
  (let ((p (1- (fill-pointer vector))))
    (assert (not (minusp p)))
    (setf (fill-pointer vector) p)
    (aref vector p)))

(defun vector-push-extend (new-element vector &optional extension)
  (declare (ignore extension))
  (check-type vector vector)
  (let ((p (fill-pointer vector)))
    (declare (type (unsigned-byte 16) p))
    (cond
     ((< p (array-dimension vector 0))
      (setf (aref vector p) new-element
	    (fill-pointer vector) (1+ p)))
     (t (error "Vector-push extending not implemented yet.")))
    p))


(define-compiler-macro bvref-u16 (&whole form vector offset index &environment env)
  (let ((actual-index (and (movitz:movitz-constantp index env)
			   (movitz::eval-form index env))))
    (if (not (typep actual-index '(integer 0 *)))
	`(bvref-u16-fallback ,vector ,offset ,index)
      (let ((var (gensym)))
	`(let ((,var ,vector))
	   (if (not (typep ,var 'vector-u8))
	       (bvref-u16-fallback ,var ,offset ,index)
	     (with-inline-assembly (:returns :untagged-fixnum-ecx)
	       (:compile-two-forms (:eax :ecx) ,var ,offset)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:andl #xfffe :ecx)
	       (:cmpw :cx (:eax #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements)))
	       (:jbe '(:sub-program () (:int 69)))
	       (:movw (:eax :ecx ,(+ actual-index (bt:slot-offset 'movitz::movitz-vector 'movitz::data))) :cx)
	       (:xchgb :cl :ch))))))))

(defun bvref-u16-fallback (vector offset index)
  (logior (ash (aref vector (+ index offset)) 8)
	  (aref vector (+ index offset))))
  
(defun bvref-u16 (vector offset index)
  "View <vector> as an sequence of octets, access the big-endian 16-bit word at position <index> + <offset>."
  (bvref-u16 vector offset index))
