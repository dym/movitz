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
;;;; $Id: arrays.lisp,v 1.45 2004/10/11 13:52:12 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(require :muerte/memref)
(provide :muerte/arrays)

(in-package muerte)

(defun vector-element-type (object)
  (memref object (movitz-type-slot-offset 'movitz-basic-vector 'element-type)
	  :type :unsigned-byte8))

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
  `(memref ,object (movitz-type-slot-offset 'movitz-basic-vector 'element-type)
	   :type :unsigned-byte8))

(defun (setf vector-element-type) (numeric-element-type vector)
  (check-type vector vector)
  (setf (memref vector (movitz-type-slot-offset 'movitz-basic-vector 'element-type)
		:type :unsigned-byte8)    
    numeric-element-type))

(defun array-element-type (array)
  (ecase (vector-element-type array)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :any-t)
       t)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :character)
       'character)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u8)
       '(unsigned-byte 8))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u16)
       '(unsigned-byte 16))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u32)
       '(unsigned-byte 32))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :bit)
       'bit)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :code)
       'code)))

(defun upgraded-array-element-type (type-specifier &optional environment)
  "=> upgraded-type-specifier"
  ;; We're in dire need of subtypep..
  (cond
   ((symbolp type-specifier)
    (case type-specifier
      ((character base-char standard-char)
       'character)
      ((code)
       'code)
      (t (let ((deriver (gethash type-specifier *derived-typespecs*)))
	   (if (not deriver)
	       t
	     (upgraded-array-element-type (funcall deriver)))))))
   ((null type-specifier)
    t)
   ((consp type-specifier)
    (case (car type-specifier)
      ((integer)
       (let* ((q (cdr type-specifier))
	      (min (if q (pop q) '*))
	      (max (if q (pop q) '*)))
	 (cond
	  ((or (eq min '*) (eq max '*))
	   t)
	  ((<= 0 min max 1)
	   'bit)
	  ((<= 0 min max #xff)
	   '(unsigned-byte 8))
	  ((<= 0 min max #xffff)
	   '(unsigned-byte 16))
	  ((<= 0 min max #xffffffff)
	   '(unsigned-byte 32)))))
      (t (let ((deriver (gethash (car type-specifier) *derived-typespecs*)))
	   (if (not deriver)
	       t
	     (upgraded-array-element-type (apply deriver (cdr type-specifier)) environment))))))
   (t t)))
    

(defun array-dimension (array axis-number)
  (etypecase array
    ((simple-array * 1)
     (assert (zerop axis-number))
     (memref array (movitz-type-slot-offset 'movitz-basic-vector 'num-elements)))))

(defun array-dimensions (array)
  (check-type array array)
  1)

(defun shrink-vector (vector new-size)
  (check-type vector vector)
  (setf (memref vector (movitz-type-slot-offset 'movitz-basic-vector 'num-elements))
    new-size))

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
    (simple-array
     (%basic-vector-has-fill-pointer-p array))
    (array nil)))
  
(defun fill-pointer (vector)
  (etypecase vector
    (simple-array
     (assert (%basic-vector-has-fill-pointer-p vector) (vector)
       "Vector has no fill-pointer.")
     (%basic-vector-fill-pointer vector))))

(defun copy-vector (vector)
  (check-type vector vector)
  (let ((length (the fixnum
		  (memref vector (movitz-type-slot-offset 'movitz-basic-vector 'num-elements)))))
    (ecase (vector-element-type vector)
      (#.(bt:enum-value 'movitz::movitz-vector-element-type :any-t)
	 (%shallow-copy-object vector (+ 2 length)))
      (#.(bt:enum-value 'movitz::movitz-vector-element-type :u32)
	 (%shallow-copy-non-pointer-object vector (+ 2 length)))
      ((#.(bt:enum-value 'movitz::movitz-vector-element-type :character)
	#.(bt:enum-value 'movitz::movitz-vector-element-type :u8)
	#.(bt:enum-value 'movitz::movitz-vector-element-type :code))
       (%shallow-copy-non-pointer-object vector	(+ 2 (truncate (+ 3 length) 4))))
      (#.(bt:enum-value 'movitz::movitz-vector-element-type :u16)
	 (%shallow-copy-non-pointer-object vector (+ 2 (truncate (+ 1 length) 2))))
      (#.(bt:enum-value 'movitz::movitz-vector-element-type :bit)
	 (%shallow-copy-non-pointer-object vector (+ 2 (truncate (+ 31 length) 32)))))))

(defun (setf fill-pointer) (new-fill-pointer vector)
  (etypecase vector
    (simple-array
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
       (do-it)))))

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
	(simple-array
	 (macrolet
	     ((do-it ()
		`(with-inline-assembly (:returns :eax)
		   (:declare-label-set basic-vector-dispatcher
				       ,(loop with x = (make-list 8 :initial-element 'unknown)
					    for et in '(:any-t :character :u8 :u32 :code :bit)
					    do (setf (elt x (bt:enum-value
							     'movitz::movitz-vector-element-type
							     et))
						 et)
					    finally (return x)))
		   (:compile-two-forms (:eax :ebx) array index)
		   (:movl (:eax ,movitz:+other-type-offset+) :ecx)
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
			      (movitz-type-slot-offset 'movitz-basic-vector 'num-elements))))))
		   (:jmp (:esi (:ecx 4) 'basic-vector-dispatcher
			       ,(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)))
		   
		   (() () '(:sub-program (unknown) (:int 100)))
		  :u32
		   (:movl (:eax :ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			  :ecx)
		   (:call-local-pf box-u32-ecx)
		   (:jmp 'return)
		  :u8 :code
		   (:movl :ebx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movzxb (:eax :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			    :ecx)
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
		   (:jmp 'return)
		  :character
		   (:movl :ebx :ecx)
		   (:movl :eax :ebx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movl ,(movitz:tag :character) :eax)
		   (:movb (:ebx :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
			  :ah)
		   (:jmp 'return)
		  :bit
		   (:movl :ebx :ecx)
		   (:movl :eax :ebx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:xorl :eax :eax)
		   (:btl :ecx (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jnc 'return)
		   (:addl ,movitz:+movitz-fixnum-factor+ :eax)
		   (:jmp 'return)
		  :any-t
		   (,movitz:*compiler-nonlocal-lispval-read-segment-prefix*
		    :movl (:eax :ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data))
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
	(simple-array
	 (macrolet
	     ((do-it ()
		`(with-inline-assembly (:returns :eax)
		   (:compile-two-forms (:eax :ebx) value vector)
		   (:leal (:ebx ,(- (movitz:tag :other))) :ecx)
		   (:compile-form (:result-mode :edx) index)
		   (:testb 7 :cl)
		   (:jnz '(:sub-program (not-a-vector)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a vector: ~S." vector))))
		   (:movl (:ebx ,movitz:+other-type-offset+) :ecx)
		   (:andl #xffff :ecx)
		   (:testb ,movitz:+movitz-fixnum-zmask+ :dl)
		   (:jnz '(:sub-program (not-an-index)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a vector index: ~S." index))))
		   (:cmpl (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
			  :edx)
		   (:jnc '(:sub-program (illegal-index)
			   (:compile-form (:result-mode :ignore)
			    (error "Index ~S out of range." index))))
		   ;; t?
		   (:cmpl ,(movitz:basic-vector-type-tag :any-t) :ecx)
		   (:jne 'not-any-t-vector)
		   (,movitz:*compiler-nonlocal-lispval-write-segment-prefix*
		    :movl :eax
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
		  code-vector
		   (:testl ,(logxor #xffffffff (* #xff movitz:+movitz-fixnum-factor+))
			   :eax)
		   (:jne '(:sub-program (not-an-u8)
			   (:compile-form (:result-mode :ignore)
			    (error "Not an (unsigned-byte 8): ~S" value))))
		   (:shll ,(- 8 movitz:+movitz-fixnum-shift+) :eax)
		   (:movl :edx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:movb :ah (:ebx :ecx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:shrl ,(- 8 movitz:+movitz-fixnum-shift+) :eax)
		   (:jmp 'return)

		  not-u8-vector
		   ;; Code?
		   (:cmpl ,(movitz:basic-vector-type-tag :code) :ecx)
		   (:je 'code-vector)
		   
		   ;; u32?
		   (:cmpl ,(movitz:basic-vector-type-tag :u32) :ecx)
		   (:jne 'not-u32-vector)
		   (:call-local-pf unbox-u32)
		   (:movl :ecx
			  (:ebx :edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)

		  not-u32-vector
		   ;; bit?
		   (:cmpl ,(movitz:basic-vector-type-tag :bit) :ecx)
		   (:jne 'not-bit-vector)
		   (:testl ,(logxor #xffffffff (* #x1 movitz:+movitz-fixnum-factor+))
			   :eax)
		   (:jne '(:sub-program (not-a-bit)
			   (:compile-form (:result-mode :ignore)
			    (error "Not a bit: ~S" value))))
		   (:movl :edx :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   
		   (:testl :eax :eax)
		   (:jnz 'set-one-bit)
		   (:btrl :ecx (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)
		  set-one-bit
		   (:btsl :ecx (:ebx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)))
		   (:jmp 'return)
		   
		  not-bit-vector
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
  `(memref ,simple-vector 2 :index ,index))

(define-compiler-macro (setf svref%unsafe) (value simple-vector index)
  `(setf (memref ,simple-vector 2 :index ,index) ,value))

(defun svref%unsafe (simple-vector index)
;;  (compiler-macro-call svref%unsafe simple-vector index))
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) simple-vector index)
    (:movl (:eax :ebx #.(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)) :eax)))

(defun (setf svref%unsafe) (value simple-vector index)
  (setf (svref%unsafe simple-vector index) value))

(defun svref (simple-vector index)
  (etypecase simple-vector
    (simple-vector
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
    (simple-vector
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
  (memref string 2 :index index :type :character))

(defun (setf char) (value string index)
  (assert (below index (array-dimension string 0)))
  (setf (memref string 2 :index index :type :character) value))

(defun schar (string index)
  (check-type string string)
  (assert (below index (length string)))
  (memref string 2 :index index :type :character))

(defun (setf schar) (value string index)
  (check-type string string)
  (assert (below index (length string)))
  (setf (aref string index) value))

(define-compiler-macro char%unsafe (string index)
  `(memref ,string 2 :index ,index :type :character))

(defun char%unsafe (string index)
  (char%unsafe string index))

(define-compiler-macro (setf char%unsafe) (value string index)
  `(setf (memref ,string 2 :index ,index :type :character) ,value))

(defun (setf char%unsafe) (value string index)
  (setf (char%unsafe string index) value))

;;; u8 accessors

(define-compiler-macro u8ref%unsafe (vector index)
  `(memref ,vector 2 :index ,index :type :unsigned-byte8))

(defun u8ref%unsafe (vector index)
  (u8ref%unsafe vector index))

(define-compiler-macro (setf u8ref%unsafe) (value vector index)
  `(setf (memref ,vector 2 :index ,index :type :unsigned-byte8) ,value))

(defun (setf u8ref%unsafe) (value vector index)
  (setf (u8ref%unsafe vector index) value))

;;; u32 accessors

(define-compiler-macro u32ref%unsafe (vector index)
  `(memref ,vector 2 :index ,index :type :unsigned-byte32))

(defun u32ref%unsafe (vector index)
  (compiler-macro-call u32ref%unsafe vector index))

(define-compiler-macro (setf u32ref%unsafe) (value vector index)
  (let ((var (gensym "setf-u32ref-value-")))
    ;; Use var so as to avoid re-boxing of the u32 value.
    `(let ((,var ,value))
       (setf (memref ,vector 2 :index ,index :type :unsigned-byte32) ,var)
       ,var)))

(defun (setf u32ref%unsafe) (value vector index)
  (compiler-macro-call (setf u32ref%unsafe) value vector index))

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

(defun make-basic-vector%character (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 (truncate (+ dimension 3) 4)))
	 (array (macrolet
		    ((do-it ()
		       `(with-non-pointer-allocation-assembly (words :fixed-size-p t
								     :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :character)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements))))))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-element
      (check-type initial-element character)
      (dotimes (i dimension)
	(setf (char array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%u32 (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 dimension))
	 (array (macrolet
		    ((do-it ()
		       `(with-non-pointer-allocation-assembly (words :fixed-size-p t
								     :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :u32)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements))))))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-element
      ;; (check-type initial-element (unsigned-byte 32))
      (dotimes (i dimension)
	(setf (u32ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%u8 (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 (truncate (+ dimension 3) 4)))
	 (array (macrolet
		    ((do-it ()
		       `(with-non-pointer-allocation-assembly (words :fixed-size-p t
								     :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :u8)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements))))))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-element
      (check-type initial-element (unsigned-byte 8))
      (dotimes (i dimension)
	(setf (u8ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%bit (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 (truncate (+ dimension 31) 32)))
	 (array (macrolet
		    ((do-it ()
		       `(with-non-pointer-allocation-assembly (words :fixed-size-p t
								     :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :bit)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements))))))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-element
      (check-type initial-element bit)
      (dotimes (i dimension)
	(setf (aref array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%code (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 (truncate (+ dimension 3) 4)))
	 (array (macrolet
		    ((do-it ()
		       `(with-non-pointer-allocation-assembly (words :fixed-size-p t
								     :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :code)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements))))))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-element
      (check-type initial-element (unsigned-byte 8))
      (dotimes (i dimension)
	(setf (u8ref%unsafe array i) initial-element)))
     (initial-contents
      (replace array initial-contents)))
    array))

(defun make-basic-vector%t (dimension fill-pointer initial-element initial-contents)
  (check-type dimension (and fixnum (integer 0 *)))
  (let* ((words (+ 2 dimension))
	 (array (macrolet
		    ((do-it ()
		       `(with-allocation-assembly (words :fixed-size-p t
							 :object-register :eax)
			  (:load-lexical (:lexical-binding dimension) :ecx)
			  (:movl ,(movitz:basic-vector-type-tag :any-t)
				 (:eax (:offset movitz-basic-vector type)))
			  (:movl :ecx (:eax (:offset movitz-basic-vector num-elements)))
			  (:addl 4 :ecx)
			  (:andl -8 :ecx)
			  (:jz 'init-done)
			  init-loop
			  (:movl :edi (:eax (:offset movitz-basic-vector data) :ecx -4))
			  (:subl 4 :ecx)
			  (:jnz 'init-loop)
			  init-done
			  )))
		  (do-it))))
    (cond
     (fill-pointer
      (setf (fill-pointer array) fill-pointer))
     ((array-has-fill-pointer-p array)
      (setf (fill-pointer array) dimension)))
    (cond
     (initial-contents
      (replace array initial-contents))
     (initial-element
      (dotimes (i dimension)
	(setf (svref%unsafe array i) initial-element))))
    array))

(defun make-array (dimensions &key element-type initial-element initial-contents adjustable
				   fill-pointer displaced-to displaced-index-offset)
  (declare (ignore adjustable displaced-to displaced-index-offset))
  (let ((size (cond ((integerp dimensions)
                     dimensions)
                    ((and (consp dimensions) (null (cdr dimensions)))
                     (car dimensions))
                    (t
                     (error "Multi-dimensional arrays not supported.")))))
    (let ((upgraded-element-type (upgraded-array-element-type element-type)))
      (cond
       ;; These should be replaced by subtypep sometime.
       ((eq upgraded-element-type 'character)
	(make-basic-vector%character size fill-pointer initial-element initial-contents))
       ((eq upgraded-element-type 'bit)
	(make-basic-vector%bit size fill-pointer initial-element initial-contents))
       ((member upgraded-element-type '(u8 (unsigned-byte 8)) :test #'equal)
	(make-basic-vector%u8 size fill-pointer initial-element initial-contents))
       ((member upgraded-element-type '(u32 (unsigned-byte 32)) :test #'equal)
	(make-basic-vector%u32 size fill-pointer initial-element initial-contents))
       ((eq upgraded-element-type 'code)
	(make-basic-vector%code size fill-pointer initial-element initial-contents))
       (t (make-basic-vector%t size fill-pointer initial-element initial-contents))))))

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
			   (movitz:movitz-eval index env))))
    (if (not (typep actual-index '(integer 0 *)))
	`(bvref-u16-fallback ,vector ,offset ,index)
      (let ((var (gensym)))
	`(let ((,var ,vector))
	   (if (not (typep ,var 'vector-u8))
	       (bvref-u16-fallback ,var ,offset ,index)
	     (with-inline-assembly (:returns :untagged-fixnum-ecx)
	       (:compile-two-forms (:eax :ecx) ,var ,offset)
	       (:cmpl (:eax ,(bt:slot-offset 'movitz::movitz-basic-vector
					     'movitz::num-elements))
		      :ecx)
	       (:jnc '(:sub-program () (:int 69)))
	       (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
	       (:movw (:eax :ecx ,(+ actual-index (bt:slot-offset 'movitz::movitz-basic-vector
								  'movitz::data)))
		      :cx)
	       (:xchgb :cl :ch))))))))

(defun bvref-u16-fallback (vector offset index)
  (logior (ash (aref vector (+ index offset)) 8)
	  (aref vector (+ index offset))))
  
(defun bvref-u16 (vector offset index)
  "View <vector> as an sequence of octets, access the big-endian 16-bit word at position <index> + <offset>."
  (bvref-u16 vector offset index))

(define-typep array (x &optional (element-type '*) (dimension-spec '*))
  (and (typep x 'array)
       (or (eq element-type '*)
	   (eq element-type t)
	   (equalp (array-element-type x)
		   (upgraded-array-element-type element-type)))
       (or (eq dimension-spec '*)
	   (and (integerp dimension-spec)
		(= dimension-spec (array-dimensions x)))
	   (and (listp dimension-spec)
		(do ((array-rank (array-dimensions x))
		     (d 0 (1+ d))
		     (q dimension-spec))
		    ((null q) (= d array-rank))
		  (let ((dim (pop q)))
		    (cond
		     ((>= d array-rank)
		      (return nil))
		     ((eq dim '*))
		     ((= dim (array-dimension x d)))
		     (t (return nil)))))))))
