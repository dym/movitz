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
;;;; $Id: arrays.lisp,v 1.16 2004/04/01 02:09:58 ffjeld Exp $
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
       '(unsigned-byte 32))))

(defmacro vector-dimension (vector)
  `(movitz-accessor-u16 ,vector movitz-vector num-elements))

(defun array-dimension (array axis-number)
  (etypecase array
    (vector
     (assert (zerop axis-number))
     (vector-dimension array))))

(define-compiler-macro array-dimension (&whole form array axis-number)
  (cond
   ((and (movitz:movitz-constantp axis-number)
	 (zerop (movitz::movitz-eval axis-number)))
    `(vector-dimension ,array))
   (t (warn "Unknown array-dimension: ~S" form)
      form)))

(defun shrink-vector (vector new-size)
  (set-movitz-accessor-u16 vector movitz-vector num-elements new-size)
  vector)


(define-compiler-macro vector-fill-pointer (vector)
  `(movitz-accessor-u16 ,vector movitz-vector fill-pointer)
  #+ignore `(with-inline-assembly (:returns :untagged-fixnum-ecx)
	      (:compile-form (:result-mode :eax) ,vector)
	      (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-vector 'movitz::fill-pointer))
		       :ecx)))

(defun vector-fill-pointer (vector)
  (vector-fill-pointer vector))


(defun array-has-fill-pointer-p (array)
  (etypecase array			;
    (vector t)
    (array nil)))
  
(defun fill-pointer (vector)
  (check-type vector vector)
  (memref vector #.(bt:slot-offset 'movitz:movitz-vector 'movitz::fill-pointer) 0
	  :unsigned-byte16))


(defun (setf fill-pointer) (new-fill-pointer vector)
  (check-type vector vector)
  (assert (<= new-fill-pointer (vector-dimension vector)))
  (setf (memref vector #.(bt:slot-offset 'movitz::movitz-vector 'movitz::fill-pointer) 0
		:unsigned-byte16)
    new-fill-pointer))

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


(defun aref (vector &rest subscripts)
  (numargs-case
   (2 (vector index)
      (with-inline-assembly (:returns :eax)
	(:compile-form (:result-mode :eax) vector)
	(:compile-form (:result-mode :ebx) index)
	(:leal (:eax #.(cl:- (movitz::tag :other))) :ecx)
	(:testb #.movitz::+movitz-fixnum-zmask+ :bl)
	(:jnz '(:sub-program (not-fixnum) (:int 107))) ; index not fixnum
	(:andl #.(cl:ash #x000ffff movitz::+movitz-fixnum-shift+) :ebx)

	(:testb 7 :cl)
	(:jnz '(:sub-program ()
		(:compile-form (:result-mode :ignore)
		 (error "Not a vector: ~S" vector))))
		
	(:shrl #.movitz::+movitz-fixnum-shift+ :ebx)
	(:movzxw (:eax -2) :ecx)

	(:cmpw (:eax #.(bt:slot-offset 'movitz:movitz-vector 'movitz::num-elements)) :bx)
	(:jae '(:sub-program ()
		(:compile-form (:result-mode :ignore)
		 (error "Index ~D out of bounds ~D." index (length vector)))))

	(:cmpl #.(movitz:vector-type-tag :any-t) :ecx)
	(:jne 'not-any-t)
	(:movl (:eax (:ebx 4) 2) :eax)
	(:jmp 'done)

       not-any-t
	(:cmpl #.(movitz:vector-type-tag :character) :ecx)
	(:jne 'not-character)
	(:movb (:eax :ebx 2) :bl)
	(:xorl :eax :eax)
	(:movb :bl :ah)
	(:movb #.(movitz::tag :character) :al) ; character
	(:jmp 'done)
    
       not-character
	(:cmpl #.(movitz:vector-type-tag :u8) :ecx)
	(:jne 'not-u8)
	(:movzxb (:eax :ebx 2) :eax)	; u8
	(:shll #.movitz::+movitz-fixnum-shift+ :eax)
	(:jmp 'done)
    
       not-u8
	(:cmpl #.(movitz:vector-type-tag :u16) :ecx)
	(:jne 'not-u16)
	(:movzxw (:eax (:ebx 2) 2) :eax) ; u16
	(:jmp 'done)

       not-u16
	(:cmpl #.(movitz:vector-type-tag :u32) :ecx)
	(:jne 'not-u32)
	(:movl (:eax (:ebx 4) 2) :ecx)	; u32
	(:cmpl #.movitz::+movitz-most-positive-fixnum+ :ecx)
	(:jg '(:sub-program (:overflowing-u32)
	       (:int 107)))
	(:leal ((:ecx #.movitz::+movitz-fixnum-factor+)) :eax)
	(:jmp 'done)

       not-u32
	(:compile-form (:result-mode :ignore)
		       (error "Not a vector: ~S" vector))

       done))
   (t (vector &rest subscripts)
      (declare (dynamic-extent subscripts)
	       (ignore vector subscripts))
      (error "Multi-dimensional arrays not implemented."))))

(defun (setf aref) (value vector &rest subscripts)
  (numargs-case
   (3 (value vector index)
      (with-inline-assembly (:returns :ebx)
	(:compile-form (:result-mode :ebx) value)
	(:compile-form (:result-mode :eax) vector)

	(:leal (:eax #.(cl:- (movitz::tag :other))) :ecx)
	(:testb 7 :cl)
	(:jnz '(:sub-program ()
		(:compile-form (:result-mode :ignore)
		 (error "Not a vector: ~S" vector))))
	(:movzxw (:eax -2) :edx)
    
	(:compile-form (:result-mode :ecx) index)
	(:testb #.movitz::+movitz-fixnum-zmask+ :cl)
	(:jnz '(:sub-program () (:int 107))) ; index not fixnum
	(:andl #.(cl:ash #xffff movitz::+movitz-fixnum-shift+) :ecx)
	(:shrl #.movitz::+movitz-fixnum-shift+ :ecx)

	(:cmpw (:eax #.(bt:slot-offset 'movitz:movitz-vector 'movitz::num-elements)) :cx)
	(:jae '(:sub-program () (:int 61) (:jmp (:pc+ -4)))) ; index out of bounds

	(:cmpl #.(movitz:vector-type-tag :any-t) :edx)
	(:jnz 'not-any-t)

	(:movl :ebx (:eax (:ecx 4) 2))
	(:jmp 'done)

       not-any-t
	(:cmpl #.(movitz:vector-type-tag :character) :edx)
	(:jnz 'not-character)
	(:cmpb #.(movitz:tag :character) :bl)
	(:jnz '(:sub-program (not-character-value)
		(:compile-form (:result-mode :ignore)
		 (error "Value not character: ~S" value))))
	(:movb :bh (:eax :ecx 2))
	(:jmp 'done)
    
       not-character
	(:cmpl #.(movitz:vector-type-tag :u8) :edx)
	(:jnz 'not-u8)
	(:testl #.(cl:ldb (cl:byte 32 0) (cl:- -1 (cl:* #xff movitz:+movitz-fixnum-factor+))) :ebx)
	(:jnz '(:sub-program (not-u8-value)
		(:compile-form (:result-mode :ignore)
		 (error "Value not (unsigned-byte 8): ~S" value))))
	(:shrl #.movitz:+movitz-fixnum-shift+ :ebx)
	(:movb :bl (:eax (:ecx 1) #.(bt:slot-offset 'movitz:movitz-vector 'movitz::data)))
	(:leal ((:ebx #.movitz:+movitz-fixnum-factor+)) :ebx)
	(:jmp 'done)
    
    
       not-u8
	(:cmpl #.(movitz:vector-type-tag :u16) :edx)
	(:jnz 'not-u16)
	(:testl #.(cl:ldb (cl:byte 32 0) (cl:- -1 (cl:* #xffff movitz:+movitz-fixnum-factor+))) :ebx)
	(:jnz '(:sub-program (not-u16-value)
		(:compile-form (:result-mode :ignore)
		 (error "Value not (unsigned-byte 16): ~S" value))))
	(:shrl #.movitz:+movitz-fixnum-shift+ :ebx)
	(:movw :bx (:eax (:ecx 2) #.(bt:slot-offset 'movitz:movitz-vector 'movitz::data)))
	(:leal ((:ebx #.movitz:+movitz-fixnum-factor+)) :ebx)
	(:jmp 'done)

       not-u16
	(:cmpl #.(movitz:vector-type-tag :u32) :edx)
	(:jnz 'not-u32)
	(:testl #.(cl:ldb (cl:byte 32 0) (cl:- -1 (cl:* #xffffffff movitz:+movitz-fixnum-factor+))) :ebx)
	(:jnz '(:sub-program (not-u32-value)
		(:compile-form (:result-mode :ignore)
		 (error "Value not (unsigned-byte 32): ~S" value))))
	(:shrl #.movitz:+movitz-fixnum-shift+ :ebx)
       	(:movl :ebx (:eax (:ecx 4) #.(bt:slot-offset 'movitz:movitz-vector 'movitz::data)))
	(:leal ((:ebx #.movitz:+movitz-fixnum-factor+)) :ebx)
	(:jmp 'done)

       not-u32
	(:compile-form (:result-mode :ignore) (error "Not a vector: ~S" vector))
       done))
   (t (value vector &rest subscripts)
      (declare (dynamic-extent subscripts)
	       (ignore value vector subscripts))
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
  (macrolet ((do-svref ()
	       `(with-inline-assembly (:returns :eax)
		  (:compile-two-forms (:eax :ebx) simple-vector index)
		  (:leal (:eax ,(- (movitz::tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jnz '(:sub-program (not-simple-vector)
			  (:int 66)))
		  (:cmpw ,(dpb (bt:enum-value 'movitz::movitz-vector-element-type :any-t)
			       (byte 8 8)
			       (movitz:tag :vector))
			 (:eax ,(bt:slot-offset 'movitz::movitz-vector 'movitz::type)))
		  (:jne 'not-simple-vector)
		  (:testb #.movitz::+movitz-fixnum-zmask+ :bl)
		  (:jnz '(:sub-program (not-fixnum)
			  (:int 107)))
		  (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements))
			   :ecx)
		  (:shll #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:xchgl :ecx :ebx)
		  (:cmpl :ecx :ebx)
		  (:jna '(:sub-program (index-out-of-bounds)
			  (:int 70)))
		  ,@(if (= 4 movitz::+movitz-fixnum-factor+)
			`((:movl (:eax :ecx #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data))
				 :eax))
		      `((:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
			(:movl (:eax (:ecx 4) #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data))
			       :eax))))))
    (do-svref)))
    

(defun (setf svref) (value simple-vector index)
  (check-type simple-vector simple-vector)
  (assert (below index (vector-dimension simple-vector)))
  (setf (memref simple-vector 2 index :lisp) value))

;;; string accessors

(defun char (string index)
  (check-type string string)
  (assert (below index (vector-dimension string)))
  (memref string 2 index :character))

(defun (setf char) (value string index)
  (setf (aref string index) value))

(defun schar (string index)
  (check-type string string)
  (assert (below index (length string)))
  (memref string 2 index :character))

(defun (setf schar) (value string index)
  (check-type string string)
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
    (assert (<= end (vector-dimension vector))))
  (case (vector-element-type vector)
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :any-t)
       (values #'svref%unsafe #'(setf svref%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :character)
       (values #'char%unsafe #'(setf char%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u8)
       (values #'u8ref%unsafe #'(setf u8ref%unsafe)))
    (#.(bt:enum-value 'movitz::movitz-vector-element-type :u32)
       (values #'u32ref%unsafe #'(setf u32ref%unsafe)))
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

(defun make-array (dimensions &key element-type initial-element initial-contents adjustable
				   fill-pointer displaced-to displaced-index-offset)
  (declare (ignore adjustable displaced-to displaced-index-offset))
  (etypecase dimensions
    (cons
     (error "Multi-dimensional arrays not supported."))
    (integer
     (setf fill-pointer (if (integerp fill-pointer) fill-pointer dimensions))
     (cond
      ((equal element-type 'character)
       (let ((array (malloc-data-clumps (truncate (+ dimensions 7 8) 8))))
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::flags)
		       0 :unsigned-byte16)
	   0)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements)
		       0 :unsigned-byte16)
	   dimensions)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::type)
		       0 :unsigned-byte16)
	   #.(movitz:vector-type-tag :character))
	 (check-type array string)
	 (setf (fill-pointer array) fill-pointer)
	 (cond
	  (initial-element
	   (check-type initial-element character)
	   (dotimes (i dimensions)
	     (setf (char array i) initial-element)))
	  (initial-contents
	   (dotimes (i dimensions)
	     (setf (char array i) (elt initial-contents i)))))
	 array))
      ((member element-type '(u8 (unsigned-byte 8)) :test #'equal)
       (let ((array (malloc-data-clumps (truncate (+ dimensions 7 8) 8))))
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::flags)
		       0 :unsigned-byte16)
	   0)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements)
		       0 :unsigned-byte16)
	   dimensions)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::type)
		       0 :unsigned-byte16)
	   #.(movitz:vector-type-tag :u8))
	 (setf (fill-pointer array) fill-pointer)
	 (cond
	  (initial-element
	   (dotimes (i dimensions)
	     (setf (aref array i) initial-element)))
	  (initial-contents
	   (replace array initial-contents)))
	 array))
      ((member element-type '(u32 (unsigned-byte 32)) :test #'equal)
       (let ((array (malloc-words dimensions)))
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::flags)
		       0 :unsigned-byte16)
	   0)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements)
		       0 :unsigned-byte16)
	   dimensions)
	 (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::type)
		       0 :unsigned-byte16)
	   #.(movitz:vector-type-tag :u32))	 
	 (setf (fill-pointer array) fill-pointer)
	 (cond
	  (initial-element
	   (dotimes (i dimensions)
	     (setf (aref array i) initial-element)))
	  (initial-contents
	   (replace array initial-contents)))
	 array))
      (t (let ((array (malloc-words dimensions)))
	   (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::flags)
			 0 :unsigned-byte16)
	     0)
	   (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::num-elements)
			 0 :unsigned-byte16)
	     dimensions)
	   (setf (memref array #.(bt:slot-offset 'movitz::movitz-vector 'movitz::type)
			 0 :unsigned-byte16)
	     #.(movitz:vector-type-tag :any-t))
	   (setf (fill-pointer array) fill-pointer)
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
  (let ((p (vector-fill-pointer vector)))
    (declare (type (unsigned-byte 16) p))
    (when (< p (vector-dimension vector))
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
  (vector-push new-element vector))

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
