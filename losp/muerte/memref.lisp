;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      memref.lisp
;;;; Description:   Low-level memory access.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Mar  6 21:25:49 2001
;;;;                
;;;; $Id: memref.lisp,v 1.1 2004/01/13 11:05:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/memref)

(in-package muerte)

(defun memwrite2 (address value)
  "Writes the 16-bit VALUE to memory ADDRESS."
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :eax) address)
    (:compile-form (:result-mode :ebx) value)
    (:sarl #.movitz::+movitz-fixnum-shift+ :eax)
    (:sarl #.movitz::+movitz-fixnum-shift+ :ebx)
    (:movw :bx (:eax))))

(define-compiler-macro memref (&whole form object offset index type &environment env)
;;;  (assert (typep offset '(integer 0 0)) (offset)
;;;    (error "memref offset not supported."))
  (if (not (movitz:movitz-constantp type))
      form
    (labels ((extract-constant-delta (form)
	     "Try to extract at compile-time an integer offset from form."
	     (cond
	      ((movitz:movitz-constantp form env)
	       (let ((x (movitz::eval-form form env)))
		 (check-type x integer)
		 (values x 0)))
	      ((not (consp form))
	       (values 0 form))
	      (t (case (car form)
		   (1+ (values 1 (second form)))
		   (1- (values -1 (second form)))
		   (+ (case (length form)
			(1 (values 0 0))
			(2 (values 0 (second form)))
			(t (loop with x = 0 and f = nil for sub-form in (cdr form)
			       as sub-value = (when (movitz:movitz-constantp sub-form env)
						(movitz::eval-form sub-form env))
			       do (if (integerp sub-value)
				      (incf x sub-value)
				    (push sub-form f))
			       finally (return (values x (cons '+ (nreverse f))))))))
		   (t #+ignore (warn "extract from: ~S" form)
		      (values 0 form)))))))
      (multiple-value-bind (constant-index index)
	  (extract-constant-delta index)
	(multiple-value-bind (constant-offset offset)
	    (extract-constant-delta offset)
	  (flet ((offset-by (element-size)
		   (+ constant-offset (* constant-index element-size))))
	    #+ignore
	    (warn "o: ~S, co: ~S, i: ~S, ci: ~S"
		  offset constant-offset
		  index constant-index)
	    (let ((type (movitz::eval-form type env)))
	      (case type
		(:unsigned-byte8
		 `(with-inline-assembly (:returns :untagged-fixnum-eax)
		    (:compile-form (:result-mode :push) ,object)
		    (:compile-two-forms (:ecx :ebx) ,offset ,index)
		    (:popl :eax)	; object
		    (:addl :ecx :ebx)	; index += offset
		    (:sarl #.movitz::+movitz-fixnum-shift+ :ebx)
		    (:movzxb (:eax :ebx ,(offset-by 1)) :eax)))
		(:unsigned-byte16
		 `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		    (:compile-form (:result-mode :push) ,object)
		    (:compile-two-forms (:eax :ebx) ,offset ,index)
		    (:sarl #.(cl:1- movitz::+movitz-fixnum-shift+) :ebx)
		    (:sarl #.movitz::+movitz-fixnum-shift+ :eax)
		    (:addl :eax :ebx)
		    (:popl :eax)	; object
		    (:movzxw (:eax :ebx ,(offset-by 2)) :ecx)))
		(:unsigned-byte32
		 (assert (= 2 movitz::+movitz-fixnum-shift+))
		 (let ((overflow (gensym "overflow-")))
		   `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		      (:compile-form (:result-mode :push) ,object)
		      (:compile-two-forms (:ecx :ebx) ,offset ,index)
		      (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
		      (:addl :ebx :ecx)
		      (:popl :eax)	; object
		      (:movl (:eax :ecx ,(offset-by 4)) :ecx)
		      (:cmpl ,movitz::+movitz-most-positive-fixnum+ :ecx)
		      (:jg '(:sub-program (,overflow) (:int 4))))))
		(:unsigned-byte29+3
		 ;; Two values: the 29 upper bits as unsigned integer,
		 ;; and secondly the lower 3 bits as unsigned.
		 (assert (= 2 movitz::+movitz-fixnum-shift+))
		 `(with-inline-assembly (:returns :multiple-values)
		    (:compile-form (:result-mode :push) ,object)
		    (:compile-two-forms (:ecx :ebx) ,offset ,index)
		    (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
		    (:addl :ebx :ecx)
		    (:popl :eax)	; object
		    (:movl (:eax :ecx ,(offset-by 4)) :ecx)
		    (:leal ((:ecx 4)) :ebx)
		    (:shrl 1 :ecx)
		    (:andl #b11100 :ebx)
		    (:andl -4 :ecx)
		    (:movl :ecx :eax)
		    (:movl 2 :ecx)
		    (:stc)))
		(:signed-byte30+2
		 ;; Two values: the 30 upper bits as signed integer,
		 ;; and secondly the lower 2 bits as unsigned.
		 (assert (= 2 movitz::+movitz-fixnum-shift+))
		 `(with-inline-assembly (:returns :multiple-values)
		    (:compile-form (:result-mode :push) ,object)
		    (:compile-two-forms (:ecx :ebx) ,offset ,index)
		    (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
		    (:addl :ebx :ecx)
		    (:popl :eax)	; object
		    (:movl (:eax :ecx ,(offset-by 4)) :ecx)
		    (:leal ((:ecx 4)) :ebx)
		    (:andl #b1100 :ebx)
		    (:andl -4 :ecx)
		    (:movl :ecx :eax)
		    (:movl 2 :ecx)
		    (:stc)))
		(:character
		 (when (eq 0 index) (warn "zero char index!"))
		 (cond
		  ((eq 0 offset)
		   `(with-inline-assembly (:returns :eax)
		      (:compile-two-forms (:ecx :ebx) ,object ,index)
		      (:xorl :eax :eax)
		      (:movb #.(movitz:tag :character) :al)
		      (:sarl #.movitz::+movitz-fixnum-shift+ :ebx) ; scale index
		      (:movb (:ecx :ebx ,(offset-by 1)) :ah)))
		  (t `(with-inline-assembly (:returns :eax)
			(:compile-form (:result-mode :push) ,object)
			(:compile-two-forms (:ecx :ebx) ,offset ,index)
			(:addl :ecx :ebx)
			(:xorl :eax :eax)
			(:movb #.(movitz:tag :character) :al)
			(:popl :ecx)	; pop object
			(:sarl #.movitz::+movitz-fixnum-shift+ :ebx) ; scale offset+index
			(:movb (:ebx :ecx ,(offset-by 1)) :ah)))))
		((:lisp :lisp-code-vector)
		 (let ((fix-when-code-vector
			(when (eq type :lisp-code-vector)
			  `((:subl ,movitz::+code-vector-word-offset+ :eax)))))
		   (cond
		    ((and (eq 0 index) (eq 0 offset))
		     `(with-inline-assembly (:returns :eax)
			(:compile-form (:result-mode :eax) ,object)
			(:movl (:eax ,(offset-by 4)) :eax)
			,@fix-when-code-vector))
		    ((eq 0 offset)
		     `(with-inline-assembly (:returns :eax)
			(:compile-two-forms (:eax :ecx) ,object ,index)
			,@(when (cl:plusp (cl:- movitz::+movitz-fixnum-shift+ 2))
			    `((:sarl ,(cl:- movitz::+movitz-fixnum-shift+ 2)) :ecx))
			(:movl (:eax :ecx ,(offset-by 4)) :eax)
			,@fix-when-code-vector))
		    (t `(with-inline-assembly (:returns :eax)
			  (:compile-form (:result-mode :push) ,object)
			  (:compile-two-forms (:untagged-fixnum-eax :ecx) ,offset ,index)
			  ,@(when (cl:plusp (cl:- movitz::+movitz-fixnum-shift+ 2))
			      `((:sarl ,(cl:- movitz::+movitz-fixnum-shift+ 2)) :ecx))
			  (:addl :ecx :eax)
			  (:popl :ebx)	; pop object
			  (:movl (:eax :ebx ,(offset-by 4)) :eax)
			  ,@fix-when-code-vector)))))
		(t (error "Unknown memref type: ~S" (movitz::eval-form type nil nil))
		   form)))))))))

(defun memref (object offset index type)
  (ecase type
    (:unsigned-byte8    (memref object offset index :unsigned-byte8))
    (:unsigned-byte16   (memref object offset index :unsigned-byte16))
    (:unsigned-byte32   (memref object offset index :unsigned-byte32))
    (:character         (memref object offset index :character))
    (:lisp              (memref object offset index :lisp))
    (:lisp-code-vector  (memref object offset index :lisp-code-vector))
    (:signed-byte30+2   (memref object offset index :signed-byte30+2))
    (:unsigned-byte29+3 (memref object offset index :unsigned-byte29+3))))

(define-compiler-macro (setf memref) (&whole form value object offset index type)
  (if (not (movitz:movitz-constantp type))
      form
    (case (movitz::eval-form type)
      (:character
       `(with-inline-assembly (:returns :eax)
	  (:compile-form (:result-mode :push) ,object)
	  (:compile-form (:result-mode :push) ,offset)
	  (:compile-two-forms (:ebx :eax) ,index ,value)
	  (:popl :ecx)			; offset
	  (:addl :ecx :ebx)		; index += offset
	  (:sarl #.movitz::+movitz-fixnum-shift+ :ebx)
	  (:popl :ecx)			; object
	  (:movb :ah (:ebx :ecx))))
      (:unsigned-byte16
       `(with-inline-assembly (:returns :untagged-fixnum-eax)
	  (:compile-form (:result-mode :push) ,object)
	  (:compile-form (:result-mode :push) ,offset)
	  (:compile-two-forms (:ebx :eax) ,index ,value)
	  (:sarl #.(cl:1- movitz::+movitz-fixnum-shift+) :ebx)
	  (:popl :ecx)			; offset
	  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
	  (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
	  (:addl :ecx :ebx)		; index += offset
	  (:popl :ecx)			; object
	  (:movw :ax (:ebx :ecx))))
      (:unsigned-byte8
       `(with-inline-assembly (:returns :untagged-fixnum-eax)
	  (:compile-form (:result-mode :push) ,object)
	  (:compile-form (:result-mode :push) ,offset)
	  (:compile-two-forms (:ebx :eax) ,index ,value)
	  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
	  (:popl :ecx)			; offset
	  (:addl :ecx :ebx)		; index += offset
	  (:sarl #.movitz::+movitz-fixnum-shift+ :ebx)
	  (:popl :ecx)			; object
	  (:movb :al (:ebx :ecx))))
      (:lisp
       `(with-inline-assembly (:returns :eax)
	  (:compile-form (:result-mode :push) ,object)
	  (:compile-form (:result-mode :push) ,offset)
	  (:compile-two-forms (:ebx :eax) ,index ,value)
	  (:popl :ecx)			; offset
	  (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
	  ,@(when (cl:plusp (cl:- movitz::+movitz-fixnum-shift+ 2))
	      `((:sarl ,(cl:- movitz::+movitz-fixnum-shift+ 2)) :ebx))
	  (:addl :ecx :ebx)		; index += offset
	  (:popl :ecx)			; value
	  (:movl :eax (:ebx :ecx))))
      (t ;; (warn "Can't handle inline MEMREF: ~S" form)
	 form))))

(defun (setf memref) (value object offset index type)
  (ecase type
    (:character
     (setf (memref object offset index :character) value))
    (:unsigned-byte8
     (setf (memref object offset index :unsigned-byte8) value))
    (:unsigned-byte16
     (setf (memref object offset index :unsigned-byte8) value))
    (:lisp
     (setf (memref object offset index :lisp) value))))

(define-compiler-macro memref-int (&whole form &environment env address offset index type
				   &optional physicalp)
  (if (or (not (movitz:movitz-constantp type physicalp))
	  (not (movitz:movitz-constantp physicalp env)))
      form
    (let* ((physicalp (movitz::eval-form physicalp env))
	   (prefixes (if physicalp '(:gs-override) ())))
      (ecase (movitz::eval-form type)
	(:lisp
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :push) ,address)
	    (:compile-form (:result-mode :push) ,offset)
	    (:compile-form (:result-mode :ecx) ,index)
	    (:popl :ebx)		; offset
	    (:popl :eax)		; address
	    (:shll 2 :ecx)
	    (:addl :ecx :eax)
	    (:addl :ebx :eax)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
	    (,prefixes :movl (:eax) :eax)))
	(:unsigned-byte8
	 `(with-inline-assembly (:returns :untagged-fixnum-eax)
	    (:compile-form (:result-mode :push) ,address)
	    (:compile-form (:result-mode :push) ,offset)
	    (:compile-form (:result-mode :ecx) ,index)
	    (:popl :eax)		; offset
	    (:popl :ebx)		; address
	    (:addl :ecx :ebx)		; add index
	    (:addl :eax :ebx)		; add offset
	    (:xorl :eax :eax)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :ebx) ; scale down address
	    (,prefixes :movb (:ebx) :al)))
	(:unsigned-byte32
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :push) ,address)
	    (:compile-two-forms (:eax :ecx) ,offset ,index)
	    (:popl :ebx)		; address
	    (:shll 2 :ecx)
	    (:addl :ebx :eax)
	    (:into)
	    (:testb ,(cl:mask-field (cl:byte (cl:+ 2 movitz::+movitz-fixnum-shift+) 0) -1)
		    :al)
	    (:jnz '(:sub-program (unaligned) (:int 63)))
	    (:addl :ecx :eax)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :eax) ; scale down address
	    (,prefixes :movl (:eax) :ecx)
	    (:cmpl ,movitz::+movitz-most-positive-fixnum+ :ecx)
	    (:jg '(:sub-program (overflow) (:int 4)))
	    (:leal ((:ecx ,movitz::+movitz-fixnum-factor+)
		    :edi ,(- (movitz::image-nil-word movitz::*image*)))
		   :eax)))
	(:unsigned-byte16
	 (cond
	  ((and (eq 0 offset) (eq 0 index))
	   `(with-inline-assembly (:returns :untagged-fixnum-eax)
	      (:compile-form (:result-mode :ebx) ,address)
	      (:xorl :eax :eax)
	      (:shrl #.movitz::+movitz-fixnum-shift+ :ebx) ; scale down address
	      (,prefixes :movw (:ebx (:ecx 2)) :ax)))
	  (t `(with-inline-assembly (:returns :untagged-fixnum-eax)
		(:compile-form (:result-mode :push) ,address)
		(:compile-form (:result-mode :push) ,offset)
		(:compile-form (:result-mode :ecx) ,index)
		(:popl :eax)		; offset
		(:popl :ebx)		; address
		(:shrl #.movitz::+movitz-fixnum-shift+ :ecx) ; scale index
		(:addl :eax :ebx)	; add offset
		(:xorl :eax :eax)
		(:shrl #.movitz::+movitz-fixnum-shift+ :ebx) ; scale down address
		(,prefixes :movw (:ebx (:ecx 2)) :ax)))))))))

(defun memref-int (address offset index type &optional physicalp)
  (cond
   ((not physicalp)
    (ecase type
      (:lisp
       (memref-int address offset index :lisp))
      (:unsigned-byte8
       (memref-int address offset index :unsigned-byte8))
      (:unsigned-byte16
       (memref-int address offset index :unsigned-byte16))
      (:unsigned-byte32
       (memref-int address offset index :unsigned-byte32))))
   (physicalp
    (ecase type
      (:lisp
       (memref-int address offset index :lisp t))
      (:unsigned-byte8
       (memref-int address offset index :unsigned-byte8 t))
      (:unsigned-byte16
       (memref-int address offset index :unsigned-byte16 t))
      (:unsigned-byte32
       (memref-int address offset index :unsigned-byte32 t))))))

(define-compiler-macro (setf memref-int) (&whole form &environment env value address offset index type
								   &optional physicalp)
  (if (or (not (movitz:movitz-constantp type env))
	  (not (movitz:movitz-constantp physicalp env)))
      (progn
	(warn "setf memref-int form: ~S, ~S ~S" form type physicalp)
	form)
    (let* ((physicalp (movitz::eval-form physicalp env))
	   (prefixes (if physicalp '(:gs-override) ())))
      (ecase type
	(:lisp
	 (assert (= 4 movitz:+movitz-fixnum-factor+))
	 `(with-inline-assembly (:returns :untagged-fixnum-eax)
	    (:compile-form (:result-mode :push) ,address)
	    (:compile-form (:result-mode :push) ,index)
	    (:compile-form (:result-mode :push) ,offset)
	    (:compile-form (:result-mode :eax) ,value)
	    (:popl :edx)		; offset
	    (:popl :ebx)		; index
	    (:popl :ecx)		; address
	    (:addl :edx :ecx)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	    (,prefixes :movl :eax (:ecx :ebx))))
	(:unsigned-byte8
	 `(with-inline-assembly (:returns :untagged-fixnum-eax)
	    (:compile-form (:result-mode :push) ,address)
	    (:compile-form (:result-mode :push) ,index)
	    (:compile-form (:result-mode :push) ,offset)
	    (:compile-form (:result-mode :eax) ,value)
	    (:popl :edx)		; offset
	    (:popl :ebx)		; index
	    (:popl :ecx)		; address
	    (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
	    (:addl :ebx :ecx)
	    (:addl :edx :ecx)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	    (,prefixes :movb :al (:ecx))))
	(:unsigned-byte16
	 (cond
	  ((eq 0 offset)
	   `(with-inline-assembly (:returns :untagged-fixnum-eax)
	      (:compile-form (:result-mode :push) ,address)
	      (:compile-form (:result-mode :push) ,index)
	      (:compile-form (:result-mode :eax) ,value)
	      (:popl :ebx)		; index
	      (:shrl #.movitz::+movitz-fixnum-shift+ :eax) ; scale value
	      (:popl :ecx)		; address
	      (:shll 1 :ebx)		; scale index
	      (:addl :ebx :ecx)
	      (:shrl #.movitz::+movitz-fixnum-shift+ :ecx) ; scale address
	      (,prefixes :movw :ax (:ecx))))
	  (t `(with-inline-assembly (:returns :untagged-fixnum-eax)
		(:compile-form (:result-mode :push) ,address)
		(:compile-form (:result-mode :push) ,index)
		(:compile-form (:result-mode :push) ,offset)
		(:compile-form (:result-mode :eax) ,value)
		(:popl :edx)		; offset
		(:popl :ebx)		; index
		(:popl :ecx)		; address
		(:shrl #.movitz::+movitz-fixnum-shift+ :eax) ; scale value
		(:leal (:ecx (:ebx 2)) :ecx)
		(:addl :edx :ecx)	;
		(:shrl #.movitz::+movitz-fixnum-shift+ :ecx) ; scale offset+address
		(,prefixes :movw :ax (:ecx))))))))))

(defun (setf memref-int) (value address offset index type &optional physicalp)
  (cond
   ((not physicalp)
    (ecase type
      (:unsigned-byte8
       (setf (memref-int address offset index :unsigned-byte8) value))
      (:unsigned-byte16
       (setf (memref-int address offset index :unsigned-byte16) value))))
   (physicalp
    (ecase type
      (:unsigned-byte8
       (setf (memref-int address offset index :unsigned-byte8 t) value))
      (:unsigned-byte16
       (setf (memref-int address offset index :unsigned-byte16 t) value))))))

(defun memcopy (object-1 object-2 offset index-1 index-2 count type)
  (ecase type
    ((:unsigned-byte8 :character)
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :edx) offset)
       (:compile-form (:result-mode :ecx) index-1)
       (:addl :edx :ecx)
       (:compile-form (:result-mode :eax) object-1)
       (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
       (:addl :ecx :eax)

       (:compile-form (:result-mode :ecx) index-2)
       (:addl :edx :ecx)
       (:compile-form (:result-mode :ebx) object-2)
       (:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
       (:addl :ecx :ebx)

       (:compile-form (:result-mode :ecx) count)
       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
       (:jz 'done)
       (:decl :eax)
       (:decl :ebx)
       loop
       (:movb (:ebx :ecx) :dl)
       (:movb :dl (:eax :ecx))
       (:decl :ecx)
       (:jnz 'loop)
       done))))
	     
;;;       (:shrl 4 :ecx)
;;;       (:jz 'quads-done)
;;;
;;;       quad-loop
;;;       (:movl (:ebx) :edx)
;;;       (:addl 4 :ebx)
;;;       (:movl :edx (:eax))
;;;       (:addl 4 :eax)
;;;       (:decl :ecx)
;;;       (:jnz 'quad-loop)
;;;       
;;;       quads-done
;;;       (:compile-form (:result-mode ) count :ecx)
;;;       (:shrl 2 :ecx)
;;;       (:andl 3 :ecx)
;;;       (:jz 'done)
;;;       loop
;;;       (:movb (:ebx :ecx) :dl)
;;;       (:movb :dl (:eax :ecx))
;;;       (:decl :ecx)
;;;       (:jnz 'loop)
;;;       done))))

(define-compiler-macro %copy-words (destination source count &optional (start1 0) (start2 0)
				    &environment env)
  (assert (= 4 movitz::+movitz-fixnum-factor+))
  (cond
   ((and (movitz:movitz-constantp start1 env)
	 (movitz:movitz-constantp start2 env))
    (let ((start1 (movitz::eval-form start1 env))
	  (start2 (movitz::eval-form start2 env)))
      `(with-inline-assembly-case ()
	 (do-case (t :eax :labels (done copy-loop no-fixnum))
	   (:compile-arglist () ,destination ,source ,count)
	   (:popl :edx)			; count
	   ,@(unless (= 0 start1)
	       `((:addl ,(* start1 movitz::+movitz-fixnum-factor+) :eax)))
	   (:testl :edx :edx)
	   (:jz 'done)
	   ,@(unless (= 0 start2)
	       `((:addl ,(* start2 movitz::+movitz-fixnum-factor+) :ebx)))
	   (:testb ,movitz::+movitz-fixnum-zmask+ :dl)
	   (:jnz '(:sub-program (no-fixnum) (:int 107)))
	  copy-loop
	   (:movl (:ebx :edx) :ecx)
	   (:movl :ecx (:eax :edx))
	   (:subl 4 :edx)
	   (:jnz 'copy-loop)
	  done))))
   (t `(with-inline-assembly-case ()
	 (do-case (t :eax :labels (done copy-loop no-fixnum))
	   (:compile-arglist () ,destination ,source ,count ,start1 ,start2)
	   (:popl :ecx)			; start2
	   (:addl :ecx :ebx)
	   (:popl :ecx)			; start1
	   (:addl :ecx :eax)
	   (:popl :edx)			; count
	   (:testl :edx :edx)
	   (:jz 'done)
	   (:testb ,movitz::+movitz-fixnum-zmask+ :dl)
	   (:jnz '(:sub-program (no-fixnum) (:int 107)))
	  copy-loop
	   (:movl (:ebx :edx) :ecx)
	   (:movl :ecx (:eax :edx))
	   (:subl 4 :edx)
	   (:jnz 'copy-loop)
	  done)))))

(defun %copy-words (destination source count &optional (start1 0) (start2 0))
  (%copy-words destination source count start1 start2))
