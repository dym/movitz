;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      bignums.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Jul 17 19:42:57 2004
;;;;                
;;;; $Id: bignums.lisp,v 1.12 2004/10/11 13:52:21 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(require :muerte/arithmetic-macros)
(provide :muerte/bignums)

(in-package muerte)

(defun %bignum-bigits (x)
  (%bignum-bigits x))

(defun bignum-canonicalize (x)
  "Assuming x is a bignum, return the canonical integer value. That is,
either return a fixnum, or destructively modify the bignum's length so
that the msb isn't zero. DO NOT APPLY TO NON-BIGNUM VALUES!"
  (check-type x bignum)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:load-lexical (:lexical-binding x) :eax)
	    (:movl (:eax ,movitz:+other-type-offset+) :ecx)
	    (:shrl 16 :ecx)
	    (:jz '(:sub-program (should-never-happen)
		   (:int 63)))
	   shrink-loop
	    (:cmpl 4 :ecx)
	    (:je 'shrink-no-more)
	    (:cmpl 0 (:eax :ecx ,(+ -4 (bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0))))
	    (:jnz 'shrink-done)
	    (:subl 4 :ecx)
	    (:jmp 'shrink-loop)
	   shrink-no-more
	    (:cmpl ,(1+ movitz:+movitz-most-positive-fixnum+)
		   (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0)))
	    (:jc '(:sub-program (fixnum-result)
		   (:movl (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0))
		    :ecx)
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
		   (:jmp 'done)))
	   shrink-done
	    (:testb 3 :cl)
	    (:jnz '(:sub-program () (:int 63)))
	    (:testw :cx :cx)
	    (:jz '(:sub-program () (:int 63)))
	    (:movw :cx (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::length)))
	   done
	    )))
    (do-it)))

(defun copy-bignum (old)
  (check-type old bignum)
  (%shallow-copy-object old (1+ (%bignum-bigits old))))

(defun %make-bignum (bigits)
  (assert (plusp bigits))
  (macrolet
      ((do-it ()
	 `(let ((words (1+ bigits)))
	    (with-non-pointer-allocation-assembly (words :fixed-size-p t
							 :object-register :eax)
	      (:load-lexical (:lexical-binding bigits) :ecx)
	      (:shll 16 :ecx)
	      (:orl ,(movitz:tag :bignum 0) :ecx)
	      (:movl :ecx (:eax (:offset movitz-bignum type)))))))
    (do-it)))

(defun print-bignum (x)
  (check-type x bignum)
  (dotimes (i (1+ (%bignum-bigits x)))
    (format t "~8,'0X " (memref x -6 :index i :type :unsigned-byte32)))
  (terpri)
  (values))

(defun bignum-add-fixnum (bignum delta)
  "Non-destructively add an unsigned fixnum delta to an (unsigned) bignum."
  (check-type bignum bignum)
  (check-type delta fixnum)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax :labels (not-size1
							copy-bignum-loop
							add-bignum-loop
							add-bignum-done
							no-expansion
							pfix-pbig-done))
	    (:compile-two-forms (:eax :ebx) bignum delta)
	    (:testl :ebx :ebx)
	    (:jz 'pfix-pbig-done)	; EBX=0 => nothing to do.
	    (:movzxw (:eax (:offset movitz-bignum length)) :ecx)
	    (:cmpl ,movitz:+movitz-fixnum-factor+ :ecx)
	    (:jne 'not-size1)
	    (:compile-form (:result-mode :ecx) delta)
	    (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	    (:addl (:eax (:offset movitz-bignum bigit0)) :ecx)
	    (:jc 'not-size1)
	    (:call-local-pf box-u32-ecx)
	    (:jmp 'pfix-pbig-done)

	   not-size1
	    ;; Set up atomically continuation.
	    (:declare-label-set restart-jumper (restart-addition))
	    (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
	    (:pushl 'restart-jumper)
	    ;; ..this allows us to detect recursive atomicallies.
	    (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
	    (:pushl :ebp)
	   restart-addition

	    (:movl (:esp) :ebp)
	    (:compile-form (:result-mode :eax) bignum)
	    (:movzxw (:eax (:offset movitz-bignum length)) :ecx)

	    (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
	    ;; Now inside atomically section.
	    (:leal ((:ecx 1) ,(* 2 movitz:+movitz-fixnum-factor+))
		   :eax)		; Number of words
	    (:call-local-pf get-cons-pointer)
	    (:load-lexical (:lexical-binding bignum) :ebx) ; bignum
	    (:movzxw (:ebx (:offset movitz-bignum length)) :ecx)
	    (:leal ((:ecx 1) ,movitz:+movitz-fixnum-factor+)
		   :edx)
	    (:movl 0 (:eax :edx ,movitz:+other-type-offset+)) ; MSB
	   copy-bignum-loop
	    (:subl ,movitz:+movitz-fixnum-factor+ :edx)
	    (:movl (:ebx :edx ,movitz:+other-type-offset+) :ecx)
	    (:movl :ecx (:eax :edx ,movitz:+other-type-offset+))
	    (:jnz 'copy-bignum-loop)

	    (:load-lexical (:lexical-binding delta) :ecx)
	    (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	    (:xorl :ebx :ebx)
	    (:addl :ecx (:eax (:offset movitz-bignum bigit0)))
	    (:jnc 'add-bignum-done)
	   add-bignum-loop
	    (:addl 4 :ebx)
	    (:addl 1 (:eax :ebx (:offset movitz-bignum bigit0)))
	    (:jc 'add-bignum-loop)
	   add-bignum-done
	    (:movzxw (:eax (:offset movitz-bignum length)) :ecx)
	    (:leal ((:ecx 1) ,movitz:+movitz-fixnum-factor+) :ecx)
	    (:cmpl 0 (:eax :ecx (:offset movitz-bignum bigit0 -4)))
	    (:je 'no-expansion)
	    (:addl #x40000 (:eax ,movitz:+other-type-offset+))
	    (:addl ,movitz:+movitz-fixnum-factor+ :ecx)
	   no-expansion
	    (:call-local-pf cons-commit)
	    ;; Exit atomically block.
	    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	    (:leal (:esp 16) :esp)
	    
	   pfix-pbig-done)))
    (do-it)))

(defun bignum-addf-fixnum (bignum delta)
  "Destructively add a fixnum delta (negative or positive) to an (unsigned) bignum."
  (check-type delta fixnum)
  (check-type bignum bignum)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax :labels (add-bignum-loop add-bignum-done))
	    (:load-lexical (:lexical-binding delta) :ecx)
	    (:load-lexical (:lexical-binding bignum) :eax)
	    (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)) :ebx) ; length
	    (:xorl :edx :edx)		; counter
	    (:sarl ,movitz:+movitz-fixnum-shift+ :ecx)
	    (:jns 'positive-delta)
	    ;; negative-delta
	    (:negl :ecx)
	    (:subl :ecx (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
	    (:jnc 'add-bignum-done)
	   sub-bignum-loop
	    (:addl 4 :edx)
	    (:cmpl :edx :ebx)
	    (:je '(:sub-program (overflow) (:int 4)))
	    (:subl 1 (:eax :edx ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
	    (:jc 'sub-bignum-loop)
	    (:jmp 'add-bignum-done)
	    
	   positive-delta
	    (:addl :ecx (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
	    (:jnc 'add-bignum-done)
	   add-bignum-loop
	    (:addl 4 :edx)
	    (:cmpl :edx :ebx)
	    (:je '(:sub-program (overflow) (:int 4)))
	    (:addl 1 (:eax :edx ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
	    (:jc 'add-bignum-loop)
	   add-bignum-done)))
    (do-it)))

(defun bignum-addf (bignum delta)
  "Destructively add (abs delta) to bignum."
  (check-type bignum bignum)
  (etypecase delta
    (positive-fixnum
     (bignum-addf-fixnum bignum delta))
    (negative-fixnum
     (bignum-addf-fixnum bignum (- delta)))
    (bignum
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	      not-size1
	       (:load-lexical (:lexical-binding bignum) :eax) ; EAX = bignum
	       (:load-lexical (:lexical-binding delta) :ebx) ;  EBX = delta
	       (:xorl :edx :edx)	; Counter
	       (:xorl :ecx :ecx)	; Carry
	      add-bignum-loop
	       (:addl (:ebx :edx (:offset movitz-bignum :bigit0))
		      :ecx)
	       (:jz 'carry+digit-overflowed) ; If CF=1, then ECX=0.
	       (:cmpw :dx (:eax (:offset movitz-bignum length)))
	       (:jbe '(:sub-program (overflow) (:int 4)))
	       (:addl :ecx (:eax :edx (:offset movitz-bignum bigit0)))
	      carry+digit-overflowed
	       (:sbbl :ecx :ecx)
	       (:negl :ecx)		; ECX = Add's Carry.
	       (:addl 4 :edx)
	       (:cmpw :dx (:ebx (:offset movitz-bignum length)))
	       (:ja 'add-bignum-loop)
	       ;; Now, if there's a carry we must propagate it.
	       (:jecxz 'add-bignum-done)
	      carry-propagate-loop
	       (:cmpw :dx (:eax (:offset movitz-bignum length)))
	       (:jbe '(:sub-program (overflow) (:int 4)))
	       (:addl 4 :edx)
	       (:addl 1 (:eax :edx (:offset movitz-bignum bigit0 -4)))
	       (:jc 'carry-propagate-loop)
	      add-bignum-done)))
       (do-it)))))

(defun bignum-subf (bignum delta)
  "Destructively subtract (abs delta) from bignum."
  (check-type bignum bignum)
  (etypecase delta
    (positive-fixnum
     (bignum-addf-fixnum bignum (- delta)))
    (negative-fixnum
     (bignum-addf-fixnum bignum delta))
    (bignum
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	      not-size1
	       (:load-lexical (:lexical-binding bignum) :eax) ; EAX = bignum
	       (:load-lexical (:lexical-binding delta) :ebx) ;  EBX = delta
	       (:xorl :edx :edx)	; Counter
	       (:xorl :ecx :ecx)	; Carry
	      sub-bignum-loop
	       (:cmpw :dx (:eax (:offset movitz-bignum length)))
	       (:jbe '(:sub-program (overflow) (:int 4)))
	       (:addl (:ebx :edx (:offset movitz-bignum :bigit0))
		      :ecx)
	       (:jz 'carry+digit-overflowed) ; If CF=1, then ECX=0.
	       (:subl :ecx (:eax :edx (:offset movitz-bignum bigit0)))
	      carry+digit-overflowed
	       (:sbbl :ecx :ecx)
	       (:negl :ecx)		; ECX = Add's Carry.
	       (:addl 4 :edx)
	       (:cmpw :dx (:ebx (:offset movitz-bignum length)))
	       (:ja 'sub-bignum-loop)
	       ;; Now, if there's a carry we must propagate it.
	       (:jecxz 'sub-bignum-done)
	      carry-propagate-loop
	       (:cmpw :dx (:eax (:offset movitz-bignum length)))
	       (:jbe '(:sub-program (overflow) (:int 4)))
	       (:addl 4 :edx)
	       (:subl 1 (:eax :edx (:offset movitz-bignum bigit0 -4)))
	       (:jc 'carry-propagate-loop)
      sub-bignum-done)))
       (do-it)))))

(defun bignum-shift-rightf (bignum count)
  "Destructively right-shift bignum by count bits."
  (check-type bignum bignum)
  (check-type count positive-fixnum)
  (multiple-value-bind (long-shift short-shift)
      (truncate count 32)
    (macrolet
	((do-it ()
	   `(with-inline-assembly (:returns :ebx)
	      (:compile-two-forms (:edx :ebx) long-shift bignum)
	      (:xorl :eax :eax)
	     shift-long-loop
	      (:cmpw :dx (:ebx (:offset movitz-bignum length)))
	      (:jbe 'zero-msb-loop)
	      (:movl (:ebx :edx (:offset movitz-bignum bigit0)) :ecx)
	      (:movl :ecx (:ebx :eax (:offset movitz-bignum bigit0)))
	      (:addl 4 :eax)
	      (:addl 4 :edx)
	      (:jmp 'shift-long-loop)
	     zero-msb-loop
	      (:cmpw :ax (:ebx (:offset movitz-bignum length)))
	      (:jbe 'long-shift-done)
	      (:movl 0 (:ebx :eax (:offset movitz-bignum bigit0)))
	      (:addl 4 :eax)
	      (:jmp 'zero-msb-loop)
	     long-shift-done
	      (:compile-form (:result-mode :ecx) short-shift)
	      (:xorl :edx :edx)		; counter
	      (:xorl :eax :eax)		; We need to use EAX for u32 storage.
	      (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	      (:std)
	     shift-short-loop
	      (:addl 4 :edx)
	      (:cmpw :dx (:ebx (:offset movitz-bignum length)))
	      (:jbe 'end-shift-short-loop)
	      (:movl (:ebx :edx (:offset movitz-bignum bigit0))
		     :eax)
	      (:shrdl :cl :eax
		      (:ebx :edx (:offset movitz-bignum bigit0 -4)))
	      (:jmp 'shift-short-loop)
	     end-shift-short-loop
	      (:movl :edx :eax)		; Safe EAX
	      (:shrl :cl (:ebx :edx (:offset movitz-bignum bigit0 -4)))
	      (:cld))))
      (do-it))))

(defun bignum-shift-leftf (bignum count)
  "Destructively left-shift bignum by count bits."
  (check-type bignum bignum)
  (check-type count positive-fixnum)
  (multiple-value-bind (long-shift short-shift)
      (truncate count 32)
    (macrolet
	((do-it ()
	   `(with-inline-assembly (:returns :ebx)
	      (:compile-two-forms (:ecx :ebx) long-shift bignum)
	      (:jecxz 'long-shift-done)
	      (:xorl :eax :eax)
	      (:movw (:ebx (:offset movitz-bignum length)) :ax)
	      (:subl 4 :eax)		; destination pointer
	      (:movl :eax :edx)
	      ;; Overflow check
	     overflow-check-loop
	      (:cmpl 0 (:ebx :edx (:offset movitz-bignum bigit0)))
	      (:jne '(:sub-program (overflow) (:int 4)))
	      (:subl 4 :edx)
	      (:subl 4 :ecx)
	      (:jnz 'overflow-check-loop)
	      ;; (:subl :ecx :edx)		; source = EDX = (- dest long-shift)
	      (:jc '(:sub-program (overflow) (:int 4)))
	     shift-long-loop
	      (:movl (:ebx :edx (:offset movitz-bignum bigit0)) :ecx)
	      (:movl :ecx (:ebx :eax (:offset movitz-bignum bigit0)))
	      (:subl 4 :eax)
	      (:subl 4 :edx)
	      (:jnc 'shift-long-loop)
	     zero-lsb-loop
	      (:movl 0 (:ebx :eax (:offset movitz-bignum bigit0))) ; EDX=0
	      (:subl 4 :eax)
	      (:jnc 'zero-lsb-loop)
	      
	     long-shift-done
	      (:compile-form (:result-mode :ecx) short-shift)
	      (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	      (:jz 'done)
	      (:xorl :esi :esi)		; counter
	      (:movw (:ebx (:offset movitz-bignum length)) :si)
	      (:subl 4 :esi)
	      (:jz 'shift-short-lsb)
	      (:xorl :eax :eax)
	      (:std)
	      ;; Overflow check
	      (:movl (:ebx :esi (:offset movitz-bignum bigit0))
		     :eax)
	      (:xorl :edx :edx)
	      (:shldl :cl :eax :edx)
	      (jnz 'overflow)
	     shift-short-loop
	      (:movl (:ebx :esi (:offset movitz-bignum bigit0 -4))
		     :eax)
	      (:shldl :cl :eax (:ebx :esi (:offset movitz-bignum bigit0)))
	      (:subl 4 :esi)
	      (:jnz 'shift-short-loop)
	      (:movl :edi :edx)
	      (:movl :edi :eax)		; Safe EAX
	      (:cld)
	      (:movl (:ebp -4) :esi)
	     shift-short-lsb
	      (:shll :cl (:ebx (:offset movitz-bignum bigit0)))
	     done
	      )))
      (do-it))))

(defun bignum-mulf (bignum factor)
  "Destructively multiply bignum by (abs factor)."
  (check-type bignum bignum)
  (etypecase factor
    (bignum
     (error "not yet"))
    (negative-fixnum
     (bignum-mulf bignum (- factor)))
    (positive-fixnum
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :ebx)
	       (:load-lexical (:lexical-binding bignum) :ebx) ; bignum
	       (:compile-form (:result-mode :ecx) factor)
	       (:sarl ,movitz:+movitz-fixnum-shift+ :ecx)
	       (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0))))
	       (:xorl :esi :esi)	; Counter (by 4)
	       (:xorl :edx :edx)	; Initial carry
	       (:std)			; Make EAX, EDX non-GC-roots.
	      multiply-loop
	       (:movl (:ebx :esi (:offset movitz-bignum bigit0))
		      :eax)
	       (:movl :edx :ecx)	; Save carry in ECX
	       (:locally (:mull (:edi (:edi-offset raw-scratch0)) :eax :edx)) ; EDX:EAX = scratch0*EAX
	       (:addl :ecx :eax)	; Add carry
	       (:adcl 0 :edx)		; Compute next carry
	       (:jc '(:sub-program (should-not-happen) (:int 63)))
	       (:movl :eax (:ebx :esi (:offset movitz-bignum bigit0)))
	       (:addl 4 :esi)
	       (:cmpw :si (:ebx (:offset movitz-bignum length)))
	       (:ja 'multiply-loop)
	       (:movl :edx :ecx)	; Carry into ECX
	       (:movl :edi :eax)
	       (:movl :edi :edx)
	       (:cld)
	       (:movl (:ebp -4) :esi)
	       (:testl :ecx :ecx)	; Carry overflow?
	       (:jnz '(:sub-program (overflow) (:int 4)))
	       )))
       (do-it)))))

(defun bignum-truncatef (bignum divisor)
  (etypecase divisor
    (positive-fixnum
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :ebx)
	       (:compile-two-forms (:ebx :ecx) bignum divisor)
	       (:xorl :edx :edx)	; hi-digit
	       (:sarl ,movitz:+movitz-fixnum-shift+ :ecx)
	       (:xorl :esi :esi)	; ESI is counter by 4
	       (:movw (:ebx (:offset movitz-bignum length)) :si)
	       (:std)
	      divide-loop
	       (:movl (:ebx :esi (:offset movitz-bignum bigit0 -4))
		      :eax)		; lo-digit
	       (:divl :ecx :eax :edx)	; EDX:EAX = EDX:EAX/ECX
	       (:movl :eax (:ebx :esi (:offset movitz-bignum bigit0 -4)))
	       (:subl 4 :esi)
	       (:jnz 'divide-loop)

	       (:movl (:ebp -4) :esi)
	       (:movl :edi :edx)
	       (:movl :ebx :eax)
	       (:cld))))
       (do-it)))))

(defun bignum-set-zerof (bignum)
  (check-type bignum bignum)
  (dotimes (i (%bignum-bigits bignum))
    (setf (memref bignum (movitz-type-slot-offset 'movitz-bignum 'bigit0)
		  :index i :type :unsigned-byte32) 0))
  bignum)

(defun %bignum= (x y)
  (check-type x bignum)
  (check-type y bignum)
  (compiler-macro-call %bignum= x y))

(defun %bignum< (x y)
  (check-type x bignum)
  (check-type y bignum)
  (compiler-macro-call %bignum< x y))

(defun %bignum-zerop (x)
  (compiler-macro-call %bignum-zerop x))

(defun bignum-integer-length (x)
  "Compute (integer-length (abs x))."
  (check-type x bignum)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :ebx) x)
	    (:movzxw (:ebx (:offset movitz-bignum length))
		     :edx)
	    (:xorl :eax :eax)
	   bigit-scan-loop
	    (:subl 4 :edx)
	    (:jc 'done)
	    (:cmpl 0 (:ebx :edx (:offset movitz-bignum bigit0)))
	    (:jz 'bigit-scan-loop)
	    ;; Now, EAX must be loaded with (+ (* EDX 32) bit-index 1).
	    (:leal ((:edx 8)) :eax)	; Factor 8
	    (:bsrl (:ebx :edx (:offset movitz-bignum bigit0))
		   :ecx)
	    (:leal ((:eax 4)) :eax)	; Factor 4
	    (:leal ((:ecx 4) :eax 4) :eax)
	   done)))
    (do-it)))

(defun bignum-logcount (x)
  "Compute (logcount (abs x))."
  (check-type x bignum)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :ebx) x)
	    (:xorl :eax :eax)
	    (:xorl :edx :edx)
	    (:movw (:ebx (:offset movitz-bignum length)) :dx)
	   word-loop
	    (:movl (:ebx :edx (:offset movitz-bignum bigit0 -4)) :ecx)
	   bit-loop
	    (:jecxz 'end-bit-loop)
	    (:shrl 1 :ecx)
	    (:jnc 'bit-loop)
	    (:addl ,movitz:+movitz-fixnum-factor+ :eax)
	    (:jmp 'bit-loop)
	   end-bit-loop
	    (:subl 4 :edx)
	    (:jnz 'word-loop))))
    (do-it)))

(defun %bignum-negate (x)
  (compiler-macro-call %bignum-negate x))

(defun %bignum-plus-fixnum-size (x fixnum-delta)
  (compiler-macro-call %bignum-plus-fixnum-size x fixnum-delta))
