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
;;;; $Id: bignums.lisp,v 1.1 2004/07/17 19:30:09 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(require :muerte/arithmetic-macros)
(provide :muerte/bignums)

(in-package muerte)

(defun %bignum-bigits (x)
  (%bignum-bigits x))

(defun %bignum-canonicalize (x)
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
		   (:int 107)))
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
	    (:jnz '(:sub-program () (:int 107)))
	    (:testw :cx :cx)
	    (:jz '(:sub-program () (:int 107)))
	    (:movw :cx (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::length)))
	   done
	    )))
    (do-it)))

(defun copy-bignum (old)
  (check-type old bignum)
  (let* ((length (%bignum-bigits old))
	 (new (malloc-non-pointer-words (1+ length))))
    (with-inline-assembly (:returns :eax)
      (:compile-two-forms (:eax :ebx) new old)
      (:compile-form (:result-mode :edx) length)
     copy-bignum-loop
      (:movl (:ebx :edx #.movitz:+other-type-offset+) :ecx)
      (:movl :ecx (:eax :edx #.movitz:+other-type-offset+))
      (:subl 4 :edx)
      (:jnc 'copy-bignum-loop))))

(defun %make-bignum (bigits)
  (assert (plusp bigits))
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:compile-two-forms (:eax :ecx) (malloc-non-pointer-words (1+ bigits)) bigits)
	    (:shll 16 :ecx)
	    (:orl ,(movitz:tag :bignum 0) :ecx)
	    (:movl :ecx (:eax ,movitz:+other-type-offset+))
	    )))
    (do-it)))

(defun print-bignum (x)
  (check-type x bignum)
  (dotimes (i (1+ (%bignum-bigits x)))
    (format t "~8,'0X " (memref x -6 i :unsigned-byte32)))
  (terpri)
  (values))

(defun %bignum-addf-fixnum (bignum delta)
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

(defun %bignum-addf (bignum delta)
  "Destructively add (abs delta) to bignum."
  (check-type bignum bignum)
  (etypecase delta
    (positive-fixnum
     (%bignum-addf-fixnum bignum delta))
    (negative-fixnum
     (%bignum-addf-fixnum bignum (- delta)))
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
	       (:cmpw :dx (:eax (:offset movitz-bignum length)))
	       (:jbe '(:sub-program (overflow) (:int 4)))
	       (:addl (:ebx :edx (:offset movitz-bignum :bigit0))
		      :ecx)
	       (:jz 'carry+digit-overflowed) ; If CF=1, then ECX=0.
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

