;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      segments.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu May  8 14:25:06 2003
;;;;                
;;;; $Id: segments.lisp,v 1.2 2004/01/19 11:23:47 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/segments)

(in-package muerte)

(defun segment-register (segment-register)
  "Return the value of an x86 segment register, such as :cs or :ds."
  (macrolet ((sreg (reg)
	       `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		  (:xorl :ecx :ecx)
		  (:movw ,reg :cx))))
    (ecase segment-register
      (:ss (sreg :ss))
      (:cs (sreg :cs))
      (:ds (sreg :ds))
      (:es (sreg :es))
      (:fs (sreg :fs))
      (:gs (sreg :gs)))))

(defun (setf segment-register) (value segment-register)
  "This function indiscriminately sets a segment register,
which is a great way to crash the machine. So know what you're doing."
  (check-type value (unsigned-byte 16))
  (macrolet ((set-sreg (reg)
	       `(with-inline-assembly (:returns :nothing)
		  (:compile-form (:result-mode :ecx) value)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:movw :cx ,reg))))
    (ecase segment-register
      (:ss (set-sreg :ss))
      (:cs (set-sreg :cs))
      (:ds (set-sreg :ds))
      (:es (set-sreg :es))
      (:fs (set-sreg :fs))
      (:gs (set-sreg :gs))))
  value)

(defun sgdt ()
  (without-gc
   (with-inline-assembly (:returns :multiple-values)
     (:pushl 0)
     (:pushl 0)
     (:leal (:esp 2) :ecx)
     (:sgdt (:ecx))
     (:popl :ecx)
     ;; (:andl #xffff :ecx)
     (:shrl 16 :ecx)
     (:leal ((:ecx #.movitz::+movitz-fixnum-factor+)) :ebx)
     (:popl :ecx)
     (:leal ((:ecx #.movitz::+movitz-fixnum-factor+)) :eax)
     (:movl 2 :ecx)
     (:stc))))

;;;

(defun control-register-lo12 (name)
  "Return the low 12 bits of an x86 control register, such as :cr0 or :cr1."
  (macrolet ((creg (reg)
	       `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		  (:movcr ,reg :ecx)
		  (:andl #xfff :ecx))))
    (ecase name
      (:cr0 (creg :cr0))
      (:cr2 (creg :cr2))
      (:cr3 (creg :cr3))
      (:cr4 (creg :cr4)))))

(defun control-register-hi20 (name)
  "Return the high 20 bits of an x86 control register, such as :cr0 or :cr1."
  (macrolet ((creg (reg)
	       `(with-inline-assembly (:returns :ecx)
		  (:movcr ,reg :ecx)
		  (:andl #xfffff000 :ecx)
		  (:shrl #.(cl:- 12 movitz::+movitz-fixnum-shift+) :ecx))))
    (ecase name
      (:cr0 (creg :cr0))
      (:cr2 (creg :cr2))
      (:cr3 (creg :cr3))
      (:cr4 (creg :cr4)))))

(defun (setf control-register-lo12) (value name)
  "Set the low 12 bits of an x86 control register, such as :cr0 or :cr1."
  (macrolet ((set-creg (reg)
	       `(with-inline-assembly (:returns :nothing)
		  (:compile-form (:result-mode :eax) value)
		  (:movcr ,reg :ecx)
		  (:andl ,(cl:* movitz::+movitz-fixnum-factor+ #xfff) :eax)
		  (:andl #xfffff000 :ecx)
		  (:shrl ,movitz::+movitz-fixnum-shift+ :eax)
		  (:orl :eax :ecx)
		  (:movcr :ecx ,reg))))
    (ecase name
      (:cr0 (set-creg :cr0))
      (:cr2 (set-creg :cr2))
      (:cr3 (set-creg :cr3))
      (:cr4 (set-creg :cr4)))
    value))

(defun (setf control-register-hi20) (value name)
  "Set the high 20 bits of an x86 control register, such as :cr0 or :cr1."
  (macrolet ((set-creg (reg)
	       `(with-inline-assembly (:returns :nothing)
		  (:compile-form (:result-mode :eax) value)
		  (:movcr ,reg :ecx)
		  (:shll ,(- 12 movitz::+movitz-fixnum-shift+) :eax)
		  (:andl #xfff :ecx)
		  (:andl #xfffff000 :eax)
		  (:orl :eax :ecx)
		  (:movcr :ecx ,reg))))
    (ecase name
      (:cr0 (set-creg :cr0))
      (:cr2 (set-creg :cr2))
      (:cr3 (set-creg :cr3))
      (:cr4 (set-creg :cr4)))
    value))
    
  
