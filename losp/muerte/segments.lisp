;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      segments.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu May  8 14:25:06 2003
;;;;                
;;;; $Id: segments.lisp,v 1.19 2007/04/13 22:41:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/segments)

(in-package muerte)

(defvar *initial-segment-descriptor-table*)

(defun segment-register (segment-register-name)
  "Return the value of an x86 segment register, such as :cs or :ds."
  (declare (without-check-stack-limit))
  (macrolet ((sreg (reg)
	       `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		  (:xorl :ecx :ecx)
		  (:movw ,reg :cx))))
    (ecase segment-register-name
      (:ss (sreg :ss))
      (:cs (sreg :cs))
      (:ds (sreg :ds))
      (:es (sreg :es))
      (:fs (sreg :fs))
      (:gs (sreg :gs)))))

(defun (setf segment-register) (value segment-register-name)
  "This function indiscriminately sets a segment register,
which is a great way to crash the machine. So know what you're doing."
  (declare (without-check-stack-limit))
  (check-type value (unsigned-byte 16))
  (macrolet ((set-sreg (reg)
	       `(with-inline-assembly (:returns :nothing)
		  (:compile-form (:result-mode :ecx) value)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:movw :cx ,reg))))
    (ecase segment-register-name
      (:ss (set-sreg :ss))
      (:ds (set-sreg :ds))
      (:es (set-sreg :es))
      (:fs (set-sreg :fs))
      (:gs (set-sreg :gs))
      (:cs (without-interrupts
	     (with-inline-assembly (:returns :nothing)
	       (:load-lexical (:lexical-binding value) :untagged-fixnum-ecx)
	       (:declare-label-set jmp-table (jmp-target))
	       (:pushl :ecx)		; push selector
	       (:pushl (:esi (:offset movitz-funobj constant0) 'jmp-table))
	       (:jmp-segment (:esp))
	      jmp-target
	       (:popl :ecx)
	       (:popl :ecx))))))
  value)

(defun %sgdt ()
  "Return the location of the GDT, and the limit.
Error if the GDT location is not zero modulo 4."
  (declare (without-check-stack-limit))
  (eval-when (:compile-toplevel)
    (assert (= 4 movitz:+movitz-fixnum-factor+)))
  (without-interrupts
    (with-inline-assembly (:returns :multiple-values)
      (:std)
      (:pushl 0)
      (:pushl 0)
      (:leal (:esp 2) :ecx)
      (:sgdt (:ecx))
      (:popl :ebx)
      (:shrl #.(cl:- 16 movitz::+movitz-fixnum-shift+) :ebx)
      (:andl -4 :ebx)
      (:popl :eax)
      (:andl -4 :eax)
      (:cld)
      (:movl 2 :ecx)
      (:stc))))

(defun %lgdt (base-location limit)
  "Set the GDT according to base-location and limit.
This is the setter corresponding to the sgdt getter."
  (declare (without-check-stack-limit))
  (eval-when (:compile-toplevel)
    (assert (= 4 movitz:+movitz-fixnum-factor+)))
  (check-type base-location fixnum)
  (check-type limit positive-fixnum)
  (without-interrupts
    (with-inline-assembly (:returns :eax)
      (:compile-form (:result-mode :push) base-location)
      (:compile-form (:result-mode :push) limit)
      (:shll #.(cl:- 16 movitz:+movitz-fixnum-shift+) (:esp))
      (:leal (:esp 2) :ecx)
      (:lgdt (:ecx))
      (:popl :eax)
      (:popl :eax))))

;;;

(defun control-register (name)
  (macrolet ((creg (reg)
	       `(with-inline-assembly (:returns :untagged-fixnum-ecx)
		  (:movcr ,reg :ecx))))
    (ecase name
      (:cr0 (creg :cr0))
      (:cr2 (creg :cr2))
      (:cr3 (creg :cr3))
      (:cr4 (creg :cr4)))))

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

;;

(defun (setf global-segment-descriptor-table) (table)
  "Install <table> as the GDT.
NB! you need to ensure that the table object isn't garbage-collected."
  (check-type table (vector (unsigned-byte 32)))
  (let ((limit (1- (* 4 (length table))))
	(base (+ 2 (+ (object-location table)
		      (location-physical-offset)))))
    (%lgdt base limit)
    table))
    
(defun segment-descriptor-base-location (table selector)
  (check-type table (and vector (not simple-vector)))
  (eval-when (:compile-toplevel)
    (assert (= 4 movitz::+movitz-fixnum-factor+)))
  ;; XXX This fails for locations above 2GB.
  (let ((offset (+ (logand selector #xfff8)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (logior (ash (memref table (+ 7 offset) :type :unsigned-byte8)
		 22)
	    (ash (memref table (+ 4 offset) :type :unsigned-byte8)
		 14)
	    (ash (memref table (+ 2 offset) :type :unsigned-byte16)
		 -2))))

(defun (setf segment-descriptor-base-location) (base-location table selector)
  (check-type table (and vector (not simple-vector)))
  (eval-when (:compile-toplevel)
    (assert (= 4 movitz::+movitz-fixnum-factor+)))
  (let ((offset (+ (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (setf (memref table (+ 7 offset) :type :unsigned-byte8)
      (ldb (byte 8 22) base-location))
    (setf (memref table (+ 4 offset) :type :unsigned-byte8)
      (ldb (byte 8 14) base-location))
    (setf (memref table (+ 2 offset) :type :unsigned-byte16)
      (ash (ldb (byte 14 0) base-location) 2))
    base-location))

(defun segment-descriptor-limit (table selector)
  (check-type table (and vector (not simple-vector)))
  (let ((offset (+ (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (dpb (memref table (+ 6 offset) :type :unsigned-byte8)
	 (byte 4 16)
	 (memref table (+ 0 offset) :type :unsigned-byte16))))

(defun (setf segment-descriptor-limit) (limit table selector)
  (check-type table (and vector (not simple-vector)))
  (let ((offset (+ (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (setf (ldb (byte 4 0) (memref table (+ 6 offset) :type :unsigned-byte8))
          (ldb (byte 4 16) limit))
    (setf (memref table (+ 0 offset) :type :unsigned-byte16)
          (ldb (byte 16 0) limit))
    limit))

(defun segment-descriptor-type-s-dpl-p (table selector)
  "Access bits 40-47 of the segment descriptor."
  (check-type table (and vector (not simple-vector)))
  (memref table (+ 5 (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))
	  :type :unsigned-byte8))

(defun (setf segment-descriptor-type-s-dpl-p) (bits table selector)
  "Access bits 40-47 of the segment descriptor."
  (check-type table (and vector (not simple-vector)))
  (setf (memref table (+ 5 (logand #xfff8 selector)
			 (movitz-type-slot-offset 'movitz-basic-vector 'data))
		:type :unsigned-byte8)
    bits))
		   
(defun segment-descriptor-avl-x-db-g (table selector)
  "Access bits 52-55 of the segment descriptor."
  (check-type table (and vector (not simple-vector)))
  (ldb (byte 4 4)
       (memref table (+ 6 (logand #xfff8 selector)
			(movitz-type-slot-offset 'movitz-basic-vector 'data))
	       :type :unsigned-byte8)))

(defun (setf segment-descriptor-avl-x-db-g) (bits table selector)
  "Access bits 52-55 of the segment descriptor."
  (check-type table (and vector (not simple-vector)))
  (setf (ldb (byte 4 4)
	     (memref table (+ 6 (logand #xfff8 selector)
			      (movitz-type-slot-offset 'movitz-basic-vector 'data))
		     :type :unsigned-byte8))
    bits))

(defun segment-descriptor (table selector)
  "Access entire segment descriptor as a 64-bit integer."
  (check-type table (and vector (not simple-vector)))
  (let ((offset (+ (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (logior (ash (memref table offset :index 1 :type :unsigned-byte32)
		 32)
	    (ash (memref table offset :index 0 :type :unsigned-byte32)
		 0))))

(defun (setf segment-descriptor) (value table selector)
  "Access entire segment descriptor as a 64-bit integer."
  (check-type table (and vector (not simple-vector)))
  (let ((offset (+ (logand #xfff8 selector)
		   (movitz-type-slot-offset 'movitz-basic-vector 'data))))
    (setf (memref table offset :index 1 :type :unsigned-byte32)
      (ldb (byte 32 32) value))
    (setf (memref table offset :index 0 :type :unsigned-byte32)
      (ldb (byte 32 0) value))
    value))
  
(defun dump-global-segment-table (&key table entries nofill)
  "Dump contents of the current global (segment) descriptor table into a vector."
  (multiple-value-bind (gdt-base gdt-limit)
      (%sgdt)
    (let* ((gdt-entries (/ (1+ gdt-limit) 8))
	   (entries (or entries gdt-entries)))
      (check-type entries (integer 1 8192))
      (let ((table (or table
		       (make-array (* 2 entries)
				   :element-type '(unsigned-byte 32)
				   :initial-element 0))))
	(check-type table (vector (unsigned-byte 32)))
	(unless nofill
	  (loop for i upfrom 0 below (* 2 gdt-entries)
	      do (setf (aref table i)
		   (memref gdt-base 0 :index i :type :unsigned-byte32 :physicalp t))))
	table))))
