;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromsoe, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      run-time-context.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov 12 18:33:02 2003
;;;;                
;;;; $Id: run-time-context.lisp,v 1.14 2004/09/27 08:54:53 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/run-time-context)

(in-package muerte)

(define-compiler-macro current-run-time-context ()
  `(with-inline-assembly (:returns :register)
     (:locally (:movl (:edi (:edi-offset self)) (:result-register)))))

(defun current-run-time-context ()
  (current-run-time-context))

(defun find-run-time-context-slot (context slot-name &optional (errorp t))
  (or (assoc slot-name (slot-value (class-of context) 'slot-map))
      (when errorp
	(error "No run-time-context slot named ~S in ~S." slot-name context))))

(defun %run-time-context-slot (slot-name &optional (context (current-run-time-context)))
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (word
       (memref context -6 (third slot) :lisp))
      (code-vector-word
       (memref context -6 (third slot) :code-vector))
      (lu32
       (memref context -6 (third slot) :unsigned-byte32)))))

(define-compiler-macro (setf %run-time-context-slot) (&whole form &environment env value slot-name
						      &optional (context '(current-run-time-context)))
  (if (not (and (movitz:movitz-constantp slot-name env)
		(equal context '(current-run-time-context))))
      form
    (let ((slot-name (movitz:movitz-eval slot-name env)))
      (ecase (bt:binary-slot-type 'movitz::movitz-run-time-context (intern (symbol-name slot-name) :movitz))
	(movitz:word
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :eax) ,value)
	    (:locally (:movl :eax (:edi (:edi-offset ,slot-name))))))
	(movitz:lu32
	 `(with-inline-assembly (:returns :untagged-fixnum-ecx)
	    (:compile-form (:result-mode :untagged-fixnum-ecx) ,value)
	    (:locally (:movl :ecx (:edi (:edi-offset ,slot-name))))))
	(movitz:code-vector-word
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :eax) ,value)
	    (:leal (:eax ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::data)) :ecx)
	    (:locally (:movl :ecx (:edi (:edi-offset ,slot-name))))))))))

(defun (setf %run-time-context-slot) (value slot-name &optional (context (current-run-time-context)))
  (check-type context run-time-context)
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (word
       (setf (memref context -6 (third slot) :lisp) value))
      (lu32
       (setf (memref context -6 (third slot) :unsigned-byte32) value))
      (code-vector-word
       (setf (memref context -6 (third slot) :code-vector) value)))))

(defun %run-time-context-segment-base (slot-name
				      &optional (context (current-run-time-context)))
  (check-type context run-time-context)
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (segment-descriptor
       (let ((index8 (* 4 (third slot)))
	     (index16 (* 2 (third slot))))
	 (+ (memref context (+ -6 2) index16 :unsigned-byte16)
	    (ash (memref context (+ -6 4) index8 :unsigned-byte8) 16)
	    (ash (memref context (+ -6 7) index8 :unsigned-byte8) 24)))))))

(defun (setf %run-time-context-segment-base) (value slot-name
					     &optional (context (current-run-time-context)))
  (check-type context run-time-context)
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (segment-descriptor
       (let ((index8 (* 4 (third slot)))
	     (index16 (* 2 (third slot))))
	 (setf (memref context (+ -6 2) index16 :unsigned-byte16) (ldb (byte 16 0) value)
	       (memref context (+ -6 4) index8 :unsigned-byte8) (ldb (byte 8 16) value)
	       (memref context (+ -6 7) index8 :unsigned-byte8) (ldb (byte 6 24) value)))))
    value))

(defun %run-time-context-ref (edi-offset)
  "Get a run-time-context slot by its EDI-relative offset."
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) edi-offset)
    (:leal (:eax #.(cl:* 1 movitz:+movitz-fixnum-factor+)) :ecx)
    (:sarl #.movitz:+movitz-fixnum-shift+ :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program ()
	    (:compile-form (:result-mode :ignore)
	     (error "Illegal edi-offset ~S" edi-offset))))
    (:locally (:movl (:edi :ecx -1) :eax))))

(defun clone-run-time-context (&key (parent (current-run-time-context))
				    (name :anonymous))
  (check-type parent run-time-context)
  (let ((context (%shallow-copy-object parent #.(movitz::movitz-type-word-size 'movitz-run-time-context))))
    (setf (%run-time-context-slot 'name context) name
	  (%run-time-context-slot 'self context) context)
    (setf (%run-time-context-segment-base 'segment-descriptor-thread-context context) 
      (+ (* #.movitz::+movitz-fixnum-factor+ (object-location context))
	 (%run-time-context-slot 'physical-address-offset)))
    context))

(defun switch-to-context (context)
  (check-type context run-time-context)
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :eax) context)
    (:movw #.(cl:1- (cl:* 8 8)) (:esp -6))
    (:addl #.(cl:+ -6 (movitz::global-constant-offset 'movitz::segment-descriptor-table))
	   :eax)
    (:addl :edi :eax)
    (:locally (:addl (:edi (:edi-offset physical-address-offset)) :eax))
    (:movl :eax (:esp -4))
    (:lgdt (:esp -6))
    (:movw #x28 :ax)
    (:movw :ax :fs)
    (:locally (:movl (:edi (:edi-offset self)) :eax))))

(defun %run-time-context-install-stack (context &optional (stack-vector
							   (make-array 8192 :element-type 'u32))
							  (cushion 1024))
  (check-type stack-vector vector)
  (assert (< cushion (array-dimension stack-vector 0)))
  (setf (%run-time-context-slot 'stack-vector context) stack-vector)
  (setf (%run-time-context-slot 'stack-top context)
    (+ (object-location stack-vector) 8
       (* 4 (array-dimension stack-vector 0))))
  (setf (%run-time-context-slot 'stack-bottom context)
    (+ (object-location stack-vector) 8
       (* 4 cushion)))
  stack-vector)
