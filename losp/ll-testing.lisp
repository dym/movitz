;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ll-testing.lisp
;;;; Description:   low-level test code.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Apr 14 08:18:43 2005
;;;;                
;;;; $Id: ll-testing.lisp,v 1.12 2005/08/24 07:32:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :ll-testing)
(in-package muerte)

;;;(defun dump-global-segment-table (&key table entries nofill)
;;;  "Dump contents of the current global (segment) descriptor table into a vector."
;;;  (multiple-value-bind (gdt-base gdt-limit)
;;;      (%sgdt)
;;;    (let* ((gdt-entries (/ (1+ gdt-limit) 8))
;;;	   (entries (or entries gdt-entries)))
;;;      (check-type entries (integer 1 8192))
;;;      (let ((table (or table
;;;		       (make-array (* 2 entries)
;;;				   :element-type '(unsigned-byte 32)
;;;				   :initial-element 0))))
;;;	(check-type table (vector (unsigned-byte 32)))
;;;	(unless nofill
;;;	  (loop for i upfrom 0 below (* 2 gdt-entries)
;;;	      do (setf (aref table i)
;;;		   (memref gdt-base 0 :index i :type :unsigned-byte32 :physicalp t))))
;;;	table))))



(defmacro control-stack-fs (stack)
  `(stack-frame-ref ,stack 0 2))

(defmacro control-stack-esp (stack)
  `(stack-frame-ref ,stack 0 1))

(defmacro control-stack-ebp (stack)
  `(stack-frame-ref ,stack 0 0))

(defun control-stack-init (&optional (stack (make-array 254 :element-type '(unsigned-byte 32))))
  (let ((i (length stack)))
    (setf (control-stack-esp stack) i
	  (control-stack-ebp stack) 0)
    stack))

(defun control-stack-push (value stack &optional (type :lisp))
  (let ((i (decf (control-stack-esp stack))))
    (assert (< 1 i (length stack)))
    (setf (stack-frame-ref stack i 0 type) value)))

(defun control-stack-enter-frame (stack &optional function)
  (control-stack-push (control-stack-ebp stack) stack)
  (setf (control-stack-ebp stack) (control-stack-esp stack))
  (when function
    (check-type function function)
    (control-stack-push function stack))
  stack)

(defun stack-stopper (&rest args)
  (declare (ignore args))
  (declare (without-function-prelude))
  (error "Stack stop.")
  (format *terminal-io* "~&Stack-stopper halt.")
  (loop (halt-cpu)))

(defun alloc-context (segment-descriptor-table)
  (let* ((fs-index 8)
	 (thread (muerte::clone-run-time-context :name 'subthread)))
    (setf (segment-descriptor segment-descriptor-table fs-index)
      (segment-descriptor segment-descriptor-table (truncate (segment-register :fs) 8)))
    (warn "Thread ~S FS base: ~S"
	  thread
	  (setf (segment-descriptor-base-location segment-descriptor-table fs-index)
	    (+ (object-location thread)
	       (muerte::location-physical-offset))))
    (values thread (* 8 fs-index))))

(defun control-stack-bootstrap (stack function &rest args)
  (declare (dynamic-extent args))
  (check-type function function)
  (control-stack-init stack)
  (control-stack-push 0 stack)
  (control-stack-enter-frame stack #'stack-stopper)
  (let ((stack-top (+ (object-location stack) 2 (length stack)))
	(stack-bottom (+ (object-location stack) 2)))
    (dolist (arg (cddr args))
      (control-stack-push arg stack))
    (control-stack-push (+ 2 1 (object-location (funobj-code-vector #'stack-stopper)))
			stack)		; XXX The extra word skips the frame-setup.
    (multiple-value-bind (ebp esp)
	(control-stack-fixate stack)
      (stack-yield stack esp ebp
		   :eax (car args)
		   :ebx (cadr args)
		   :ecx (length args)
		   :esi function)))
  stack)

;;;(defun make-thread (&key (name (gensym "thread-")) (function #'invoke-debugger) (args '(nil)))
;;;  "Make a thread and initialize its stack to apply function to args."
;;;  (let* ((fs-index 8)			; a vacant spot in the global segment descriptor table..
;;;	 (fs (* 8 fs-index))
;;;	 (thread (muerte::clone-run-time-context :name name))
;;;	 (segment-descriptor-table (symbol-value 'muerte.init::*segment-descriptor-table*)))
;;;    (setf (segment-descriptor segment-descriptor-table fs-index)
;;;      (segment-descriptor segment-descriptor-table (truncate (segment-register :fs) 8)))
;;;    (setf (segment-descriptor-base-location segment-descriptor-table fs-index)
;;;      (+ (object-location thread) (muerte::location-physical-offset)))
;;;    (let ((cushion nil)
;;;	  (stack (control-stack-init-for-yield (make-array 4094 :element-type '(unsigned-byte 32))
;;;					       function args)))
;;;      (multiple-value-bind (ebp esp)
;;;	  (control-stack-fixate stack)
;;;	(setf (control-stack-fs stack) fs
;;;	      (control-stack-ebp stack) ebp
;;;	      (control-stack-esp stack) esp))
;;;      (setf (%run-time-context-slot 'dynamic-env thread) 0
;;;	    (%run-time-context-slot 'stack-vector thread) stack
;;;	    (%run-time-context-slot 'stack-top thread) (+ 2 (object-location stack)
;;;							  (length stack))
;;;	    (%run-time-context-slot 'stack-bottom thread) (+ (object-location stack) 2
;;;							     (or cushion
;;;								 (if (>= (length stack) 200)
;;;								     100
;;;								   0))))
;;;      (values thread))))

(defun stack-bootstrapper (&rest ignore)
  (declare (ignore ignore))
  (let ((frame (current-stack-frame)))
    (assert (eql 0 (stack-frame-uplink nil frame)))
    (let ((function (stack-frame-ref nil frame 1))
	  (args (stack-frame-ref nil frame 2)))
      (check-type function function)
      (check-type args list)
      (apply function args)))
  (error "Nothing left to do for ~S." (current-run-time-context))
  (format *terminal-io* "~&stack-bootstrapper halt.")
  (loop (halt-cpu)))

(defun control-stack-init-for-yield (stack function args)
  (check-type function function)
  (control-stack-init stack)
  (control-stack-push args stack)
  (control-stack-push function stack)
  (control-stack-enter-frame stack #'stack-bootstrapper)
  ;; Now pretend stack-bootstrapper called yield. First, the return address
  (control-stack-push (+ 2 2 (object-location (funobj-code-vector #'stack-bootstrapper)))
		      stack)		; XXX The extra 2 words skip the frame-setup,
					; XXX which happens to be 8 bytes..
  (control-stack-enter-frame stack #'yield)
  stack)
  

(defun yield (target-rtc &optional value)
  (declare (dynamic-extent values))
  (assert (not (eq target-rtc (current-run-time-context))))
  (let ((my-stack (%run-time-context-slot 'stack-vector))
	(target-stack (%run-time-context-slot 'stack-vector target-rtc)))
    (assert (not (eq my-stack target-stack)))
    (let ((fs (control-stack-fs target-stack))
	  (esp (control-stack-esp target-stack))
	  (ebp (control-stack-ebp target-stack)))
      (assert (location-in-object-p target-stack esp))
      (assert (location-in-object-p target-stack ebp))
      (assert (eq (stack-frame-funobj nil ebp)
		  (asm-register :esi)) ()
	"Will not yield to a non-yield frame.")
      ;; Push eflags for later..
      (setf (memref (decf esp) 0) (eflags))
      ;; Store EBP and ESP so we can get to them after the switch
      (setf (%run-time-context-slot 'scratch1 target-rtc) ebp
	    (%run-time-context-slot 'scratch2 target-rtc) esp)
      ;; Enable someone to yield back here..
      (setf (control-stack-fs my-stack) (segment-register :fs)
	    (control-stack-ebp my-stack) (asm-register :ebp)
	    (control-stack-esp my-stack) (asm-register :esp))
      (with-inline-assembly (:returns :eax)
	(:load-lexical (:lexical-binding fs) :untagged-fixnum-ecx)
	(:load-lexical (:lexical-binding value) :eax)
	(:cli)
	(:movw :cx :fs)
	(:locally (:movl (:edi (:edi-offset scratch1)) :ebp))
	(:locally (:movl (:edi (:edi-offset scratch2)) :esp))
	(:popfl)))))

(defun stack-yield (stack esp ebp &key eax ebx ecx edx esi eflags (dynamic-env 0) cushion)
  "Activate stack for the current run-time-context, and load the indicated CPU state.
EIP is loaded from ESI's code-vector."
  (assert (not (eq stack (%run-time-context-slot 'stack-vector))))
  (assert (location-in-object-p stack esp))
  (assert (location-in-object-p stack ebp))
  (assert (or (= 0 dynamic-env) (location-in-object-p stack dynamic-env)))
  (let ((stack-top (+ (object-location stack) 2 (length stack)))
	(stack-bottom (+ (object-location stack) 2
			 (or cushion
			     (if (>= (length stack) 200)
				 100
			       0)))))
    (with-inline-assembly (:returns :non-local-exit)
      (:clc)
      (:pushfl)
      (:popl :ebx)
      (:compile-form (:result-mode :eax) eflags)
      (:cmpl :edi :eax)
      (:je 'no-eflags-provided)
      (:movl :eax :ebx)
     no-eflags-provided
      (:locally (:movl :ebx (:edi (:edi-offset raw-scratch0)))) ; Keep eflags in raw-scratch0
      (:cli)				; Disable interrupts for a little while
      (:compile-form (:result-mode :eax) stack)
      (:locally (:movl :eax (:edi (:edi-offset stack-vector))))
      (:compile-form (:result-mode :eax) dynamic-env)
      (:locally (:movl :eax (:edi (:edi-offset dynamic-env))))
      (:compile-two-forms (:eax :ebx) stack-top stack-bottom)
      (:locally (:movl :eax (:edi (:edi-offset stack-top))))
      (:locally (:movl :ebx (:edi (:edi-offset stack-bottom))))

      (:compile-two-forms (:eax :ebx) esp ebp)
      (:locally (:movl :eax (:edi (:edi-offset scratch1))))
      (:locally (:movl :ebx (:edi (:edi-offset scratch2))))

      (:compile-form (:result-mode :untagged-fixnum-ecx) ecx)
      (:compile-two-forms (:eax :ebx) eax ebx)
      (:compile-two-forms (:edx :esi) edx esi)
      (:locally (:movl (:edi (:edi-offset scratch1)) :esp))
      (:locally (:movl (:edi (:edi-offset scratch2)) :ebp))
      (:locally (:pushl (:edi (:edi-offset raw-scratch0)))) ; reset eflags
      (:popfl)
      (:jmp (:esi (:offset movitz-funobj code-vector))))))



