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
;;;; $Id: ll-testing.lisp,v 1.4 2005/04/26 22:23:14 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :ll-testing)
(in-package muerte)

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

(defun install-global-segment-table (table &optional entries)
  "Install <table> as the GDT.
NB! ensure that the table object isn't garbage-collected."
  (check-type table (vector (unsigned-byte 32)))
  (let ((entries (or entries (truncate (length table) 2))))
    (check-type entries (integer 0 *))
    (let ((limit (1- (* 8 entries)))
	  (base (+ 2 (+ (object-location table)
			(location-physical-offset)))))
      (%lgdt base limit)
      (values table limit))))


(defun format-segment-table (table &key (start 0) (end (truncate (length table) 2)))
  (loop for i from start below end
      do (format t "~&~2D: base: #x~8,'0X, limit: #x~5,'0X, type-s-dpl-p: ~8,'0b, avl-x-db-g: ~4,'0b~%"
		 i
		 (* 4 (segment-descriptor-base-location table i))
		 (segment-descriptor-limit table i)
		 (segment-descriptor-type-s-dpl-p table i)
		 (segment-descriptor-avl-x-db-g table i)))
  (values))



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

(defun control-stack-fixate (stack)
  (let ((stack-base (+ 2 (object-location stack))))
    (do ((frame (control-stack-ebp stack)))
	((zerop (stack-frame-uplink stack frame)))
      (assert (typep (stack-frame-funobj stack frame) 'function))
      (let ((previous-frame frame))
	(setf frame (stack-frame-uplink stack frame))
	(incf (stack-frame-ref stack previous-frame 0)
	      stack-base)))
    (values (+ (control-stack-ebp stack) stack-base)
	    (+ (control-stack-esp stack) stack-base))))	       

(defun make-thread (segment-descriptor-table)
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

(defun test-tt ()
  (multiple-value-bind (thread stack)
      (muerte.init::threading)
    (control-stack-bootstrap stack #'format t "Hello world!")))

(defun test-tr (function &rest args)
  (declare (dynamic-extent args))
  (assert (= 2 (length args)))
  (multiple-value-bind (thread fs)
      (make-thread muerte.init::*segment-descriptor-table*)
    (let ((cushion nil)
	  (stack (control-stack-init-for-yield (make-array 4094 :element-type '(unsigned-byte 32))
					       function args)))
      (multiple-value-bind (ebp esp)
	  (control-stack-fixate stack)
	(setf (control-stack-ebp stack) ebp
	      (control-stack-esp stack) esp))
      (setf (%run-time-context-slot 'dynamic-env thread) 0
	    (%run-time-context-slot 'stack-vector thread) stack
	    (%run-time-context-slot 'stack-top thread) (+ 2 (object-location stack)
							  (length stack))
	    (%run-time-context-slot 'stack-bottom thread) (+ (object-location stack) 2
							     (or cushion
								 (if (>= (length stack) 200)
								     100
								   0))))
      (values thread fs stack))))

(defun stack-bootstrapper (&rest args)
  (declare (ignore args))
  (with-inline-assembly (:returns :nothing) (:break))
  (let ((frame (current-stack-frame)))
    (assert (eql 0 (stack-frame-uplink nil frame)))
    (let ((function (stack-frame-ref nil frame 1))
	  (numargs (stack-frame-ref nil frame 2)))
      (warn "[~S] bootstrapping function ~S with ~D args." frame function numargs)
      (check-type function function)
      (check-type numargs (integer 0 #xffff))
      (with-inline-assembly (:returns :multiple-values)
	(:load-lexical (:lexical-binding function) :esi)
	(:movl (:ebp #x0c) :eax)
	(:movl (:ebp #x10) :ebx)
	(:call (:esi (:offset movitz-funobj code-vector%2op))))))
  (error "Stack bootstrapper stop.")
  (format *terminal-io* "~&stack-bootstrapper halt.")
  (loop (halt-cpu)))

(defun control-stack-init-for-yield (stack function args)
  (check-type function function)
  (control-stack-init stack)
  (control-stack-push (second args) stack)
  (control-stack-push (first args) stack)
  (control-stack-push (length args) stack)
  (control-stack-push function stack)
  (control-stack-enter-frame stack #'stack-bootstrapper)
  ;; Now pretend stack-bootstrapper called yield. First, the return address
  (control-stack-push (+ 2 2 (object-location (funobj-code-vector #'stack-bootstrapper)))
		      stack)		; XXX The extra 2 words skip the frame-setup,
					; XXX which happens to be 8 bytes..
  (control-stack-enter-frame stack #'yield)
  (control-stack-push 0 stack)		; XXX shouldn't need this?
  stack)
  

(defun yield (target-rtc fs)
  (assert (not (eq target-rtc (current-run-time-context))))
  (let ((my-stack (%run-time-context-slot 'stack-vector))
	(target-stack (%run-time-context-slot 'stack-vector target-rtc)))
    (assert (not (eq my-stack target-stack)))
    (let ((esp (control-stack-esp target-stack))
	  (ebp (control-stack-ebp target-stack)))
      (assert (location-in-object-p target-stack esp))
      (assert (location-in-object-p target-stack ebp))
      (assert (eq (memref ebp -4) (asm-register :esi)) ()
	"Cannot yield to a non-yield frame.")
      ;; Push eflags for later..
      (setf (memref (decf esp) 0) (eflags))
      ;; Enable someone to yield back here..
      (setf (control-stack-ebp my-stack) (asm-register :ebp)
	    (control-stack-esp my-stack) (asm-register :esp))
      (with-inline-assembly (:returns :nothing)
	(:cli)
	(:load-lexical (:lexical-binding fs) :untagged-fixnum-ecx)
	(:movw :cx :fs)
	(:load-lexical (:lexical-binding ebp) :eax)
	(:load-lexical (:lexical-binding esp) :ebx)
	(:movl :eax :ebp)
	(:movl :ebx :esp)
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

