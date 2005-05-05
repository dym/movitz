;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      threading.lisp
;;;; Description:   A basic threading library.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Apr 28 08:30:01 2005
;;;;                
;;;; $Id: threading.lisp,v 1.2 2005/05/05 15:21:59 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :lib/threading)

(defpackage threading
  (:use cl muerte)
  (:export thread
	   make-thread
	   yield
	   ))

(in-package muerte)

(defclass thread (run-time-context)
  ()
  (:metaclass run-time-context-class))

(defmacro control-stack-ebp (stack)
  `(stack-frame-ref ,stack 0 0))

(defmacro control-stack-esp (stack)
  `(stack-frame-ref ,stack 0 1))

(defmacro control-stack-fs (stack)
  `(stack-frame-ref ,stack 0 2))

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

(defun stack-bootstrapper (&rest ignore)
  "Control stacks are initialized with this function as their initial frame."
  (declare (ignore ignore))
  (let ((frame (current-stack-frame)))
    (assert (eql 0 (stack-frame-uplink nil frame)))
    (let ((function (stack-frame-ref nil frame 1))
	  (args (stack-frame-ref nil frame 2)))
      (check-type function function)
      (check-type args list)
      (apply function args)))
  (error "Nothing left to do for ~S." (current-run-time-context))
  (loop (halt-cpu)))			; just to make sure

(defun control-stack-init-for-yield (stack function args)
  "Make it so that a yield to stack will cause function to be applied to args."
  (check-type function function)
  (setf (control-stack-esp stack) (length stack)
	(control-stack-ebp stack) 0)
  (control-stack-push args stack)
  (control-stack-push function stack)
  (control-stack-enter-frame stack #'stack-bootstrapper)
  ;; Now pretend stack-bootstrapper called yield. First, the return address
  (control-stack-push (+ 2 2 (object-location (funobj-code-vector #'stack-bootstrapper)))
		      stack)		; XXX The extra 2 words skip the frame-setup,
					; XXX which happens to be 8 bytes..
  (control-stack-enter-frame stack #'yield)
  stack)

(defun make-thread (&key (name (gensym "thread-")) (function #'invoke-debugger) args)
  "Make a thread and initialize its stack to apply function to args."
  (let* ((fs-index 8) ; a vacant spot in the global segment descriptor table..
	 (fs (* 8 fs-index))
	 (thread (muerte::clone-run-time-context :name name))
	 (segment-descriptor-table nil #+ignore (symbol-value 'muerte.init::*segment-descriptor-table*)))
    (setf (segment-descriptor segment-descriptor-table fs-index)
      (segment-descriptor segment-descriptor-table (truncate (segment-register :fs) 8)))
    (setf (segment-descriptor-base-location segment-descriptor-table fs-index)
      (+ (object-location thread) (muerte::location-physical-offset)))
    (let ((cushion nil)
	  (stack (control-stack-init-for-yield (make-array 4094 :element-type '(unsigned-byte 32))
					       function args)))
      (multiple-value-bind (ebp esp)
	  (control-stack-fixate stack)
	(setf (control-stack-fs stack) fs
	      (control-stack-ebp stack) ebp
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
      (values thread))))

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
      (assert (eq (muerte::stack-frame-funobj nil ebp)
		  (muerte::asm-register :esi)) ()
	"Will not yield to a non-yield frame.")
      ;; Push eflags for later..
      (setf (memref (decf esp) 0) (eflags))
      ;; Store EBP and ESP so we can get to them after the switch
      (setf (%run-time-context-slot 'scratch1 target-rtc) ebp
	    (%run-time-context-slot 'scratch2 target-rtc) esp)
      ;; Enable someone to yield back here..
      (setf (control-stack-fs my-stack) (segment-register :fs)
	    (control-stack-ebp my-stack) (muerte::asm-register :ebp)
	    (control-stack-esp my-stack) (muerte::asm-register :esp))
      (with-inline-assembly (:returns :eax)
	(:load-lexical (:lexical-binding fs) :untagged-fixnum-ecx)
	(:load-lexical (:lexical-binding value) :eax)
	(:cli)
	(:movw :cx :fs)
	(:locally (:movl (:edi (:edi-offset scratch1)) :ebp))
	(:locally (:movl (:edi (:edi-offset scratch2)) :esp))
	(:popfl)))))
