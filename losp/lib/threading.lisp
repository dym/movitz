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
;;;; $Id: threading.lisp,v 1.10 2008-04-02 20:49:35 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :lib/threading)

(defpackage threading
  (:use cl muerte)
  (:export thread
	   yield
	   *segment-descriptor-table-manager*
	   segment-descriptor-table-manager
	   allocate-segment-selector
	   ))

(in-package threading)

(defvar *segment-descriptor-table-manager*)

(defclass segment-descriptor-table-manager ()
  ((table
    :reader segment-descriptor-table
    :initarg :table
    :initform (let ((table (muerte::dump-global-segment-table :entries 64)))
		(push (lambda ()
			(setf (muerte::global-segment-descriptor-table) table))
		      *gc-hooks*)
		(setf (muerte::global-segment-descriptor-table) table)))
   (clients
    :initform (make-array 64))
   (range-start
    :initarg :range-start
    :accessor range-start
    :initform (+ 8 (logand #xfff8 (reduce #'max '(:cs :ds :es :ss :fs)
					  :key #'segment-register))))))

(defmethod allocate-segment-selector ((manager segment-descriptor-table-manager) client
				      &optional (errorp t))
  (loop with table = (segment-descriptor-table manager)
      with clients = (slot-value manager 'clients)
      for selector from (range-start manager) below (* (length table) 2) by 8
      do (when (not (aref clients (truncate selector 8)))
	   (setf  (aref clients (truncate selector 8)) client)
	   (return selector))
      finally (when errorp
		(error "Unable to allocate a segment selector."))))

(defclass thread (run-time-context)
  ((segment-selector
    :reader segment-selector
    :initarg :segment-selector))
  (:metaclass run-time-context-class))

(defmacro control-stack-ebp (stack)
  `(stack-frame-ref ,stack 0 0))

(defmacro control-stack-esp (stack)
  `(stack-frame-ref ,stack 0 1))

(defmacro control-stack-fs (stack)
  `(stack-frame-ref ,stack 0 2))

(defmethod initialize-instance :after ((thread thread)
				       &key (stack-size 2048) segment-selector stack-cushion
					    (function #'invoke-debugger) (args '(nil))
				       &allow-other-keys)
  (let ((segment-selector
	 (or segment-selector
	     (let ((selector (setf (slot-value thread 'segment-selector)
			       (allocate-segment-selector *segment-descriptor-table-manager* thread))))
	       (setf (segment-descriptor (segment-descriptor-table *segment-descriptor-table-manager*)
					 selector)
		 (segment-descriptor (segment-descriptor-table *segment-descriptor-table-manager*)
				     (segment-register :fs)))
	       selector))))
    (check-type segment-selector (unsigned-byte 16))
    (setf (segment-descriptor-base-location (segment-descriptor-table *segment-descriptor-table-manager*)
					    segment-selector)
      (+ (object-location thread) (location-physical-offset)))
    (let ((stack (control-stack-init-for-yield (make-stack-vector stack-size)
					       function args)))
      (multiple-value-bind (ebp esp)
	  (control-stack-fixate stack)
	(setf (control-stack-fs stack) segment-selector
	      (control-stack-ebp stack) ebp
	      (control-stack-esp stack) esp))
      (setf (%run-time-context-slot thread 'muerte::dynamic-env) 0)
      (setf (%run-time-context-slot thread 'muerte::stack-vector) stack)
      (setf (%run-time-context-slot thread 'muerte::stack-top)
	(+ 2 (object-location stack)
	   (length stack)))
      (setf (%run-time-context-slot thread 'muerte::stack-bottom)
	(+ (object-location stack) 2
	   (or stack-cushion
	       (if (>= (length stack) 200)
		   100
		 0))))
      (values thread))))


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

(defun yield (target-rtc &optional value)
  (declare (dynamic-extent values))
  (assert (not (eq target-rtc (current-run-time-context))))
  (let ((my-stack (%run-time-context-slot nil 'muerte::stack-vector))
	(target-stack (%run-time-context-slot target-rtc 'muerte::stack-vector)))
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
      (setf (memref (decf esp) 0 :type :unsigned-byte32) (eflags))
      ;; Store EBP and ESP so we can get to them after the switch
      (setf (%run-time-context-slot target-rtc 'muerte::scratch1) ebp
	    (%run-time-context-slot target-rtc 'muerte::scratch2) esp)
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

