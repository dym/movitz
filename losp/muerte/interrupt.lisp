;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      interrupt.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Apr  7 01:50:03 2004
;;;;                
;;;; $Id: interrupt.lisp,v 1.35 2005/01/17 10:51:09 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package muerte)

(provide :muerte/interrupt)

(defvar *last-dit-frame* nil)

(defconstant +dit-frame-map+
    '(:eflags :cs :eip :error-code :exception-vector
      :ebp
      :funobj
      :edi
      :dynamic-env
      :atomically-continuation
      :raw-scratch0
      :ecx
      :cr2
      :eax :edx :ebx :esi
      :scratch1 :scratch2
      :debug0
      :debug1
      :tail-marker))

(defun dit-frame-esp (stack dit-frame)
  "Return the frame ESP pointed to when interrupt at dit-frame occurred."
  (declare (ignore stack))
  (+ dit-frame 6))

(define-compiler-macro dit-frame-index (&whole form name &environment env)
  (let ((name (and (movitz:movitz-constantp name env)
		   (movitz:movitz-eval name env))))
    (if (not name)
	form
      (- 5 (position name +dit-frame-map+)))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun dit-frame-index (name)
    (- 5 (position name +dit-frame-map+)))
  (defun dit-frame-offset (name)
    (* 4 (dit-frame-index name))))

(define-compiler-macro dit-frame-ref (&whole form stack frame reg
				      &optional (type :lisp)
				      &environment env)
  (if (not (and (movitz:movitz-constantp stack env)
		(eq nil (movitz:movitz-eval stack env))))
      form
    `(memref ,frame (dit-frame-offset ,reg) :type ,type)))

(defun dit-frame-ref (stack frame reg &optional (type :lisp))
  (stack-frame-ref stack frame (dit-frame-index reg) type))

(define-compiler-macro (setf dit-frame-ref) (&whole form value stack frame reg
					     &optional (type :lisp)
					     &environment env)
  (if (not (and (movitz:movitz-constantp stack env)
		(eq nil (movitz:movitz-eval stack env))))
      form
    `(setf (memref ,frame (dit-frame-offset ,reg) :type ,type) ,value)))

;;;(defun (setf dit-frame-ref) (x reg type &optional (frame *last-dit-frame*))
;;;  (setf (memref frame (dit-frame-offset reg) 0 type) x))

(defun dit-frame-casf (stack dit-frame)
  "Compute the `currently active stack-frame' when the interrupt occurred."
  (let ((ebp (dit-frame-ref stack dit-frame :ebp))
	(esp (dit-frame-esp stack dit-frame)))
    (cond
     ((null ebp)			; special mode
      (stack-frame-ref stack (dit-frame-ref stack dit-frame :dynamic-env) 0))
     ((< esp ebp)
      ebp)
     ((> esp ebp)
      ;; A throw situation
      (let ((next-ebp (stack-frame-ref stack esp 0)))
	(check-type next-ebp fixnum)
	(assert (< esp next-ebp))
	next-ebp))
     (t (let ((next-ebp (stack-frame-ref stack esp 0)))
	  (check-type next-ebp fixnum)
	  (assert (< esp next-ebp))
	  next-ebp)))))

(define-primitive-function (default-interrupt-trampoline :symtab-property t) ()
  "Default first-stage/trampoline interrupt handler. Assumes the IF flag in EFLAGS
is off, e.g. because this interrupt/exception is routed through an interrupt gate."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    ,@(loop for i from 0 to 255
		  append (list i)
		  append (if (member i '(8 10 11 12 13 14 17))
			     `((:pushl ,i)
			       (:jmp 'ok))
			   `((:pushl 0) ; replace Error Code
			     (:pushl ,i)
			     (:jmp 'ok))))
	   ok
	    ;; Stack:
	    ;; 20: Interruptee EFLAGS (later EIP)
	    ;; 16: Interruptee CS     (later EFLAGS)
	    ;; 12: Interruptee EIP
	    ;;  8: Error code
	    ;;  4: Exception number
	    ;;  0: EBP
	    (:pushl :ebp)
	    (:movl :esp :ebp)
	    (:pushl 0)			; 0 'funobj' means default-interrupt-trampoline frame
	    (:pushl :edi)		; 
	    (:movl ':nil-value :edi)	; We want NIL!
	    (:locally (:pushl (:edi (:edi-offset dynamic-env))))
	    (:locally (:pushl (:edi (:edi-offset atomically-continuation))))
	    (:locally (:pushl (:edi (:edi-offset raw-scratch0))))
	    (:locally (:pushl :ecx))
	    (:movcr :cr2 :ecx)
	    (:locally (:pushl :ecx))
	    ,@(loop for reg in (sort (copy-list '(:eax :ebx :edx :esi))
				     #'>
				     :key #'dit-frame-index)
		  collect `(:pushl ,reg))
	    (:locally (:pushl (:edi (:edi-offset scratch1))))
	    (:locally (:pushl (:edi (:edi-offset scratch2))))
 	    
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :eax))
	    (:pushl :eax)		; debug0: nursery-space
	    (:pushl (:eax 2))		; debug1: nursery-space's fresh-pointer

	    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	    
	    ;; Do RET atomicification
	    (:movl (:ebp ,(dit-frame-offset :eip)) :ecx)
	    ((:cs-override) :cmpb ,(realpart (ia-x86:asm :ret)) (:ecx))
	    (:jne 'not-at-ret-instruction)
	    (:globally (:movl (:edi (:edi-offset ret-trampoline)) :ecx))
	    (:movl :ecx (:ebp ,(dit-frame-offset :eip)))
	   not-at-ret-instruction
	    
	    (:xorl :eax :eax)		; Ensure safe value
	    (:xorl :edx :edx)		; Ensure safe value

	    (:pushl (:ebp ,(dit-frame-offset :eflags))) ; EFLAGS
	    (:pushl :cs)		; push CS
	    (:call (:pc+ 0))		; push EIP.
	    ;; Now add a few bytes to the on-stack EIP so the iret goes to
	    ;; *DEST* below.
	    (((:size 4)) :addl 5 (:esp)) ; 4 bytes
	    (((:size 1)) :iretd)	; 1 byte
    
	    ;; *DEST* iret branches to here.
	    ;; we're now in the context of the interruptee.
	    
	    (:cld)
	    ;; Save/push thread-local values
	    (:locally (:movl (:edi (:edi-offset num-values)) :ecx))
	    (:jecxz 'push-values-done)
	    (:leal (:edi (:offset movitz-run-time-context values)) :eax)
	   push-values-loop
	    (:locally (:pushl (:eax)))
	    (:addl 4 :eax)
	    (:subl 1 :ecx)
	    (:jnz 'push-values-loop)
	   push-values-done
	    (:locally (:pushl (:edi (:edi-offset num-values))))

	    ;; Check the current atomically-continuation isn't a recursive one.
	    (:movl (:ebp ,(dit-frame-offset :atomically-continuation)) :ecx)
	    (:testl :ecx :ecx)
	    (:jz 'atomically-continuation-ok)
	    (:testb 3 :cl)
	    (:jnz 'atomically-continuation-ok) ; can't tell for pf-atomically.
	    (:movl (:ecx 4) :ecx)
	    (:testl :ecx :ecx)
	    (:jz 'atomically-continuation-ok)
	    (:int 63)			; not ok.
	   atomically-continuation-ok
	    
	    ;; call handler
	    (:movl (:ebp ,(dit-frame-offset :exception-vector)) :ecx)
	    (:locally (:movl (:edi (:edi-offset exception-handlers)) :eax))
	    (:movl (:eax 2 (:ecx 4)) :esi) ; funobj at (aref ECX exception-handlers) into :esi
	    (:movl :ebp :ebx)		; pass dit-frame as arg1
	    (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax) ; pass interrupt number as arg 0.
	    (:call (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op)))

	   skip-interrupt-handler
	    ;; Restore thread-local values
	    (:popl :ecx)
	    (:locally (:movl :ecx (:edi (:edi-offset num-values))))
	    (:jecxz 'pop-values-done)
	   pop-values-loop
	    ;; ((:fs-override) :popl (:edi #.(movitz::global-constant-offset 'values) (:ecx 4) -4))
	    (:locally (:popl (:edi (:edi-offset values) (:ecx 4) -4)))
	    (:subl 1 :ecx)
	    (:jnz 'pop-values-loop)
	   pop-values-done

	    (:movl (:ebp ,(dit-frame-offset :atomically-continuation)) :ecx)
	    (:testl :ecx :ecx)
	    (:jnz 'restart-atomical-block)

	    ;; Interrupted code was non-atomical, the normal case.
	   normal-return
	    (:movl (:ebp ,(dit-frame-offset :dynamic-env)) :ecx)
	    (:locally (:cmpl :ecx (:edi (:edi-offset dynamic-env))))
	    (:jne '(:sub-program ()
		    ;; This would mean the interrupt handled failed to reset dynamic-env.
		    (:int 63)))
	    ;; (:locally (:movl :ecx (:edi (:edi-offset dynamic-env))))
	    (:movl (:ebp ,(dit-frame-offset :raw-scratch0)) :ecx)
	    (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0))))
	    (:movl (:ebp ,(dit-frame-offset :scratch1)) :eax)
	    (:locally (:movl :eax (:edi (:edi-offset scratch1))))
	    (:movl (:ebp ,(dit-frame-offset :scratch2)) :eax)
	    (:locally (:movl :eax (:edi (:edi-offset scratch2))))

	    ;; Load the DF flag from the interruptee before we restore
	    ;; its register contents.
	    (:testl #x400 (:ebp ,(dit-frame-offset :eflags))) ; was DF set?
	    (:jz 'df-not-set)
	    (:std)
	   df-not-set
	    
	    (:movl (:ebp ,(dit-frame-offset :edi)) :edi)
	    (:movl (:ebp ,(dit-frame-offset :esi)) :esi)
	    (:movl (:ebp ,(dit-frame-offset :ebx)) :ebx)
	    (:movl (:ebp ,(dit-frame-offset :edx)) :edx)
	    (:movl (:ebp ,(dit-frame-offset :eax)) :eax)
	    (:movl (:ebp ,(dit-frame-offset :ecx)) :ecx)
	    (:cli)			; Clear IF in EFLAGS before leaving dit-frame.
	    (:leave)
	    (:addl 8 :esp)		; Skip exception-vector and error-code.
	    (:iretd)			; Pop EFLAGS, CS, and EIP.
    
	   restart-atomical-block
	    ;; Atomically-continuation is in ECX
	    
	    (:testb 3 :cl)
	    (:jnz 'restart-simple-pf)

	    ;; ECX is a throw target aka. next continuation step.
	    (:locally (:movl :esi (:edi (:edi-offset scratch1))))
	    (:movl (:ecx 12) :edx)
	    (:locally (:movl :edx (:edi (:edi-offset dynamic-env)))) ; exit to target dynamic-env
	    (:movl :ecx :esp)		; enter non-local jump stack mode.
	    
	    (:movl (:esp) :ecx)		; target stack-frame EBP
	    (:movl (:ecx -4) :esi)	; get target funobj into ESI
	    
	    (:movl (:esp 8) :ecx)	; target jumper number
	    (:jmp (:esi :ecx (:offset movitz-funobj constant0)))
	    
	   restart-simple-pf
	    ;; ECX holds the run-time-context offset for us to load.
	    
	    (:movl ,movitz:+code-vector-transient-word+ :eax)
	    (:locally (:addl (:edi :ecx) :eax))
	    (:leal (:eax ,movitz:+other-type-offset+) :ecx)
	    (:testb 7 :cl)
	    (:jnz '(:sub-program (pf-continuation-not-code-vector)
		    (:int 63)))
	    (:cmpw ,(movitz:basic-vector-type-tag :code) (:eax ,movitz:+other-type-offset+))
	    (:jne 'pf-continuation-not-code-vector)
	    (:leal (:eax ,movitz:+code-vector-word-offset+) :ecx)
	    (:movl :ecx (:ebp ,(dit-frame-offset :eip)))
	    (:jmp 'normal-return)
	    
	   not-restart-continuation
	    ;; Don't know what to do.
	    (:int 63)
	    )))
    (do-it)))

(defun interrupt-default-handler (vector dit-frame)
  (declare (without-check-stack-limit))
  (macrolet ((dereference (fixnum-address &optional (type :lisp))
	       "Dereference the fixnum-address."
	       `(memref ,fixnum-address 0 :type ,type)))
    (let (($eip (+ dit-frame (dit-frame-index :eip)))
	  ($eax (+ dit-frame (dit-frame-index :eax)))
	  ($ebx (+ dit-frame (dit-frame-index :ebx)))
	  ($ecx (+ dit-frame (dit-frame-index :ecx)))
	  ($edx (+ dit-frame (dit-frame-index :edx)))
	  ($esi (+ dit-frame (dit-frame-index :esi)))
	  (*last-dit-frame* dit-frame))
      (block nil
	(case vector
	  (0 (error 'division-by-zero))
	  (3 (break "Break instruction at ~@Z." $eip))
	  (4 (warn "into ~@Z" $eax)
	     (if (not (eq (load-global-constant new-unbound-value)
			  (dereference $eax)))
		 (error "Primitive overflow assertion failed.")
	       (let ((name (dereference $ebx)))
		 (with-simple-restart (new-value "Set the value of ~S." name)
		   (error 'unbound-variable :name name))
		 (format *query-io* "~&Enter a value for ~S: " name)
		 (setf (dereference $eax) (read *query-io*)))))
	  (6 (error "Illegal instruction at ~@Z." $eip))
	  (13  (error "General protection error. EIP=~@Z, error-code: #x~X, EAX: ~@Z, EBX: ~@Z, ECX: ~@Z"
		     $eip
		     (dit-frame-ref nil dit-frame :error-code :unsigned-byte32)
		     $eax $ebx $ecx))
	  ((60)
	   ;; EAX failed type in EDX. May be restarted by returning with a new value in EAX.
	   (with-simple-restart (continue "Retry with a different value.")
	     (error 'type-error :datum (dereference $eax) :expected-type (dereference $edx)))
	   (format *query-io* "Enter a new value: ")
	   (setf (dereference $eax) (read *query-io*)))
	  (61 (error 'type-error :datum (dereference $eax) :expected-type 'list))
	  (62 (error "Trying to save too many values: ~@Z." $ecx))
	  (63 (error "Primitive assertion error. EIP=~@Z, ESI=~@Z." $eip $esi))
	  (64 (error 'type-error :datum (dereference $eax) :expected-type 'integer))
	  (65 (error 'index-out-of-range :index (dereference $ebx) (dereference $ecx)))
	  (66 (error "Unspecified type error at ~@Z in ~S with EAX=~@Z, ECX=~@Z."
		     $eip (dereference (+ dit-frame (dit-frame-index :esi)))
		     $eax $ecx))
	  (67 (backtrace :fresh-lines nil :length 6)
	      (dotimes (i 100000)
		(with-inline-assembly (:returns :nothing) (:nop))))
	  (68 (warn "EIP: ~@Z EAX: ~@Z EBX: ~@Z  ECX: ~@Z EDX: ~@Z"
		    $eip $eax $ebx $ecx $edx)
	      (dotimes (i 100000)
		(with-inline-assembly (:returns :nothing) (:nop))))
	  (70 (error "Unaligned memref access."))
	  ((5 55)
	   (let* ((old-bottom (prog1 (%run-time-context-slot 'stack-bottom)
				(setf (%run-time-context-slot 'stack-bottom) 0)))
		  (stack (%run-time-context-slot 'movitz::stack-vector))
		  (real-bottom (- (object-location stack) 2))
		  (stack-left (- old-bottom real-bottom))
		  (old-es (segment-register :es))
		  (old-dynamic-env (%run-time-context-slot 'dynamic-env))
		  (new-bottom (cond
			       ((< stack-left 50)
				(princ "Halting CPU due to stack exhaustion.")
				(halt-cpu))
			       ((<= stack-left 1024)
				(backtrace :print-frames t)
				(halt-cpu)
				#+ignore
				(format *debug-io*
					"~&This is your LAST chance to pop off stack.~%")
				real-bottom)
			       (t (+ real-bottom (truncate stack-left 4)))))) ; Cushion the fall..
	     (unwind-protect
		 (progn
		   (setf (%run-time-context-slot 'stack-bottom) new-bottom
			 ;; (%run-time-context-slot 'dynamic-env) 0
			 (segment-register :es) (segment-register :ds))
		   (format *debug-io* "~&Stack-warning: Bumped stack-bottom by ~D to #x~X. Reset ES.~%"
			   (- old-bottom new-bottom)
			   new-bottom)
		   (break "Stack overload exception ~D at EIP=~@Z, ESP=~@Z, bottom=#x~X, ENV=#x~X."
			  vector $eip
			  (dit-frame-esp nil dit-frame)
			  old-bottom
			  old-dynamic-env))
	       (format *debug-io* "~&Stack-warning: Resetting stack-bottom to #x~X.~%"
		       old-bottom)
	       (setf (%run-time-context-slot 'stack-bottom) old-bottom
		     ;; (%run-time-context-slot 'dynamic-env) old-dynamic-env
		     (segment-register :es) old-es))))
	  (69
	   (error "Not a function: ~S" (dereference $edx)))
	  (70
	   (error "[EIP=~@Z] Index ~@Z out of bounds ~@Z for ~S." $eip $ecx $ebx (dereference $eax)))
	  (98
	   (let ((name (dereference $edx)))
	     (when (symbolp name)
	       (error 'undefined-function :name name))))
	  ((100);; 101 102 103 104 105)
	   (let ((funobj (dereference (+ dit-frame (dit-frame-index :esi))))
		 (code (dit-frame-ref nil dit-frame :ecx :unsigned-byte8)))
	     (error 'wrong-argument-count
		    :function funobj
		    :argument-count (if (logbitp 7 code)
					(ldb (byte 8 24)
					     (dit-frame-ref nil dit-frame :ecx :unsigned-byte32))
				      code))))
	  (108
	   (error 'throw-error :tag (dereference $eax)))
	  (110
	   ;; (print-dynamic-context); what's this?
	   (throw :debugger nil))
	  (112
	   (let ((*error-no-condition-for-debugger* t)) ; no space..
	     (error "Out of memory. Please take out the garbage.")))
	  (t (funcall (cond 
		       ((<= 32 vector 48) #'break)
		       ((<= 16 vector 50) #'warn)
		       (t #'error))
		      "Exception occurred: ~D, EIP: ~@Z, EAX: ~@Z, ECX: ~@Z, ESI: ~@Z"
		      vector $eip $eax $ecx $esi)))
	nil))))


(defun exception-handler (vector)
  (let ((handlers (load-global-constant exception-handlers)))
    (svref handlers vector)))

(defun (setf exception-handler) (handler vector)
  (check-type handler function)
  (let ((handlers (load-global-constant exception-handlers)))
    (setf (svref handlers vector) handler)))

(defun cli ()
  (compiler-macro-call cli))

(defun sti ()
  (compiler-macro-call sti))

(defun raise-exception (vector &optional (eax 0) (ebx 0))
  "Generate a CPU exception, with those values in EAX and EBX."
  ;; The problem now is that the x86 INT instruction only takes an
  ;; immediate argument.
  (check-type vector (unsigned-byte 8))
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:load-lexical (:lexical-binding eax) :eax)
	    (:load-lexical (:lexical-binding ebx) :ebx)
	    (:load-lexical (:lexical-binding vector) :ecx)
	    (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	    (:jnz 'not-0)
	    (:int 0)
	    (:jmp 'done)
	   not-0
	    ,@(loop for i from 1 to 255 as label = (gensym (format nil "not-~D" i))
		  appending
		    `((:decl :ecx)
		      (:jnz ',label)
		      (:int ,i)
		      ;; (:jmp 'done)
		      ,label))
	   done)))
    (do-it)))
