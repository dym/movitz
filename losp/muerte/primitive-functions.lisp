;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      primitive-functions.lisp
;;;; Description:   Some primitive-functions of the basic run-time
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Oct  2 21:02:18 2001
;;;;                
;;;; $Id: primitive-functions.lisp,v 1.71 2008-03-21 22:28:26 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/primitive-functions)

(in-package muerte)

(defconstant +funobj-trampoline-table+
    #(trampoline-funcall%1op
      trampoline-funcall%2op
      trampoline-funcall%3op
      trampoline-cl-dispatch-1or2
      assert-1arg
      assert-2args
      assert-3args
      decode-args-1or2))

(defconstant +funobj-trampoline-table-size+ 16)

(define-primitive-function trampoline-funcall%1op ()
  "Call a function with 1 argument"
  (with-inline-assembly (:returns :nothing)
    (:movb 1 :cl)
    (:jmp (:esi #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector)))))

(define-primitive-function trampoline-funcall%2op ()
  "Call a function with 2 arguments"
  (with-inline-assembly (:returns :nothing)
    (:movb 2 :cl)
    (:jmp (:esi #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector)))))

(define-primitive-function trampoline-funcall%3op ()
  "Call a function with 3 arguments"
  (with-inline-assembly (:returns :nothing)
    (:movb 3 :cl)
    (:jmp (:esi #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector)))))

(define-primitive-function trampoline-cl-dispatch-1or2 ()
  "Jump to the entry-point designated by :cl, which must be 1 or 2."
  (with-inline-assembly (:returns :nothing)
    (:subb 1 :cl)			; 1 or 2 => 0 or 1
    (:testb #xfe :cl)
    (:jnz 'mismatch)
    (:jmp (:esi (:ecx 4) #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector%1op)))
   mismatch
    (:addb 1 :cl)
    (:int 100)))

(define-primitive-function no-code-vector ()
  "This is the default code-vector, which never should be called."
  (with-inline-assembly (:returns :nothing)
   error
    (:int 69)
    (:jmp 'error)))

(defmacro define-gf-dispatcher (name lambda-list docstring forward to)
  `(define-primitive-function ,name ,lambda-list
     ,docstring
     (with-inline-assembly (:returns :nothing)
       (:movl :esi :edx)		; parameter for standard-gf-function.
       (:movl (:esi (:offset movitz-funobj-standard-gf ,to))
	      :esi)
       (:jmp (:esi  (:offset movitz-funobj ,forward))))))
  
(define-gf-dispatcher standard-gf-dispatcher ()
  "The code-vector of standard-gf instances." code-vector standard-gf-function)

(define-gf-dispatcher standard-gf-dispatcher%1op ()
  "The code-vector of standard-gf instances." code-vector%1op standard-gf-function)

(define-gf-dispatcher standard-gf-dispatcher%2op ()
  "The code-vector of standard-gf instances." code-vector%2op standard-gf-function)

(define-gf-dispatcher standard-gf-dispatcher%3op ()
  "The code-vector of standard-gf instances." code-vector%3op standard-gf-function)


;;; Dynamic binding:
;;;   12: parent (no parent == #x0)
;;;    8: value
;;;    4: scratch, free to use by binding implementation.
;;;    0: binding name (a symbol)

;;; Catch exit-point:
;;;   12: parent (no parent == #x0)
;;;    8: jumper index (=> eip)
;;;    4: catch tag object/word
;;;    0: ebp/stack-frame

;;; Unwind-protect entry:
;;;   12: parent
;;;    8: jumper index (=> eip)
;;;    4: tag = #:unwind-protect-tag
;;;    0: ebp/stack-frame

;;; Basic-restart entry:
;;;   12: parent
;;;    8: jumper index (=> eip)
;;;    4: tag = #:basic-restart-tag
;;;    0: ebp/stack-frame
;;;   -4: name
;;;   -8: function
;;;  -12: interactive function
;;;  -16: test
;;;  -20: format-control
;;;  -24: (on-stack) list of format-arguments
;;;  -28: cdr
;;;  -32: car ...

(define-primitive-function dynamic-unwind-next (dynamic-env)
  "Locate the next unwind-protect entry between here and dynamic-env/EAX.
If no such entry is found, return (same) dynamic-env in EAX and CF=0.
Otherwise return the unwind-protect entry in EAX and CF=1. Preserve EDX.
Point is: Return the 'next step' in unwinding towards dynamic-env.
Note that it's an error if dynamic-env isn't in the current dynamic environment,
it's supposed to have been found by e.g. dynamic-locate-catch-tag."
  ;; XXX: Not really sure if there's any point in the CF return value,
  ;;      because I don't think there's ever any need to know whether
  ;;      the returned entry is an unwind-protect or the actual target.
  (with-inline-assembly (:returns :nothing)
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :eax))
    (:globally (:movl (:edi (:edi-offset unwind-protect-tag)) :ebx))
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    
   search-loop
    (:jecxz '(:sub-program () (:int 63)))
    ;; (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))

    (:cmpl :ecx :eax)
    (:je 'found-dynamic-env)
    
    (:cmpl :ebx (:ecx 4))		; unwind-protect entry?
    (:je 'found-unwind-protect)
    
    ;; We don't need to check for and uninstall dynamic binding entries,
    ;; because uninstall is a NOP under naive deep binding.
    
    (:movl (:ecx 12) :ecx)		; proceed search
    (:jmp 'search-loop)
   found-unwind-protect
    (:movl :ecx :eax)
    (:stc)
   found-dynamic-env
    (:ret)))

(define-primitive-function dynamic-variable-install ()
  "Install each dynamic binding entry between that in ESP and current dynamic-env.
Preserve EDX."
  (with-inline-assembly (:returns :nothing)
    ;; Default binding strategy is naive deep binding, so this is a NOP.
    (:ret)))

(define-primitive-function dynamic-variable-uninstall (dynamic-env)
  "Uninstall each dynamic binding between 'here' (i.e. the current 
dynamic environment pointer) and the dynamic-env pointer provided in EDX.
This must be done without affecting 'current values'! (i.e. eax, ebx, ecx, or CF),
and also EDX must be preserved."
  (with-inline-assembly (:returns :nothing)
    ;; Default binding strategy is naive deep binding, so this is a NOP.
    (:ret)))
    
;;;(define-primitive-function dynamic-variable-lookup (symbol)
;;;  "Load the dynamic value of SYMBOL into EAX."
;;;  (with-inline-assembly (:returns :multiple-values)
;;;    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
;;;    (:jecxz 'no-stack-binding)
;;;    ;; Be defensive: Verify that ECX is within stack.
;;;    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))
;;;    (:cmpl :eax (:ecx))
;;;    (:je 'success)
;;;   search-loop
;;;    (:movl (:ecx 12) :ecx)		; parent
;;;    (:jecxz 'no-stack-binding)
;;;    ;; Be defensive: Verify that ECX is within stack.
;;;    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))
;;;    (:cmpl :eax (:ecx))			; compare name
;;;    (:jne 'search-loop)
;;;    ;; fall through on success
;;;   success
;;;    (:movl :eax :edx)			; Keep symbol in case it's unbound.
;;;    (:movl (:ecx 8) :eax)
;;;    (:globally (:cmpl (:edi (:edi-offset unbound-value)) :eax))
;;;    (:je '(:sub-program (unbound) (:int 99)))
;;;    (:ret)
;;;   no-stack-binding
;;;    ;; take the global value of SYMBOL, compare it against unbond-value
;;;    (:movl :eax :edx)			; Keep symbol in case it's unbound.
;;;    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
;;;     :movl (:eax (:offset movitz-symbol value)) :eax)
;;;    (:globally (:cmpl (:edi (:edi-offset unbound-value)) :eax))
;;;    (:je '(:sub-program (unbound) (:int 99)))
;;;    (:ret)))

(define-primitive-function dynamic-variable-lookup (symbol)
  "Load the dynamic value of SYMBOL/EBX into EAX. If unbound, return unbound-value."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    (:jecxz 'no-stack-binding)
    ;; Be defensive: Verify that ECX is within stack.
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))
    (:cmpl :ebx (:ecx))
    (:je 'success)
   search-loop
    (:movl (:ecx 12) :ecx)		; parent
    (:jecxz 'no-stack-binding)
    ;; Be defensive: Verify that ECX is within stack.
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))
    (:cmpl :ebx (:ecx))			; compare name
    (:jne 'search-loop)
    ;; fall through on success
   success
    (:movl (:ecx 8) :eax)
    (:ret)
   no-stack-binding
    ;; take the global value of SYMBOL, compare it against unbond-value
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:ebx (:offset movitz-symbol value)) :eax)
    (:ret)))

(define-primitive-function dynamic-variable-store (symbol value)
  "Store VALUE (ebx) in the dynamic binding of SYMBOL (eax).
   Preserves EBX and EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    (:jecxz 'no-binding)
    (:cmpl :eax (:ecx))
    (:je 'success)
   search-loop
    (:movl (:ecx 12) :ecx)		; parent
    (:jecxz 'no-binding)
    (:cmpl :eax (:ecx))			; compare name
    (:jne 'search-loop)
    ;; fall through on success
   success
    (:movl :ebx (:ecx 8))		; Store VALUE in binding.
    (:ret)
   no-binding
    (#.movitz::*compiler-nonlocal-lispval-write-segment-prefix*
     :movl :ebx (:eax (:offset movitz-symbol value)))
    (:ret)))

(define-primitive-function keyword-search ()
  "Search for keyword ECX in keyword-list EBX."
  (with-inline-assembly (:returns :multiple-values)
   search-loop
    (:cmpl :edi :ebx)
    (:je 'search-failed)		; failed: ZF=1
    (:cmpl :ecx (:ebx -1))		; (eq ecx (car))
    (:movl (:ebx 3) :ebx)		;    ebx = (cdr ebx)
    (:movl (:ebx -1) :edx)		;    edx = (car ebx)
    (:movl (:ebx 3) :ebx)		;    ebx = (cdr ebx)
    (:jne 'search-loop)			; 
    (:movl :edx :eax)
    (:testl :edi :edi)			; clear ZF
   search-failed
    (:ret)))				; success: ZF=0, eax=value



;;;;;;;;;;;;;; Heap allocation protocol

(define-primitive-function cons-pointer ()
  "Return in EAX the next object location with space for EAX words, with tag 6.
Preserve ECX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0)))) ; Preserve ECX
	    (:movl :eax :ebx)
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :eax))
	    (:testb #xff :al)
	    (:jnz '(:sub-program (not-initialized)
		    (:int 110)
		    (:halt)
		    (:jmp 'not-initialized)))
	    (:addl 4 :ebx)
	    (:andb #xf8 :bl)
	    (:movl (:eax 4) :ecx)	; cons pointer to ECX
	    (:leal (:ebx :ecx) :edx)	; new roof to EDX
	    (:cmpl :edx (:eax))		; end of buffer?
	    (:jl '(:sub-program (failed)
		   (:int 112)
		   (:halt)
		   (:jmp 'failed)))
	    (:movl :edx (:eax 4))	; new cons pointer
	    (:leal (:eax :ecx 6) :eax)
	    (:locally (:movl (:edi (:edi-offset raw-scratch0)) :ecx))
	    (:ret))))
    (do-it)))

(define-primitive-function muerte::cons-commit ()
  "Commit allocation of ECX/fixnum words.
Preserve EAX and EBX."
  (macrolet
      ((do-it ()
	 ;; Since cons-pointer is implemented as an (already committed)
	 ;; malloc, this is a no-op.
	 `(with-inline-assembly (:returns :multiple-values)
	    (:ret))))
    (do-it)))

(define-primitive-function cons-non-pointer ()
  "Return in EAX the next object location with space for EAX non-pointer words, with tag 6.
Preserve ECX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:jmp (:edi (:edi-offset cons-pointer))))))

(define-primitive-function cons-commit-non-pointer ()
  "Return in EAX the next object location with space for EAX non-pointer words, with tag 6.
Preserve ECX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:jmp (:edi (:edi-offset cons-commit))))))

(define-primitive-function cons-non-header ()
  "Return in EAX the next object location with space for EAX non-pointer words, with tag 6.
Preserve ECX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:jmp (:edi (:edi-offset cons-pointer))))))

(define-primitive-function cons-commit-non-header ()
  "Return in EAX the next object location with space for EAX non-pointer words, with tag 6.
Preserve ECX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:jmp (:edi (:edi-offset cons-commit))))))

(defun malloc-initialize (buffer-start buffer-size)
  "BUFFER-START is the location from which to allocate.
BUFFER-SIZE is the number of words in the buffer."
  (check-type buffer-start fixnum)
  (check-type buffer-size fixnum)
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :eax) buffer-start)
    (:locally (:movl :eax (:edi (:edi-offset nursery-space))))
    (:compile-form (:result-mode :ebx) buffer-size)
    (:movl :ebx (:eax))			; roof pointern
    (:movl 16 (:eax 4))))		; cons pointer

(defun malloc-buffer-start ()
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset nursery-space)) :eax))
    (:testb 7 :al)
    (:jnz '(:sub-program ()
	    (:int 63)))))
  
(defun malloc-cons-pointer ()
  "Return current cons-pointer in 8-byte units since buffer-start."
  (let ((x (%run-time-context-slot nil 'nursery-space)))
    (when (typep x 'vector)
      (truncate (aref x 0) 8)))
  #+ignore
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset nursery-space)) :eax))
    (:movl (:eax 4) :eax)
    (:testb 7 :al)
    (:jnz '(:sub-program ()
	    (:int 107)))
    (:shrl 1 :eax)))

(defun malloc-end ()
  "Return the last location of the (dynamically allocated) heap area."
  (+ (malloc-buffer-start)
     (* 2 (malloc-cons-pointer))))

(define-primitive-function fast-cons ()
  "Allocate a cons cell. Call with car in eax and cdr in ebx."
  (with-inline-assembly (:returns :multiple-values)
    (:xchgl :eax :ecx)
    (:locally (:movl (:edi (:edi-offset nursery-space)) :eax))
    (:movl (:eax 4) :edx)
    (:addl 8 :edx)
    (:cmpl :edx (:eax))
    (:jl '(:sub-program (failed)
	   (:int 112)
	   (:halt)
	   (:jmp 'failed)))
    (:xchgl :edx (:eax 4))
    (:leal (:eax :edx) :eax)
    (:movl :ecx (:eax))
    (:movl :ebx (:eax 4))
    (:addl 1 :eax)
    (:ret)))

(define-primitive-function ensure-heap-cons-variable ()
  "Call with lended variable (a cons) in EAX."
  (with-inline-assembly (:returns :multiple-values)
    ;; Be defensive: Check that EAX is LISTP.
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 63)))
    (:cmpl :ebp :eax)			; is cons above stack-frame?
    (:jge 'return-ok)
    (:cmpl :esp :eax)			; is cons below stack-frame?
    (:jl 'return-ok)
    ;; must migrate cell onto heap
    (:movl (:eax 3) :ebx)		; cdr
    (:movl (:eax -1) :eax)		; car
    (:locally (:jmp (:edi (:edi-offset fast-cons))))
   return-ok
    (:ret)))

(define-primitive-function box-u32-ecx ()
  "Make u32 in ECX into a fixnum or bignum in EAX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:cmpl ,movitz:+movitz-most-positive-fixnum+ :ecx)
	    (:ja 'not-fixnum)
	    (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
	    (:ret)
	   not-fixnum
	    ;; XXX Implement bignum consing here.
	   fail
	    (:int 63))))
    (do-it)))
	    

(define-primitive-function unbox-u32 ()
  "Load (ldb (byte 32 0) EAX) into ECX. Preserve EAX and EBX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:testb 3 :al)
	    (:jnz 'not-fixnum)
	    (:movl :eax :ecx)
	    (:sarl ,movitz:+movitz-fixnum-shift+ :ecx)
	    (:ret)
	   not-fixnum
	    (:leal (:eax ,(- (movitz:tag :other))) :ecx)
	    (:testb 7 :cl)
	    (:jnz 'fail)
	    (:cmpb ,(movitz:tag :bignum) (:eax ,movitz:+other-type-offset+))
	    (:jne 'fail)
	    (:movl (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0))
		   :ecx)
	    (:ret)
	   fail
	    (:int 64))))
    (do-it)))

;;;;

(define-primitive-function fast-class-of-even-fixnum ()
  "Return the class of a fixnum object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :eax))
    (:movl (:eax #.(movitz::class-object-offset 'fixnum)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-odd-fixnum ()
  "Return the class of a fixnum object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :eax))
    (:movl (:eax #.(movitz::class-object-offset 'fixnum)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-cons ()
  "Return the class of a cons object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :eax))
    (:movl (:eax #.(movitz::class-object-offset 'cons)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-symbol ()
  "Return the class of a symbol object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :eax))
    (:movl (:eax #.(movitz::class-object-offset 'symbol)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-std-instance ()
  "Return the class of a std-instance object."
  (with-inline-assembly (:returns :multiple-values)
    (:movl (:eax (:offset movitz-std-instance class))
	   :eax)
    (:ret)))

(define-primitive-function fast-class-of-tag3 ()
  "Return the class of a tag3 object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :eax))
    (:movl (:eax #.(movitz::class-object-offset 'illegal-object)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-character ()
  "Return the class of a character object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :ebx))
    (:cmpb #.(movitz:tag :character) :al)
    (:jne '(:sub-program ()
	    (:globally (:movl (:edi (:edi-offset complicated-class-of)) :esi))
	    (:jmp (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))))
    (:movl (:ebx #.(movitz::class-object-offset 'character)) :eax)
    (:ret)))

(define-primitive-function fast-class-of-null ()
  "Return the class of a nil object."
  (with-inline-assembly (:returns :multiple-values)
    (:globally (:movl (:edi (:edi-offset classes)) :ebx))
    (:cmpl :edi :eax)
    (:je 'null)
    (:movl (:ebx #.(movitz:class-object-offset 'illegal-object)) :eax)
    (:jmp 'not-null)
   null
    (:movl (:ebx #.(movitz:class-object-offset 'null)) :eax)
   not-null
    (:ret)))

(define-primitive-function fast-class-of-other ()
  "Return the class of an other object."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:movl (:eax ,movitz:+other-type-offset+) :ecx)
	    (:cmpb ,(movitz:tag :std-instance) :cl)
	    (:jne 'not-std-instance)
	    (,movitz:*compiler-nonlocal-lispval-read-segment-prefix*
	     :movl (:eax ,(bt:slot-offset 'movitz::movitz-std-instance 'movitz::class)) :eax)
	    (:ret)
	   not-std-instance
	    (:cmpw ,(+ (movitz:tag :funobj)
		       (ash (bt:enum-value 'movitz::movitz-funobj-type :generic-function) 8))
		   :cx)
	    (:jne 'not-std-gf-instance)
	    (,movitz:*compiler-nonlocal-lispval-read-segment-prefix*
	     :movl (:eax ,(bt:slot-offset 'movitz::movitz-funobj-standard-gf
					  'movitz::standard-gf-class))
		   :eax)
	    (:ret)
	   not-std-gf-instance

	    (:cmpb ,(movitz:tag :run-time-context) :cl)
	    (:jne 'not-rtc)
	    (,movitz:*compiler-nonlocal-lispval-read-segment-prefix*
	     :movl (:eax (:offset movitz-run-time-context class
				  ,(- (movitz::image-nil-word movitz:*image*)
				      (movitz::tag :other))))
	     :eax)
	    (:ret)
	   not-rtc
	    
	    (:globally (:movl (:edi (:edi-offset classes)) :ebx))
	    (:cmpb ,(movitz:tag :bignum) :cl)
	    (:jne 'not-bignum)
	    (:movl (:ebx ,(movitz:class-object-offset 'integer)) :eax)
	    (:ret)
	   not-bignum
	    (:globally (:movl (:edi (:edi-offset complicated-class-of)) :esi))
	    (:jmp (:esi ,(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))))
    (do-it)))

(defun complicated-class-of (object)
  (typecase object
    (ratio
     (find-class 'ratio))
    (std-instance
     (memref object (movitz-type-slot-offset 'movitz-std-instance 'class)))
    (standard-gf-instance
     (memref object (movitz-type-slot-offset 'movitz-funobj-standard-gf 'standard-gf-class)))
    (string
     (find-class 'string))
    (bit-vector
     (find-class 'bit-vector))
    (vector
     (find-class 'vector))
    (function
     (find-class 'function))
    (structure-object
     (structure-object-class object))
    (macro-function
     (find-class 'macro-function))
    (character
     (find-class 'character))
    (null
     (find-class 'null))
    (cons
     (find-class 'cons))
    (symbol
     (find-class 'symbol))
    (fixnum
     (find-class 'fixnum))
    (basic-restart
     (find-class 'basic-restart))
    (t (find-class 'illegal-object))))

(define-primitive-function pop-current-values ()
  "Input: ECX is (fixnum) number of values. Pop values into the standard location
for the current multiple values (i.e. eax, ebx, CF, and the values run-time-context array).
However, ESP is *NOT* reset, this must be done by the caller.
The number of values (untagged) is returned in ECX, even if CF=0."
  (with-inline-assembly (:returns :multiple-values)
    (:testb #.movitz:+movitz-fixnum-zmask+ :cl)
    (:jnz '(:sub-program () (:int 63)))
    (:cmpl 4 :ecx)
    (:jb '(:sub-program (zero-values) (:stc) (:ret)))
    (:je '(:sub-program (one-value)
	   (:movl (:esp 4) :eax)
	   (:shrl #.movitz:+movitz-fixnum-shift+ :ecx)
	   (:clc)
	   (:ret)))
    (:cmpl 8 :ecx)
    (:je '(:sub-program (two-values)
	   (:movl (:esp 8) :eax)
	   (:movl (:esp 4) :ebx)
	   (:shrl #.movitz:+movitz-fixnum-shift+ :ecx)
	   (:stc)
	   (:ret)))
    ;; three or more values
    (:subl 8 :ecx)
    (:locally (:movl :ecx (:edi (:edi-offset num-values))))
    (:subl 4 :ecx)
    (:xorl :edx :edx)			; pointer into stack
   pop-loop
    (:movl (:esp :edx 4) :eax)
    (:locally (:movl :eax (:edi :ecx (:edi-offset values))))
    (:addl 4 :edx)
    (:subl 4 :ecx)
    (:jnc 'pop-loop)
    (:leal (:edx 8) :ecx)
    (:movl (:esp :edx 4) :ebx)
    (:movl (:esp :edx 8) :eax)
    (:shrl #.movitz:+movitz-fixnum-shift+ :ecx)
    (:stc)
    (:ret)))

(define-primitive-function assert-1arg ()
  "1 argument there must be."
  (with-inline-assembly (:returns :multiple-values)
    (:cmpb 1 :cl)
    (:jne 'fail)
    (:ret)
   fail
    (:int 100)))

(define-primitive-function assert-2args ()
  "2 arguments there must be."
  (with-inline-assembly (:returns :multiple-values)
    (:cmpb 2 :cl)
    (:jne 'fail)
    (:ret)
   fail
    (:int 100)))

(define-primitive-function assert-3args ()
  "3 arguments there must be."
  (with-inline-assembly (:returns :multiple-values)
    (:cmpb 3 :cl)
    (:jne 'fail)
    (:ret)
   fail
    (:int 100)))

(define-primitive-function decode-args-1or2 ()
  "1 or 2 arguments there must be."
  ;; Not that we are not overly concerned about efficiency here,
  ;; because this is only a last-resort (odd-case) trampoline.
  ;; Usually the 1 or 2 entrypoints will be called directly,
  ;; or if there's an error speed really is of no concern.
  ;; This function MUST only be called when the code-vector
  ;; in fact implements special entry-points for 1 and 2 args..
  (with-inline-assembly (:returns :multiple-values)
    (:cmpb 1 :cl)
    (:jne 'not-one)
    (:jmp (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))
   not-one
    (:cmpb 2 :cl)
    (:jne 'not-two)
    (:jmp (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op)))
   not-two
    (:int 100)))


;;;;;;

(define-primitive-function ret-trampoline ()
  "This is the global RET trampoline, used to achieve stack discipline."
  (with-inline-assembly (:returns :multiple-values)
    (:ret)))

(define-primitive-function dynamic-jump-next ()
  "Transfer control to (next) dynamic control transfer target in EDX.
Final target is in raw-scratch0. Doesn't modify current-values."
  (with-inline-assembly (:returns :non-local-exit)
    (:movl :edi :esi)			; before bumping ESP, remove reference to funobj..
					; ..in case it's stack-allocated.
    (:locally (:movl :edx (:edi (:edi-offset scratch1)))) ; non-local stack-mode target entry.
    (:movl :edi :ebp)			; enter non-local jump stack mode.
    (:movl :edx :esp)			; 
    (:movl (:esp) :edx)			; target stack-frame EBP
    (:movl (:edx -4) :esi)		; get target funobj into ESI
    (:movl (:esp 8) :edx)		; target jumper number
    (:jmp (:esi :edx (:offset movitz-funobj constant0)))))

(define-primitive-function copy-funobj-code-vector-slots ()
  "Copy the (unsafe) code-vector and jumper slots of the funobj in EAX to that in EBX."
  ;; Set up thread-atomical execution
  (with-inline-assembly (:returns :eax)
    (:locally (:movl #.(movitz::atomically-continuation-simple-pf 'copy-funobj-code-vector-slots)
		     (:edi (:edi-offset atomically-continuation))))
    (:movl (:eax (:offset movitz-funobj code-vector)) :ecx)
    (:movl :ecx (:ebx (:offset movitz-funobj code-vector)))

    (:movl (:eax (:offset movitz-funobj code-vector%1op)) :ecx)
    (:movl :ecx (:ebx (:offset movitz-funobj code-vector%1op)))    

    (:movl (:eax (:offset movitz-funobj code-vector%2op)) :ecx)
    (:movl :ecx (:ebx (:offset movitz-funobj code-vector%2op)))    

    (:movl (:eax (:offset movitz-funobj code-vector%3op)) :ecx)
    (:movl :ecx (:ebx (:offset movitz-funobj code-vector%3op)))
    
    (:movl (:eax (:offset movitz-funobj num-jumpers)) :edx)
    (:andl #xffff :edx)
    (:jnz 'copy-jumpers)
    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
    (:ret)
   copy-jumpers
    (:movl (:eax :edx (:offset movitz-funobj constant0 -4)) :ecx)
    (:movl :ecx (:ebx :edx (:offset movitz-funobj constant0 -4)))
    (:subl 4 :edx)
    (:jnz 'copy-jumpers)
    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
    (:ret)))


(define-primitive-function decode-keyargs-default ()
  "Decode keyword arguments. Results are placed in stack-frame,
starting at (:ebp -16)."
  (with-inline-assembly (:returns :multiple-values)
    ;; ECX: numargs (u32)
    ;; EDX: arg-position of first keyword (fixnum)
    ;; (:ebp  -8) arg0 (if needed)
    ;; (:ebp -12) arg1 (if needed)

    (:shll 2 :ecx)
    (:subl :edx :ecx)			; find stop-pos
    (:jbe '(:sub-program (no-key-args)
	    (:xorl :eax :eax)		; No errors
	    (:ret)))

    (:locally (:movl :edx (:edi (:edi-offset scratch1)))) ; first-key-position
    ;; Error flags (0 = "not occurred", 1 = "occurred"):
    ;;   #x04: Unknown keyword.
    ;;   #x08: Keyword not a symbol.
    ;;   #x10: Odd number of keyword-args.
    ;;   #x20: :allow-other-keys (0 = nil, 1 = t).
    (:locally (:movl #x0 (:edi (:edi-offset scratch2)))) ; initial error flags
    (:cmpl 4 :edx)			; keys start at 0 or 1?
    (:jbe '(:sub-program (save-eax-ebx)
	    (:subl 8 :ecx)
	    (:jmp 'continue-save-eax-ebx)))
   continue-save-eax-ebx
    (:testl 4 :ecx)
    (:jnz '(:sub-program (odd-keywords)
	    ;; (:locally (:orl #x10 (:edi (:edi-offset scratch2))))
	    (:movl #x10 :eax)
	    (:int 72)))
   continue-from-odd-keywords
    (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0)))) ; save stop-pos
    (:xorl :edx :edx)			; EDX scans the args, last-to-first.

    (:cmpl :edx :ecx)			; might occur if key-arg-pos is 0 or 1,
    (:jbe 'check-arg0-arg1)		; and numargs is 2 or 3.
    
   scan-args-loop
    ;; Load current argument keyword and value into EAX and EBX
    (:movl (:ebp :edx 12) :eax)
    (:movl (:ebp :edx 8) :ebx)
    
   start-keyword-search
    ;; EAX: (presumed) keyword, EBX corresponding value.
    (:globally (:cmpl :eax (:edi (:edi-offset allow-other-keys-symbol))))
    (:je '(:sub-program (found-allow-other-keys)
	   (:locally (:andl #x-21 (:edi (:edi-offset scratch2)))) ; Signal :allow-other-keys nil
	   (:cmpl :edi :ebx)
	   (:je 'finished-keyword-search)
	   (:locally (:orl #x20 (:edi (:edi-offset scratch2)))) ; Signal :allow-other-keys t
	   (:jmp 'start-keyword-search-symbol)))
    (:leal (:eax -5) :ecx)
    (:testb 5 :cl)
    (:jnz '(:sub-program (keyword-not-symbol)
	    ;; (:locally (:orl #x8 (:edi (:edi-offset scratch2)))) ; Signal keyword-not-symbol
	    (:movl #x8 :eax)
	    (:int 72)))
   start-keyword-search-symbol
    (:movl (:esi (:offset movitz-funobj num-jumpers))
	   :ecx)
    (:andl #xfffc :ecx)
   position-search-loop
    ;; ECX scans funobj's keyword vector for position of keyword in EAX
    (:cmpl :eax (:esi :ecx (:offset movitz-funobj constant0)))
    (:je 'found-keyword)
    (:testb 1 (:esi :ecx (:offset movitz-funobj constant0)))
    (:jz '(:sub-program (keyword-not-fund)
	   (:locally (:orl 4 (:edi (:edi-offset scratch2)))) ; signal unknown-keyword
	   (:jmp 'finished-keyword-search)))
    (:addl 4 :ecx)
    (:jmp 'position-search-loop)
    
   found-keyword
    (:subw (:esi (:offset movitz-funobj num-jumpers)) :cx)
    (:negl :ecx)
    (:movl :ebx (:ebp -16 (:ecx 2)))
    (:globally (:movl (:edi (:edi-offset t-symbol)) :ebx))
    (:movl :ebx (:ebp -16 (:ecx 2) -4))
    
   finished-keyword-search
    (:addl 8 :edx)
    (:locally (:cmpl :edx (:edi (:edi-offset raw-scratch0)))) ; more args?
    (:ja 'scan-args-loop)

   check-arg0-arg1
    (:locally (:subl 4 (:edi (:edi-offset scratch1))))
    (:jc '(:sub-program (search-eax-ebx)
	   ;; Search one more keyword, in arg0 and arg1
	   (:movl (:ebp -8) :eax)
	   (:movl (:ebp -12) :ebx)
	   (:jmp 'start-keyword-search)))
    (:locally (:subl 4 (:edi (:edi-offset scratch1))))
    (:jc '(:sub-program (search-ebx)
	   ;; Search one more keyword, in arg1 and last on-stack.
	   (:movl (:ebp -12) :eax)
	   (:movl (:ebp :edx 8) :ebx)	    
	   (:jmp 'start-keyword-search)))
    ;; if there was :allow-other-keys t, clear the unknown-keyword error flag.
    (:locally (:movl (:edi (:edi-offset scratch2)) :eax))
    (:movl :eax :ecx)
    (:andl #x20 :ecx)
    (:shrl 3 :ecx)
    (:xorl 4 :ecx)
    (:andl :ecx :eax)
    (:ret)))

(define-primitive-function decode-keyargs-foo ()
  "foo"
  (with-inline-assembly (:returns :multiple-values)
    (:ret)))

