;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      primitive-functions.lisp
;;;; Description:   Some primitive-functions of the basic run-time
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Oct  2 21:02:18 2001
;;;;                
;;;; $Id: primitive-functions.lisp,v 1.17 2004/05/21 09:41:11 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/primitive-functions)

(in-package muerte)

(defmacro define-primitive-function (function-name lambda-list docstring &body body)
  (declare (ignore lambda-list))
  (assert (stringp docstring) (docstring)
    "Mandatory docstring for define-primitive-function.")
  `(make-primitive-function ,function-name ,docstring
			    ,(cons 'cl:progn body)))

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
       (:movl (:esi ,(bt:slot-offset 'movitz::movitz-funobj-standard-gf
				     (intern (symbol-name to) :movitz))) :esi)
       (:jmp (:esi ,(bt:slot-offset 'movitz::movitz-funobj
				    (intern (symbol-name forward) :movitz)))))))
  
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
;;;    4: tag = #:unbound (unique value that cannot be a catch tag)
;;;    0: binding name/symbol

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


(define-primitive-function dynamic-locate-catch-tag (tag)
  "Search the dynamic environment for a catch slot matching <tag> in EAX.
If EBX is not zero, only match that exact dynamic context (which presumably
was located earlier by other means).
Iff a tag is found, any intervening unwind-protect cleanup-forms are executed, and
this functions returns with EAX pointing to the dynamic-slot for tag, and with carry set.
When the tag is not found, no cleanup-forms are executed, and carry is cleared upon return,
with EAX still holding the tag."
  (with-inline-assembly (:returns :push)
    (:pushl :ebp)
    (:movl :esp :ebp)			; set up a pseudo stack-frame
    (:pushl :esi)			; for consistency
    
    (:globally (:movl (:edi (:edi-offset unwind-protect-tag)) :edx))
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))

   search-loop
    (:jecxz 'search-failed)
    
    (:cmpl :eax (:ecx 4))		; is env-slot in ECX == tag?
    (:jne 'mismatch)
    
    (:cmpl :ecx :ebx)
    (:je 'success)
    (:testl :ebx :ebx)
    (:jz 'success)

   mismatch
    (:cmpl :edx (:ecx 4))		; is env-slot in ECX == unwind-protect?
    (:jne 'not-unwind-protect)
    (:pushl :ecx)			; ..then save env-slot (in pseudo stack-frame)

   not-unwind-protect
    (:movl (:ecx 12) :ecx)		; get parent
    (:jmp 'search-loop)
    
   success
    (:pushl 0)				; mark, meaning next slot is ``the'' target slot.
    (:pushl :ecx)			; save the found env-slot

    ;; Now execute any unwind-protect cleanup-forms we encountered.
    ;; We are still inside the pseudo stack-frame.
    (:leal (:ebp -8) :edx)		; EDX points to the current dynamic-slot-slot

   unwind-loop
    (:movl (:edx) :eax)			; next dynamic-slot to unwind
    (:testl :eax :eax)			; is this the last entry?
    (:jz 'unwind-done)
    (:pushl :ebp)			; save EBP
    (:pushl :edx)			; and EDX
    (:movl (:eax 12) :ebx)		; unwind dynamic-env..
    (:locally (:movl :ebx (:edi (:edi-offset dynamic-env))))
    (:movl (:eax 0) :ebp)		; install clean-up's stack-frame (but keep our ESP)
    (:movl (:ebp -4) :esi)		; ..and install clean-up's funobj in ESI
    (:movl (:eax 8) :edx)
    (:call (:esi :edx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)))
    (:popl :edx)			; restoure our EDX
    (:popl :ebp)			; restore our EBP
    (:subl 4 :edx)			; ..slide EDX to next position inside stack-frame.
    (:jmp 'unwind-loop)

   unwind-done
    (:movl (:edx -4) :eax)		; the final dyamic-slot target.
    (:leave)				; exit pseudo stack-frame
    (:movl (:ebp -4) :esi)
    (:stc)				; signal success
    (:ret)				; return
    
   search-failed
    (:clc)				; signal failure
    (:leave)				; exit pseudo stack-frame
    (:movl (:ebp -4) :esi)
    (:ret)))				; return.
    
(define-primitive-function dynamic-unwind ()
  "Unwind ECX dynamic environment slots. Scratch EAX."
  (with-inline-assembly (:returns :nothing)
    (:jecxz 'done)
   loop
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :eax))
    (:testl :eax :eax)
    (:jz '(:sub-program () (:int 255)))	; end of dynamic environment???
    (:movl (:eax 12) :eax)		; get parent
    (:locally (:movl :eax (:edi (:edi-offset dynamic-env))))
    (:decl :ecx)
    (:jnz 'loop)
   done
    (:ret)))

(define-primitive-function dynamic-find-binding (symbol)
  "Search the stack for a dynamic binding of SYMBOL.
   On success, return Carry=1, and the address of the
   binding in EAX. On failure, return Carry=0 and EAX unmodified.
   Preserves EBX."
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    (:jecxz 'fail)
    (:cmpl :eax (:ecx))
    (:je 'success)
    (:locally (:movl (:edi (:edi-offset stack-top)) :edx))
   search-loop
    (:cmpl :edx (:ecx 12))
    (:jnc '(:sub-program () (:int 97)))
    (:movl (:ecx 12) :ecx)		; parent
    (:jecxz 'fail)
    (:cmpl :eax (:ecx))			; compare name
    (:jne 'search-loop)
    ;; fall through on success
   success
    (:leal (:ecx 8) :eax)		; location of binding value cell
    (:stc)
    (:ret)
    
   fail
    (:clc)
    (:ret)))
    
(define-primitive-function dynamic-load (symbol)
  "Load the dynamic value of SYMBOL into EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    (:jecxz 'no-stack-binding)
    (:cmpl :eax (:ecx))
    (:je 'success)
   search-loop
    (:movl (:ecx 12) :ecx)		; parent
    (:jecxz 'no-stack-binding)
    (:cmpl :eax (:ecx))			; compare name
    (:jne 'search-loop)
    ;; fall through on success
   success
    (:movl :eax :edx)			; Keep symbol in case it's unbound.
    (:movl (:ecx 8) :eax)
    (:globally (:cmpl (:edi (:edi-offset unbound-value)) :eax))
    (:je '(:sub-program (unbound) (:int 99)))
    (:ret)
   no-stack-binding
    ;; take the global value of SYMBOL, compare it against unbond-value
    (:movl :eax :edx)			; Keep symbol in case it's unbound.
    (:movl (:eax #.(bt:slot-offset 'movitz:movitz-symbol 'movitz::value)) :eax)
    (:globally (:cmpl (:edi (:edi-offset unbound-value)) :eax))
    (:je '(:sub-program (unbound) (:int 99)))
    (:ret)))

(define-primitive-function dynamic-store (symbol value)
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
    (:movl :ebx (:eax #.(bt:slot-offset 'movitz::movitz-symbol 'movitz::value)))
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

(define-primitive-function resolve-key-args (pos)
  ""
  ;; 1. Match each provided argument.
  (with-inline-assembly (:returns :multiple-values)
    (:leal (:ebp (:ecx 4) -4) :edx)
    (:movl (:edx) :eax)
    
    
    ))


;;;(define-primitive-function trampoline-restify-dynamic-extent-at0%2op ()
;;;  "Process &rest at position 0 in lambda-list, when 2 args are provided (ECX=2 is implied).
;;;EAX: arg0, EBX: arg1, Returns list in EAX and 2 in ECX.
;;;This is a special case of restify-dynamic-extent."
;;;  (with-inline-assembly (:returns :nothing)
;;;    (:popl :edx)			; return address
;;;    (:pushl :edi)
;;;    (:popl :edi)
;;;    (:andl -8 :esp)
;;;    (:pushl :ebx)			; cadr
;;;    (:pushl :edi)			; cddr
;;;    (:pushl :eax)			; car
;;;    (:movl :esp :eax)
;;;    (:subl 7 :eax)
;;;    (:pushl :eax)
;;;    (:addl 8 :eax)
;;;    (:movl 2 :ecx)
;;;    (:ret)))
  

(define-primitive-function restify-dynamic-extent ()
  "Process &rest.
EAX: arg0, EBX: arg1, ECX: numargs, EDX: rest-position,
EBP: stack-frame with rest of arguments, as per calling conventions.
Returns list in EAX and preserves numargs in ECX."
  (with-inline-assembly (:returns :nothing)
    (:cmpl :edx :ecx)
    (:jle '(:sub-program ()
	    (:movl :edi :eax) (:ret)))	; no rest at all.

    ;; Pop the return address into (:esp -8) and (:esp -12).
    (:popl (:esp -8))
    (:subl 4 :esp)
    (:popl (:esp -12))
	     
    (:pushl :edi)
    (:popl :edi)
    ;; Now the stack (below) looks like this:
    ;; (:esp 0) = ???
    ;; (:esp -4) = EDI
    ;; (:esp -8) = Return address
    ;; (:esp -12) = Return address

    (:andl -8 :esp)			; align stack to 8 (subtracts 4 when required)

    ;; We now know the return address is in (:esp -8).
    
    (:testl :edx :edx)
    (:jnz 'rest-pos-not-zero)		; arg0 doesn't go into rest.

    (:pushl :esp)			; cdr
    (:subl 15 (:esp))

    (:subl 4 :esp)
    (:popl (:esp -12))			; keep return address in (:esp -8)
    
    (:pushl :eax)			; car = eax

    (:movl :esp :eax)
    (:incl :eax)			; store head of list in eax.

    (:incl :edx)
    (:cmpl :edx :ecx)
    (:je '(:sub-program (done-early)
	   (:movl :edi (:esp 4))	; terminate list
	   (:movl (:esp -8) :ebx)	; load return address into ebx
	   (:jmp :ebx)))		; return
    (:jmp 'rest-pos-was-zero)
    
   rest-pos-not-zero
    (:leal (:esp -7) :eax)		; store head of list in eax.

   rest-pos-was-zero
    (:cmpl 1 :edx)
    (:jnz 'rest-pos-not-one-or-zero)

    (:pushl :esp)
    (:subl 15 (:esp))			; cdr

    (:subl 4 :esp)
    (:popl (:esp -12))			; keep return address in (:esp -8)

    (:pushl :ebx)			; car = ebx

    (:incl :edx)
    (:cmpl :edx :ecx)
    (:je 'done-early)

   rest-pos-not-one-or-zero

    (:movl (:esp -8) :ebx)		; load return address into ebx
    (:negl :edx)
    (:addl :ecx :edx)			; edx = (- ecx edx)
    
   loop
    (:pushl :esp)
    (:subl 15 (:esp))			; cdr
    (:pushl (:ebp (:edx 4) 4))		; car = next arg
    (:decl :edx)
    (:jnz 'loop)
    
   done
    
    (:movl :edi (:esp 4))		; terminate list
    (:jmp :ebx)))			; return

(define-primitive-function malloc ()
  "Stupid allocator.. Number of bytes in EBX. Result in EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:locally (:movl (:edi (:edi-offset malloc-buffer)) :eax))
    (:testb #xff :al)
    (:jnz '(:sub-program (not-initialized)
	    (:int 110)
	    (:halt)
	    (:jmp 'not-initialized)))
    (:addl 7 :ebx)
    (:andb #xf8 :bl)
    (:movl (:eax 4) :ecx)		; cons pointer to ECX
    (:leal (:ebx :ecx) :edx)		; new roof to EDX
    (:cmpl :edx (:eax))			; end of buffer?
    (:jl '(:sub-program (failed)
	   (:movl (:eax) :esi)
	   (:int 112)
	   (:halt)
	   (:jmp 'failed)))
    (:movl :edx (:eax 4))		; new cons pointer
    (:leal (:eax :ecx) :eax)
    (:ret)))

(defun malloc-initialize (buffer-start buffer-size)
  "BUFFER-START: the (fixnum) 4K address. BUFFER-SIZE: The size in 4K units."
  (check-type buffer-start integer)
  (check-type buffer-size integer)
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :eax) buffer-start)
    (:shll #.(cl:- 12 movitz::+movitz-fixnum-shift+) :eax)
    (:locally (:movl :eax (:edi (:edi-offset malloc-buffer))))
    (:compile-form (:result-mode :ebx) buffer-size)
    (:shll #.(cl:- 12 movitz::+movitz-fixnum-shift+) :ebx)
    (:movl :ebx (:eax))			; roof pointern
    (:movl 16 (:eax 4))))		; cons pointer

(defun malloc-buffer-start ()
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset malloc-buffer)) :eax))
    (:testb 7 :al)
    (:jnz '(:sub-program ()
	    (:int 107)))))
  
(defun malloc-cons-pointer ()
  "Return current cons-pointer in 8-byte units since buffer-start."
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset malloc-buffer)) :eax))
    (:movl (:eax 4) :eax)
    (:testb 7 :al)
    (:jnz '(:sub-program ()
	    (:int 107)))
    (:shrl 1 :eax)))

(define-primitive-function fast-cons ()
  "Allocate a cons cell. Call with car in eax and cdr in ebx."
  (with-inline-assembly (:returns :multiple-values)
    (:xchgl :eax :ecx)
    (:locally (:movl (:edi (:edi-offset malloc-buffer)) :eax))
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
    (:incl :eax)
    (:ret)))

(define-primitive-function ensure-heap-cons-variable ()
  "Call with lended variable (a cons) in EAX. Preserves EDX."
  (with-inline-assembly (:returns :multiple-values)
    (:cmpl :ebp :eax)			; is cons above stack-frame?
    (:jge 'return-ok)
    (:cmpl :esp :eax)			; is cons below stack-frame?
    (:jl 'return-ok)
    ;; must migrate cell onto heap
    (:pushl :edx)
    (:movl (:eax 3) :ebx)		; cdr
    (:movl (:eax -1) :eax)		; car
    (:locally (:call (:edi (:edi-offset fast-cons))))
    (:popl :edx)
    return-ok
    (:ret)))

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
    (:movl (:eax #.(bt:slot-offset 'movitz::movitz-std-instance 'movitz::class))
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
    (:movl (:ebx #.(movitz::class-object-offset 'illegal-object)) :eax)
    (:jmp 'not-null)
   null
    (:movl (:ebx #.(movitz::class-object-offset 'null)) :eax)
   not-null
    (:ret)))

(define-primitive-function fast-class-of-other ()
  "Return the class of an other object."
  (with-inline-assembly (:returns :multiple-values)
    (:movl (:eax #.movitz:+other-type-offset+) :ecx)
    (:cmpb #.(movitz::tag :std-instance) :cl)
    (:jne 'not-std-instance)
    (:movl (:eax #.(bt:slot-offset 'movitz::movitz-std-instance 'movitz::class)) :eax)
    (:ret)
   not-std-instance
    (:cmpw #.(cl:+ (movitz::tag :funobj)
		   (cl:ash (bt:enum-value 'movitz::movitz-funobj-type :generic-function) 8))
	   :cx)
    (:jne 'not-std-gf-instance)
    (:movl (:eax #.(bt:slot-offset 'movitz::movitz-funobj-standard-gf 'movitz::standard-gf-class))
	   :eax)
    (:ret)
   not-std-gf-instance
    (:globally (:movl (:edi (:edi-offset complicated-class-of)) :esi))
    (:jmp (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))))

(defun complicated-class-of (object)
  (typecase object
    (std-instance
     (movitz-accessor object movitz-std-instance class))
    (standard-gf-instance
     (movitz-accessor object movitz-funobj-standard-gf standard-gf-class))
    (string
     (find-class 'string))
    (vector
     (find-class 'vector))
    (function
     (find-class 'function))
    (structure-object
     (find-class (structure-object-name object)))
    (character
     (find-class 'character))
    (run-time-context
     (find-class 'run-time-context))
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

(define-primitive-function push-current-values ()
  "Push all current return-values on the stack. And, return number
of values in ECX."
  (with-inline-assembly (:returns :multiple-values)
    (:jc 'maybe-not-exactly-one-value)
    (:popl :edx)
    (:movl 1 :ecx)
    (:pushl :eax)
    (:jmp :edx)				; return
   maybe-not-exactly-one-value
    ;; Set ECX=1 if CF=0
    (:popl :edx)			; return address
    (:jecxz 'done)
    (:pushl :eax)
    (:cmpl 1 :ecx)
    (:jbe 'done)
    (:pushl :ebx)
    (:cmpl 2 :ecx)
    (:jbe 'done)
    (:subl 2 :ecx)
    (:leal (:edi #.(movitz::global-constant-offset 'values)) :eax)
    (:cmpl 127 :ecx)
    (:ja '(:sub-program ()
	   (:int 62)))
   push-loop
    (:locally (:pushl (:eax)))
    (:addl 4 :eax)
    (:subl 1 :ecx)
    (:jnz 'push-loop)
   push-done
    (:locally (:movl (:edi (:edi-offset num-values)) :ecx))
    (:addl 2 :ecx)
   done
    (:jmp :edx)))

(define-primitive-function pop-current-values ()
  "Input: ECX is number of values. Pop values into the standard
location for the current multiple values (i.e. eax, ebx, and the values thread-wide array)."
  (with-inline-assembly (:returns :multiple-values)
    (:cmpl 1 :ecx)
    (:jb '(:sub-program (zero-values) (:stc) (:ret)))
    (:popl :edx)
    (:je '(:sub-program (one-value)
	   (:popl :eax)
	   (:clc)
	   (:jmp :edx)))
    (:cmpl 2 :ecx)
    (:je '(:sub-program (two-values)
	   (:popl :ebx)
	   (:popl :eax)
	   (:stc)
	   (:jmp :edx)))
    ;; three or more values
    (:subl 2 :ecx)
    (:locally (:movl :ecx (:edi (:edi-offset num-values))))
    (:subl 1 :ecx)
   pop-loop
    (:locally (:popl (:edi (:ecx 4) (:edi-offset values))))
    (:subl 1 :ecx)
    (:jnc 'pop-loop)
    (:locally (:movl (:edi (:edi-offset num-values)) :ecx))
    (:popl :ebx)
    (:popl :eax)
    (:addl 2 :ecx)
    (:stc)
    (:jmp :edx)))

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


