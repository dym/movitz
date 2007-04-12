;;;;------------------ -*- movitz-mode: t -*--------------------------
;;;; 
;;;;    Copyright (C) 2007, Frode Vatvedt Fjeld
;;;; 
;;;; Filename:      shallow-binding.lisp
;;;; Description:   An implementation of shallow binding.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: shallow-binding.lisp,v 1.2 2007/04/12 16:09:27 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage lib.shallow-binding
  (:use common-lisp muerte)
  (:export #:install-shallow-binding
           #:deinstall-shallow-binding))

(provide :lib/shallow-binding)

(in-package lib.shallow-binding)

(define-primitive-function dynamic-variable-install-shallow ()
  "Install each dynamic binding entry between that in ESP
 (offset by 4 due to the call to this primitive-function!)
and current dynamic-env. Preserve EDX."
  (with-inline-assembly (:returns :nothing)
    (:leal (:esp 4) :ecx)		; first entry
   install-loop
    (:locally
      (:cmpl :ecx (:edi (:edi-offset dynamic-env))))
    (:je 'install-completed)
    (:movl (:ecx 0) :eax)		; binding's name
    (:movl (:eax (:offset movitz-symbol value))
	   :ebx)			; old value into EBX
    (:movl :ebx (:ecx 4))		; save old value in scratch
    (:movl (:ecx 8) :ebx)		; new value..
    (:movl :ebx				; ..into symbol's value slot
	   (:eax (:offset movitz-symbol value)))
    (:movl (:ecx 12) :ecx)		; iterate next binding
    (:jmp 'install-loop)
   install-completed
    (:ret)))

(define-primitive-function dynamic-variable-uninstall-shallow (dynamic-env)
  "Uninstall each dynamic binding between 'here' (i.e. the current 
dynamic environment pointer) and the dynamic-env pointer provided in EDX.
This must be done without affecting 'current values'! (i.e. eax, ebx, ecx, or CF),
and also EDX must be preserved."
  (with-inline-assembly (:returns :nothing)
    (:jc 'ecx-ok)
    (:movl 1 :ecx)
   ecx-ok
    (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0))))
    (:locally (:movl :eax (:edi (:edi-offset scratch1))))
    (:locally (:movl :ebx (:edi (:edi-offset scratch2))))
    
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
   uninstall-loop
    (:cmpl :edx :ecx)
    (:je 'uninstall-completed)
    (:movl (:ecx 0) :eax)		; symbol
    (:movl (:ecx 4) :ebx)		; old value
    (:movl :ebx (:eax (:offset movitz-symbol value))) ; reload old value
    (:movl (:ecx 12) :ecx)
    (:jmp 'uninstall-loop)
   uninstall-completed

    (:locally (:movl (:edi (:edi-offset raw-scratch0)) :ecx))
    (:locally (:movl (:edi (:edi-offset scratch1)) :eax))
    (:locally (:movl (:edi (:edi-offset scratch2)) :ebx))
    (:stc)
    (:ret)))

(define-primitive-function dynamic-unwind-next-shallow (dynamic-env)
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
    (:locally (:movl :eax (:edi (:edi-offset scratch2)))) ; Free up EAX
    ;; (:globally (:movl (:edi (:edi-offset unwind-protect-tag)) :ebx))
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    
   search-loop
    (:jecxz '(:sub-program () (:int 63)))
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))

    (:locally (:cmpl :ecx (:edi (:edi-offset scratch2))))
    (:je 'found-dynamic-env)

    (:movl (:ecx 4) :ebx)
    (:globally (:cmpl :ebx (:edi (:edi-offset unwind-protect-tag))))
    (:je 'found-unwind-protect)

    ;; If this entry is a dynamic variable binding, uninstall it.
    (:movl (:ecx) :eax)			; symbol?
    (:testb 3 :al)			;
    (:jz 'not-variable-binding)		; not symbol?

    (:movl :ebx (:eax (:offset movitz-symbol value))) ; uninstall.
   not-variable-binding
    (:movl (:ecx 12) :ecx)		; proceed search
    (:jmp 'search-loop)
   found-unwind-protect
    (:stc)
   found-dynamic-env
    (:movl :ecx :eax)
    (:ret)))

(define-primitive-function dynamic-variable-lookup-shallow (symbol)
  "Load the dynamic value of SYMBOL into EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:movl (:ebx (:offset movitz-symbol value)) :eax)
    (:ret)))

(define-primitive-function dynamic-variable-store-shallow (symbol value)
  "Store VALUE (ebx) in the dynamic binding of SYMBOL (eax).
   Preserves EBX and EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:movl :ebx (:eax (:offset movitz-symbol value)))
    (:ret)))

(defun install-shallow-binding (&key quiet)
  (unless quiet
    (warn "Installing shallow-binding strategy.."))
  (without-interrupts
    (macrolet ((install (slot function)
		 `(setf (%run-time-context-slot nil ',slot) (symbol-value ',function))))
      (install muerte:dynamic-variable-install dynamic-variable-install-shallow)
      (install muerte:dynamic-variable-uninstall dynamic-variable-uninstall-shallow)
      (install muerte::dynamic-unwind-next dynamic-unwind-next-shallow)
      (install muerte::dynamic-variable-store dynamic-variable-store-shallow)
      (install muerte::dynamic-variable-lookup dynamic-variable-lookup-shallow))
    (labels ((install-shallow-env (env)
	       "We use this local function in order to install dynamic-env slots
                    in reverse order, by depth-first recursion."
	       (unless (eq 0 env)
		 (install-shallow-env (memref env 12))
		 (let ((name (memref env 0)))
		   (when (symbolp name)
		     (setf (memref env 4)
		       (%symbol-global-value name))
		     (setf (%symbol-global-value name)
		       (memref env 8)))))))
      (install-shallow-env (%run-time-context-slot nil 'muerte::dynamic-env))))
  (values))

(defun deinstall-shallow-binding (&key quiet)
  (unless quiet
    (warn "Deinstalling shallow-binding strategy.."))
  (without-interrupts
    (macrolet ((install (slot)
		 `(setf (%run-time-context-slot nil ',slot) (symbol-value ',slot))))
      (install muerte:dynamic-variable-install)
      (install muerte:dynamic-variable-uninstall)
      (install muerte::dynamic-unwind-next)
      (install muerte::dynamic-variable-store)
      (install muerte::dynamic-variable-lookup))
    (loop for env = (%run-time-context-slot nil 'muerte::dynamic-env)
	then (memref env 12)
	while (plusp env)
	do (let ((name (memref env 0)))
	     (when (symbolp name)
	       (setf (%symbol-global-value name)
		 (memref env 4)))))
    (values)))
