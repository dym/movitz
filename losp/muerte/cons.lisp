;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      cons.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Dec  8 15:25:45 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: cons.lisp,v 1.8 2004/10/21 20:33:59 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/cons)

(in-package muerte)

(define-primitive-function fast-cdr-car (cell)
  "Compute both the car (into EBX) and the cdr (into EAX) of a cell."
  (with-inline-assembly (:returns :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax -1) :ebx)
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:ret)))

(define-primitive-function fast-car ()
  "This is the actual CAR code."
  (with-inline-assembly (:returns :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax -1) :eax)
    (:ret)))

(define-primitive-function fast-car-ebx ()
  "This is the actual CAR code.
Cons cell is in EBX, which is preserved."
  (with-inline-assembly (:returns :eax)
    (:leal (:ebx -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 66)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:ebx -1) :eax)
    (:ret)))

(define-primitive-function fast-cdr ()
  "This is the actual CDR code."
  (with-inline-assembly (:returns :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:ret)))

(define-primitive-function fast-cddr ()
  "This is the actual CDR code."
  (with-inline-assembly (:returns :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:ret)))

(define-primitive-function fast-cdddr ()
  "This is the actual CDR code."
  (with-inline-assembly (:returns :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program (not-cons) (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program (not-cons) (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program (not-cons) (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:ret)))

(define-primitive-function fast-cdr-ebx ()
  "This is the actual CDR code.
Cons cell is in EBX, which is preserved."
  (with-inline-assembly (:returns :eax)
    (:leal (:ebx -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:ebx 3) :eax)
    (:ret)))

;; Prefetching versions. Only works on .. PII or so and upwards.

(define-primitive-function prefetching-fast-cdr-car (cell)
  "Compute both the car and the cdr of a cell."
  (with-inline-assembly (:returns :eax)
    (:prefetch-nta (:eax))
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax -1) :ebx)
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:ret)))

(define-primitive-function prefetching-fast-car ()
  "This is the actual CAR code."
  (with-inline-assembly (:returns :eax)
    (:prefetch-nta (:eax))
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax -1) :eax)
    (:ret)))

(define-primitive-function prefetching-fast-car-ebx ()
  "This is the actual CAR code.
Cons cell is in EBX, which is preserved."
  (with-inline-assembly (:returns :eax)
    (:prefetch-nta (:ebx))
    (:leal (:ebx -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:ebx -1) :eax)
    (:ret)))

(define-primitive-function prefetching-fast-cdr ()
  "This is the actual CDR code."
  (with-inline-assembly (:returns :eax)
    (:prefetch-nta (:eax))
    (:leal (:eax -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program () (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax 3) :eax)
    (:prefetch-nta (:eax))
    (:ret)))

(define-primitive-function prefetching-fast-cdr-ebx ()
  "This is the actual CDR code.
Cons cell is in EBX, which is preserved."
  (with-inline-assembly (:returns :eax)
    (:prefetch-nta (:ebx))
    (:leal (:ebx -1) :ecx)
    (:testb 3 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:ebx 3) :eax)
    (:prefetch-nta (:eax))
    (:ret)))

(defun (setf car) (value cell)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :ebx) cell)
    (:compile-form (:result-mode :eax) value)
    (:leal (:ebx -1) :ecx)
    (:testb 7 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
     :movl :eax (:ebx -1))))

(defun (setf cdr) (value cell)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :ebx) cell)
    (:compile-form (:result-mode :eax) value)
    (:leal (:ebx -1) :ecx)
    (:testb 7 :cl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 61)))
    (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
     :movl :eax (:ebx 3))))

(defun car (x) (car x))
(defun cdr (x) (cdr x))

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))
(defun caaar (x) (car (car (car x))))
(defun caadr (x) (car (car (cdr x))))
(defun cadar (x) (car (cdr (car x))))
(defun caddr (x) (car (cdr (cdr x))))
(defun cdaar (x) (cdr (car (car x))))
(defun cdadr (x) (cdr (car (cdr x))))
(defun cddar (x) (cdr (cdr (car x))))
(defun cdddr (x) (cdr (cdr (cdr x))))
(defun caaaar (x) (car (car (car (car x)))))
(defun caaadr (x) (car (car (car (cdr x)))))
(defun caadar (x) (car (car (cdr (car x)))))
(defun caaddr (x) (car (car (cdr (cdr x)))))
(defun cadaar (x) (car (cdr (car (car x)))))
(defun cadadr (x) (car (cdr (car (cdr x)))))
(defun caddar (x) (car (cdr (cdr (car x)))))
(defun cadddr (x) (car (cdr (cdr (cdr x)))))
(defun cdaaar (x) (cdr (car (car (car x)))))
(defun cdaadr (x) (cdr (car (car (cdr x)))))
(defun cdadar (x) (cdr (car (cdr (car x)))))
(defun cdaddr (x) (cdr (car (cdr (cdr x)))))
(defun cddaar (x) (cdr (cdr (car (car x)))))
(defun cddadr (x) (cdr (cdr (car (cdr x)))))
(defun cdddar (x) (cdr (cdr (cdr (car x)))))        
(defun cddddr (x) (cdr (cdr (cdr (cdr x)))))

(defun (setf caar) (value list) (setf (car (car list)) value))
(defun (setf cadr) (value list) (setf (car (cdr list)) value))
(defun (setf cdar) (value list) (setf (cdr (car list)) value))
(defun (setf cddr) (value list) (setf (cdr (cdr list)) value))
(defun (setf caaar) (value list) (setf (car (car (car list))) value))
(defun (setf caadr) (value list) (setf (car (car (cdr list))) value))
(defun (setf cadar) (value list) (setf (car (cdr (car list))) value))
(defun (setf caddr) (value list) (setf (car (cdr (cdr list))) value))
(defun (setf cdaar) (value list) (setf (cdr (car (car list))) value))
(defun (setf cdadr) (value list) (setf (cdr (car (cdr list))) value))
(defun (setf cddar) (value list) (setf (cdr (cdr (car list))) value))
(defun (setf cdddr) (value list) (setf (cdr (cdr (cdr list))) value))
(defun (setf caaaar) (value list) (setf (car (car (car (car list)))) value))
(defun (setf caaadr) (value list) (setf (car (car (car (cdr list)))) value))
(defun (setf caadar) (value list) (setf (car (car (cdr (car list)))) value))
(defun (setf caaddr) (value list) (setf (car (car (cdr (cdr list)))) value))
(defun (setf cadaar) (value list) (setf (car (cdr (car (car list)))) value))
(defun (setf cadadr) (value list) (setf (car (cdr (car (cdr list)))) value))
(defun (setf caddar) (value list) (setf (car (cdr (cdr (car list)))) value))
(defun (setf cadddr) (value list) (setf (car (cdr (cdr (cdr list)))) value))
(defun (setf cdaaar) (value list) (setf (cdr (car (car (car list)))) value))
(defun (setf cdaadr) (value list) (setf (cdr (car (car (cdr list)))) value))
(defun (setf cdadar) (value list) (setf (cdr (car (cdr (car list)))) value))
(defun (setf cdaddr) (value list) (setf (cdr (car (cdr (cdr list)))) value))
(defun (setf cddaar) (value list) (setf (cdr (cdr (car (car list)))) value))
(defun (setf cddadr) (value list) (setf (cdr (cdr (car (cdr list)))) value))
(defun (setf cdddar) (value list) (setf (cdr (cdr (cdr (car list)))) value))
(defun (setf cddddr) (value list) (setf (cdr (cdr (cdr (cdr list)))) value))


(defun rplaca (cons object)
  (rplaca cons object))

(defun rplacd (cons object)
  (rplacd cons object))

(defun cons (car cdr)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) car)
    (:compile-form (:result-mode :ebx) cdr)
    (:call-local-pf fast-cons)))
