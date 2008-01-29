;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   Assembly syntax etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm.lisp,v 1.3 2008/01/29 22:04:31 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage asm
  (:use :common-lisp)
  (:export #:symbol-reference-p
	   #:symbol-reference
	   #:symbol-reference-symbol
	   #:immediate-p
	   #:immediate-operand
	   #:indirect-operand-p
	   #:indirect-operand
	   #:register-operand
	   #:unresolved-symbol
	   #:pc-relative-operand
	   #:proglist-encode
	   #:*pc*
	   #:*symtab*))

(in-package asm)

(defvar *pc* nil "Current program counter.")
(defvar *symtab* nil "Current symbol table.")

(deftype symbol-reference ()
  '(cons (eql quote) (cons symbol null)))

(defun symbol-reference-p (expr)
  (typep expr 'symbol-reference))

(defun symbol-reference-symbol (expr)
  (check-type expr symbol-reference)
  (second expr))

(deftype immediate-operand ()
  '(or integer symbol-reference))

(defun immediate-p (expr)
  (typep expr 'immediate-operand))

(deftype register-operand ()
  'keyword)

(defun register-p (operand)
  (typep operand 'register-operand))

(deftype indirect-operand ()
  '(and cons (not (cons (eql quote)))))

(defun indirect-operand-p (operand)
  (typep operand 'indirect-operand))

(deftype pc-relative-operand ()
  '(cons (eql :pc+)))

(defun pc-relative-operand-p (operand)
  (typep operand 'pc-relative-operand))

(define-condition unresolved-symbol ()
  ((symbol
    :initarg :symbol
    :reader unresolved-symbol))
  (:report (lambda (c s)
	     (format s "Unresolved symbol ~S." (unresolved-symbol c)))))


;;;;;;;;;;;;


(defun proglist-encode (proglist &key symtab (pc 0) (encoder (find-symbol (string '#:encode-instruction) '#:asm-x86)))
  (let ((*pc* pc)
	(*symtab* symtab))
    (loop for instruction in proglist
       appending
	 (etypecase instruction
	   (symbol
	    (when (assoc instruction *symtab*)
	      (error "Label ~S doubly defined." instruction))
	    (push (cons instruction *pc*)
		  *symtab*)
	    nil)
	   (cons
	    (let ((code (funcall encoder instruction)))
	      (incf *pc* (length code))
	      code))))))
