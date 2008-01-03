;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   Assembly syntax etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm.lisp,v 1.2 2008/01/03 10:34:20 ffjeld Exp $
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
	   #:unresolved-symbol))

(in-package asm)

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

(define-condition unresolved-symbol ()
  ((symbol
    :initarg :symbol
    :reader unresolved-symbol))
  (:report (lambda (c s)
	     (format s "Unresolved symbol ~S." (unresolved-symbol c)))))
