;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   Assembly syntax etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm.lisp,v 1.6 2008/02/03 10:23:05 ffjeld Exp $
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
	   #:retry-symbol-resolve
	   #:pc-relative-operand
	   #:proglist-encode
	   #:*pc*
	   #:*symtab*
	   #:*instruction-compute-extra-prefix-map*
	   #:*position-independent-p*))

(in-package asm)

(defvar *pc* nil "Current program counter.")
(defvar *symtab* nil "Current symbol table.")
(defvar *instruction-compute-extra-prefix-map* nil)
(defvar *position-independent-p* t)

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


(defun proglist-encode (proglist &key corrections (start-pc 0) (cpu-package '#:asm-x86))
  "Encode a proglist, using instruction-encoder in symbol encode-instruction from cpu-package."
  (let ((encoder (find-symbol (string '#:encode-instruction) cpu-package))
	(*pc* start-pc)
	(*symtab* corrections)
	(assumptions nil)
	(new-corrections nil))
    (values (loop for instruction in proglist
	       appending
	       (etypecase instruction
		 (symbol
		  (let ((previous-definition (assoc instruction *symtab*)))
		    (cond
		      ((null previous-definition)
		       (push (cons instruction *pc*)
			     *symtab*))
		      ((assoc instruction new-corrections)
		       (error "prev-def in new-corrections?? new: ~S, old: ~S"
			      *pc*
			      (cdr (assoc instruction new-corrections))))
		      ((member previous-definition assumptions)
		       (setf (cdr previous-definition) *pc*)
		       (setf assumptions (delete previous-definition assumptions))
		       (push previous-definition new-corrections))
		      ((member previous-definition corrections)
		       (cond
			 ((> *pc* (cdr previous-definition))
;; 			  (warn "correcting ~S from ~D to ~D" instruction (cdr previous-definition) *pc*)
			  (setf (cdr previous-definition) *pc*)
			  (push previous-definition new-corrections))
			 ((< *pc* (cdr previous-definition))
;; 			  (warn "Definition for ~S shrunk from ~S to ~S (corrections: ~{~D~}."
;; 				instruction
;; 				(cdr previous-definition)
;; 				*pc*
;; 				corrections)
;; 			  (warn "prg: ~{~%~A~}" proglist)
;; 			  (warn "Definition for ~S shrunk from ~S to ~S."
;; 				instruction
;; 				(cdr previous-definition)
;; 				*pc*)
;; 			  (break "Definition for ~S shrunk from ~S to ~S."
;; 				 instruction
;; 				 (cdr previous-definition)
;; 				 *pc*)
			  (setf (cdr previous-definition) *pc*)
			  (push previous-definition new-corrections))))
		      (t (error "Label ~S doubly defined. Old value: ~S, new value: ~S"
				instruction
				(cdr previous-definition)
				*pc*))))
		  nil)
		 (cons
		  (let ((code (handler-bind
				  ((unresolved-symbol (lambda (c)
							(let ((a (cons (unresolved-symbol c) *pc*)))
;; 							  (warn "assuming ~S for ~S" (unresolved-symbol c) *pc*)
							  (push a assumptions)
							  (push a *symtab*)
							  (invoke-restart 'retry-symbol-resolve)))))
				(funcall encoder instruction))))
		    (incf *pc* (length code))
		    code)))
	       finally
	       (cond
		 ((not (null assumptions))
		  (error "Undefined symbol~P: ~{~S~^, ~}"
			 (length assumptions)
			 (mapcar #'car assumptions)))
		 ((not (null new-corrections))
		  (return (proglist-encode proglist
					   :start-pc start-pc
					   :cpu-package cpu-package
					   :corrections (nconc new-corrections corrections))))))
	    *symtab*)))
