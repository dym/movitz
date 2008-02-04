;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   Assembly syntax etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm.lisp,v 1.7 2008/02/04 07:45:08 ffjeld Exp $
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
	   #:*position-independent-p*
	   #:*sub-program-instructions*))

(in-package asm)

(defvar *pc* nil "Current program counter.")
(defvar *symtab* nil "Current symbol table.")
(defvar *instruction-compute-extra-prefix-map* nil)
(defvar *position-independent-p* t)
(defvar *sub-program-instructions* '(:jmp :ret)
  "Instruction operators after which to insert sub-programs.")

(deftype simple-symbol-reference ()
  '(cons (eql quote) (cons symbol null)))

(deftype sub-program-operand ()
  '(cons (eql quote)
    (cons
     (cons (eql :sub-program))
     null)))

(deftype symbol-reference ()
  '(or simple-symbol-reference sub-program-operand))

(defun sub-program-operand-p (expr)
  (typep expr 'sub-program-operand))

(defun sub-program-label (operand)
  (car (cadadr operand)))

(defun sub-program-program (operand)
  (cddadr operand))

(defun symbol-reference-symbol (expr)
  (etypecase expr
    (simple-symbol-reference
     (second expr))
    (sub-program-operand
     (sub-program-label expr))))

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
	(new-corrections nil)
	(sub-programs nil))
    (flet ((process-instruction (instruction)
	     (etypecase instruction
	       (symbol
		(let ((previous-definition (assoc instruction *symtab*)))
		  (cond
		    ((null previous-definition)
		     (push (cons instruction *pc*)
			   *symtab*))
		    ((assoc instruction new-corrections)
		     (break "prev-def ~S in new-corrections?? new: ~S, old: ~S"
			    instruction
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
		  code)))))
      (values (loop for instruction in proglist
		 for operands = (when (consp instruction)
				  instruction)
		 for operator = (when (consp instruction)
				  (let ((x (pop operands)))
				    (if (not (listp x)) x (pop operands))))
		 append (process-instruction instruction)		   
		 do (loop for operand in operands
		       do (when (sub-program-operand-p operand)
			    (push (cons (sub-program-label operand)
					(sub-program-program operand))
				  sub-programs)))
		 when (and (not (null sub-programs))
			   (member operator *sub-program-instructions*))
		 append (loop for sub-program in (nreverse sub-programs)
			   append (mapcan #'process-instruction sub-program)
			   finally (setf sub-programs nil))
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
	      *symtab*))))
