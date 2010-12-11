;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   Assembly syntax etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm.lisp,v 1.18 2008-03-14 11:07:47 ffjeld Exp $
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
	   #:indirect-operand-offset
	   #:instruction-operands
	   #:instruction-operator
	   #:register-operand
	   #:resolve-operand
	   #:unresolved-symbol
	   #:retry-symbol-resolve
	   #:pc-relative-operand
	   #:assemble-proglist
	   #:disassemble-proglist
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
(defvar *sub-program-instructions* '(:jmp :ret :iretd)
  "Instruction operators after which to insert sub-programs.")

(defvar *anonymous-sub-program-identities* nil)

(defun quotep (x)
  "Is x a symbol (in any package) named 'quote'?"
  ;; This is required because of Movitz package-fiddling.
  (and (symbolp x)
       (string= x 'quote)))

(deftype simple-symbol-reference ()
  '(cons (satisfies quotep) (cons symbol null)))

(deftype sub-program-operand ()
  '(cons (satisfies quotep)
    (cons
     (cons (eql :sub-program))
     null)))

(deftype funcall-operand ()
  '(cons (satisfies quotep)
    (cons
     (cons (eql :funcall))
     null)))

(deftype symbol-reference ()
  '(or simple-symbol-reference sub-program-operand))

(defun sub-program-operand-p (expr)
  (typep expr 'sub-program-operand))

(defun sub-program-label (operand)
  (let ((x (cadadr operand)))
    (if (not (eq '() x))
	(car x)
	(cdr (or (assoc operand *anonymous-sub-program-identities*)
		 (car (push (cons operand (gensym "sub-program-"))
			    *anonymous-sub-program-identities*)))))))

(defun sub-program-program (operand)
  (cddadr operand))

(defun symbol-reference-symbol (expr)
  (etypecase expr
    (simple-symbol-reference
     (second expr))
    (sub-program-operand
     (sub-program-label expr))))

(defun funcall-operand-operator (operand)
  (cadadr operand))

(defun funcall-operand-operands (operand)
  (cddadr operand))

(deftype immediate-operand ()
  '(or integer symbol-reference funcall-operand))

(defun immediate-p (expr)
  (typep expr 'immediate-operand))

(deftype register-operand ()
  'keyword)

(defun register-p (operand)
  (typep operand 'register-operand))

(deftype indirect-operand ()
  '(and cons (not (cons (satisfies quotep)))))

(defun indirect-operand-p (operand)
  (typep operand 'indirect-operand))

(defun indirect-operand-offset (operand)
  (check-type operand indirect-operand)
  (reduce #'+ operand
	  :key (lambda (x)
		 (if (integerp x) x 0))))

(deftype pc-relative-operand ()
  '(cons (eql :pc+)))

(defun pc-relative-operand-p (operand)
  (typep operand 'pc-relative-operand))

(defun pc-relative-operand-offset (operand)
  (check-type operand pc-relative-operand)
  (second operand))

(define-condition unresolved-symbol ()
  ((symbol
    :initarg :symbol
    :reader unresolved-symbol))
  (:report (lambda (c s)
	     (format s "Unresolved symbol ~S." (unresolved-symbol c)))))



(defun resolve-operand (operand)
  (typecase operand
    (integer
     operand)
    (symbol-reference
     (let ((s (symbol-reference-symbol operand)))
       (loop (with-simple-restart (retry-symbol-resolve "Retry resolving ~S." s)
	       (return (cdr (or (assoc s *symtab*)
				(error 'unresolved-symbol 
				       :symbol s))))))))
    (funcall-operand
     (apply (funcall-operand-operator operand)
	    (mapcar #'resolve-operand
		    (funcall-operand-operands operand))))
    (t operand)))

;;;;;;;;;;;;

(defun assemble-proglist (proglist &key ((:symtab incoming-symtab) *symtab*) corrections (start-pc 0) (cpu-package '#:asm-x86))
  "Encode a proglist, using instruction-encoder in symbol assemble-instruction from cpu-package."
  (let ((encoder (find-symbol (string '#:assemble-instruction) cpu-package))
	(*pc* start-pc)
	(*symtab* (append incoming-symtab corrections))
	(*anonymous-sub-program-identities* *anonymous-sub-program-identities*)
	(assumptions nil)
	(new-corrections nil)
	(sub-programs nil))
    (flet ((process-instruction (instruction)
	     (etypecase instruction
	       ((or symbol integer) ; a label?
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
 			;; (warn "correcting ~S from ~D to ~D" instruction (cdr previous-definition) *pc*)
			(setf (cdr previous-definition) *pc*)
			(push previous-definition new-corrections))
		       ((< *pc* (cdr previous-definition))
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
	       (cons ; a bona fide instruction?
		(let ((code (funcall encoder instruction)))
		  (incf *pc* (length code))
		  code)))))
      (handler-bind
	  ((unresolved-symbol (lambda (c)
				(let ((a (cons (unresolved-symbol c) *pc*)))
				  ;; (warn "assuming ~S for ~S" (unresolved-symbol c) *pc*)
				  (push a assumptions)
				  (push a *symtab*)
				  (invoke-restart 'retry-symbol-resolve)))))
	(let ((code (loop for instruction in proglist
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
				 finally (setf sub-programs nil)))))
	  (cond
	    ((not (null assumptions))
	     (error "Undefined symbol~P: ~{~S~^, ~}"
		    (length assumptions)
		    (mapcar #'car assumptions)))
	    ((not (null new-corrections))
	     (assemble-proglist proglist
				:symtab incoming-symtab
				:start-pc start-pc
				:cpu-package cpu-package
				:corrections (nconc new-corrections corrections)))
	    (t (values code *symtab*))))))))

(defun instruction-operator (instruction)
  (if (listp (car instruction)) ; skip any instruction prefixes etc.
      (cadr instruction)
      (car instruction)))

(defun instruction-operands (instruction)
  (if (listp (car instruction)) ; skip any instruction prefixes etc.
      (cddr instruction)
      (cdr instruction)))

(defun instruction-modifiers (instruction)
  (if (listp (car instruction))
      (car instruction)
      nil))

(defun disassemble-proglist (code &key (cpu-package '#:asm-x86) (pc (or *pc* 0)) (symtab *symtab*) collect-data collect-labels)
  "Return a proglist (i.e. a list of instructions), or a list of (cons instruction data) if collect-data is true,
data being the octets corresponding to that instruction. Labels will be included in the proglist if collect-labels is true.
Secondarily, return the symtab."
  (let* ((instruction-disassembler (find-symbol (string '#:disassemble-instruction)
						cpu-package))
	 (proglist0 (loop while code
		       collect pc
		       collect (multiple-value-bind (instruction new-code)
				   (funcall instruction-disassembler
					    code)
				 (when (eq code new-code)
				   (loop-finish))
				 (let* ((data (loop until (eq code new-code)
						 do (incf pc)
						 collect (pop code)))
					(operands (instruction-operands instruction)))
				   (cons data
					 (if (notany #'pc-relative-operand-p operands)
					     instruction
					     (nconc (loop until (eq instruction operands)
						       collect (pop instruction))
						    (loop for operand in operands
						       collect (if (not (pc-relative-operand-p operand))
								   operand
								   (let* ((location (+ pc (pc-relative-operand-offset operand)))
									  (entry (or (rassoc location symtab)
										     (car (push (cons (gensym) location)
												symtab)))))
								     `(quote ,(car entry)))))))))))))
    (values (loop for (pc data-instruction) on proglist0 by #'cddr
	       for instruction = (cdr data-instruction)
	       for label = (when collect-labels
			     (rassoc pc symtab))
	       when label
	       collect (if (not collect-data)
			   (car label)
			   (cons nil (car label)))
	       collect (if (not collect-data)
			   instruction
			   data-instruction))
	    symtab)))

(defun disassemble-proglist* (code &key (cpu-package '#:asm-x86) (pc 0))
  "Print a human-readable disassembly of code."
  (multiple-value-bind (proglist symtab)
      (disassemble-proglist code
			    :cpu-package cpu-package
			    :collect-data t)
    (format t "~&~:{~4X: ~20<~{ ~2,'0X~}~;~> ~A~%~}"
	    (loop with pc = pc
	       for (data . instruction) in proglist
	       when (let ((x (find pc symtab :key #'cdr)))
		      (when x (list pc (list (format nil "      ~A" (car x))) "")))
	       collect it
	       collect (list pc data instruction)
	       do (incf pc (length data))))))
