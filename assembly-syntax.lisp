;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      assembly-syntax.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Nov  9 17:34:37 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: assembly-syntax.lisp,v 1.2 2004/01/19 11:23:41 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defstruct assembly-macro-environment
  (expanders (make-hash-table :test #'eq)))

(defun assembly-macro-expander (symbol amenv)
  (gethash symbol (assembly-macro-environment-expanders amenv)))

(defun (setf assembly-macro-expander) (expander symbol amenv)
  (setf (gethash symbol (assembly-macro-environment-expanders amenv))
    expander))

;;;(defun assembly-macroexpand (prg amenv)
;;;  (cond
;;;   ((and (consp prg) (symbolp (car prg)))
;;;    (let ((expander (assembly-macro-expander (car prg) amenv)))
;;;      (if expander
;;;	  (assembly-macroexpand (funcall expander prg) amenv)
;;;	#0=(cons (assembly-macroexpand (car prg) amenv)
;;;		 (assembly-macroexpand (cdr prg) amenv)))))
;;;   ((consp prg) #0#)
;;;   (t prg)))

(defun assembly-macroexpand (prg amenv)
  (loop for p in prg
      as expander = (and (consp p)
			 (symbolp (car p))
			 (assembly-macro-expander (car p) amenv))
      if expander
      append (funcall expander p)
      else if (consp p)
      append (list (assembly-macroexpand p amenv))
      else append (list p)))

;;;(defmacro with-assembly-syntax (&body body)
;;;  `(let ((*readtable* (copy-readtable nil)))
;;;     (set-dispatch-macro-character

