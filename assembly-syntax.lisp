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
;;;; $Id: assembly-syntax.lisp,v 1.3 2004/04/21 15:05:39 ffjeld Exp $
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

(defun assembly-macroexpand (prg amenv)
  (let* ((fix-tail nil)
	 (new-prg
	  (loop for (p . tail) on prg
	      as expander = (and (consp p)
				 (symbolp (car p))
				 (assembly-macro-expander (car p) amenv))
	      if expander
	      append (funcall expander p)
	      else if (consp p)
	      append (list (assembly-macroexpand p amenv))
	      else append (list p)
	      unless (listp tail)
	      do (setf fix-tail tail))))
    (when fix-tail
      (setf (cdr (last new-prg)) fix-tail))
    new-prg))

