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
;;;; $Id: assembly-syntax.lisp,v 1.4 2004/09/06 10:07:03 ffjeld Exp $
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
  #+cmu (declare (optimize (safety 0)))	; Circumvent CMUCL bug in loop for-as-on-list.
  (loop for (p . tail) on prg
      as expander = (and (consp p)
			 (symbolp (car p))
			 (assembly-macro-expander (car p) amenv))
      if expander
      append (funcall expander p) into result
      else if (consp p)
      append (list (assembly-macroexpand p amenv)) into result
      else append (list p) into result
      when (not (listp tail))
      do (setf (cdr (last result)) tail)
	 (return result)
      finally (return result)))

