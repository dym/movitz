;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Filename:      defmacro-runtime.lisp
;;;; Author:        Frode Vatvedt Fjeld
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: defmacro-runtime.lisp,v 1.1 2008-03-17 08:01:03 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package #:muerte)

(provide :muerte/defmacro-runtime)

(defmacro defmacro (name lambda-list &body macro-body)
  (warn "rmacro: ~S" name)
  `(progn
     (defmacro/runtime ,name ,lambda-list ,@macro-body)
     (defmacro-compile-time ,name ,lambda-list ,macro-body)
     ',name))
