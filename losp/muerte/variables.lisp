;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      variables.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov  5 21:53:34 2003
;;;;                
;;;; $Id: variables.lisp,v 1.10 2006/04/10 11:58:27 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/variables)

(in-package muerte)

(defconstant lambda-list-keywords
    '(&allow-other-keys &aux &body &environment &key &optional &rest &whole))

(defvar * nil)
(defvar ** nil)
(defvar *** nil)

(defvar / nil)
(defvar // nil)
(defvar /// nil)

(defvar + nil)
(defvar ++ nil)
(defvar +++ nil)

(defvar *read-base* 10)
(defvar *package* nil)

(defparameter *debugger-hook* nil)
(defvar *active-condition-handlers* nil)
(defvar *multiboot-data* nil)

(defvar internal-time-units-per-second)

(defvar *gc-hooks* nil)

(defvar *load-pathname* nil)


(defvar most-positive-short-float 1000000)
(defvar most-positive-single-float 1000000)
(defvar most-positive-double-float 1000000)
(defvar most-positive-long-float 1000000)

(defvar short-float-epsilon 1/1000)
(defvar single-float-epsilon 1/1000)
(defvar double-float-epsilon 1/1000)
(defvar long-float-epsilon 1/1000)

(defvar short-float-negative-epsilon -1/1000)
(defvar single-float-negative-epsilon -1/1000)
(defvar double-float-negative-epsilon -1/1000)
(defvar long-float-negative-epsilon -1/1000)


(defconstant call-arguments-limit #xffff0)
(defconstant lambda-parameters-limit #x1000) ; ?

(defvar *print-pprint-dispatch* nil)

(declaim (special *build-number*))
