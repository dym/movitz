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
;;;; $Id: variables.lisp,v 1.15 2008-07-09 20:00:37 ffjeld Exp $
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

(defvar - nil)
(defvar + nil)
(defvar ++ nil)
(defvar +++ nil)

(defvar *read-base* 10)
(defvar *read-eval* t)
(defvar *read-suppress* nil)
(defvar *package* nil)

(defvar *macroexpand-hook* 'funcall)
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
(defvar long-float-epsilon 1/10000)

(defconstant most-negative-short-float most-negative-fixnum)
(defconstant most-negative-single-float most-negative-fixnum)
(defconstant most-negative-long-float most-negative-fixnum)
(defconstant most-negative-double-float most-negative-fixnum)

(defconstant least-positive-short-float 1/100000)
(defconstant least-positive-single-float 1/100000)
(defconstant least-positive-double-float 1/100000)
(defconstant least-positive-long-float 1/100000)

(defconstant least-negative-short-float -1/100000)
(defconstant least-negative-single-float -1/100000)
(defconstant least-negative-double-float -1/100000)
(defconstant least-negative-long-float -1/100000)

(defconstant call-arguments-limit 512)
(defconstant lambda-parameters-limit 512) ; ?

(defvar *print-pprint-dispatch* nil)

(defvar *build-number*) ; set at bootup

(defvar *features* '(:movitz))
(defvar *modules* nil)

(defvar *compile-file-pathname* nil)
(defvar *compile-file-truename* nil)
(defvar *compile-print* nil)
(defvar *compile-verbose* nil)
(defvar *load-print* nil)
(defvar *load-verbose* nil)
(defvar *load-truename* nil)
(defvar *default-pathname-defaults* #p"")
