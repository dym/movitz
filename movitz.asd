;;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      movitz.asd
;;;; Description:   Movitz ASDF system definition.
;;;; Author:        Frode Vatvedt Fjeld <ffjeld@common-lisp.net>
;;;; Created at:    Thu Jan 15 18:40:58 2004
;;;;                
;;;; $Id: movitz.asd,v 1.1 2008/02/25 20:11:01 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(defpackage movitz-asd
  (:use :cl :asdf))

(in-package movitz-asd)

(defsystem movitz-asm
  :name "Movitz Assembler"
  :version "1.0"
  :maintainer "ffjeld@common-lisp.net"
  :author "Frode V. Fjeld"
  :license "BSD-like, see accopanying file COPYING."
  :description "An (dis-)assembler framework, with support for x86 in 16, 32, and 64-bit modes."
  :serial t
  :components ((:file "asm")
	       (:file "asm-x86")))

(defclass movitz-source-file (cl-source-file) ())

(defsystem movitz
  :name "Movitz"
  :version "0.1"
  :maintainer "ffjeld@common-lisp.net"
  :author "Frode V. Fjeld"
  :license "BSD-like, see accopanying file COPYING."
  :description "A compiler, run-time, and libraries for Common Lisp on the x86."
  :default-component-class movitz-source-file
  :serial t
  :depends-on (binary-types)
  :components ((:file "packages")
	       (:file "movitz")
	       (:file "parse")
	       (:file "eval")
	       (:file "environment")
	       (:file "compiler-types")
	       (:file "compiler-protocol")
	       (:file "storage-types")
	       (:file "multiboot")
	       (:file "bootblock")
	       (:file "image")
	       (:file "stream-image")
	       (:file "assembly-syntax")
	       (:file "compiler")
	       (:file "special-operators")
	       (:file "special-operators-cl")))


#+sbcl
(defmethod perform :around (op (file movitz-source-file))
  (handler-bind ((sb-ext:defconstant-uneql #'continue))
    (call-next-method)))
