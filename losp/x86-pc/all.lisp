;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2003, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      all.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Sep 27 21:14:56 2001
;;;;                
;;;; $Id: all.lisp,v 1.1 2004/01/13 11:05:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage muerte.x86-pc)
(in-package muerte.x86-pc)

(require :x86-pc/memory)
(require :x86-pc/keyboard)
(require :x86-pc/vga)
(require :x86-pc/textmode)
(require :x86-pc/pic8259)
(require :x86-pc/pit8253)
(require :x86-pc/interrupt)
(require :x86-pc/cmos)
;; (require :x86-pc/serial)
(require :x86-pc/textmode-console)
(require :x86-pc/debugger)

(provide :x86-pc/all)
