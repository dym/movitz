;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      all.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Sep 27 21:14:56 2001
;;;;                
;;;; $Id: all.lisp,v 1.2 2004/01/15 17:13:53 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
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
