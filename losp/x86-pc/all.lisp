;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      all.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Sep 27 21:14:56 2001
;;;;                
;;;; $Id: all.lisp,v 1.5 2005/08/24 07:33:02 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :x86-pc/memory)
(require :x86-pc/keyboard)
(require :x86-pc/vga)
(require :x86-pc/bochs-vbe)
(require :x86-pc/textmode)
(require :x86-pc/pic8259)
(require :x86-pc/pit8253)
(require :x86-pc/interrupt)
(require :x86-pc/cmos)
(require :x86-pc/pci-device)
;; (require :x86-pc/serial)
(require :x86-pc/textmode-console)
(require :x86-pc/debugger)
(require :x86-pc/ata)
(provide :x86-pc/all)
