;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      package.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Oct  2 20:30:28 2001
;;;;                
;;;; $Id: package.lisp,v 1.4 2004/04/21 16:24:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :x86-pc/package)

(defpackage muerte.x86-pc
  (:use muerte.cl muerte.lib muerte)
  (:export #:io-space-device
	   #:io-space
	   #:device-name
	   #:allocate-io-space
	   #:free-io-space
	   #:io-space-occupants
	   #:with-io-space-lock
	   #:make-io-space
	   #:reset-device
	   #:memory-size

	   #:vga-cursor-location
	   #:vga-crt-controller-register
	   #:vga-graphics-register
	   #:vga-memory-map
	   
	   #:rtc-register
	   #:cmos-register

	   #:idt-init
	   #:interrupt-handler
	   #:int-frame-ref
	   #:software-interrupt
	   #:*last-interrupt-frame*
	   
	   #:pit8253-timer-mode
	   #:pit8253-timer-count
	   
	   #:+pit8253-frequency+
	   #:+pit8253-nanosecond-period+
	   
	   #:textmode-console
	   #:vga-text-console
	   #:set-textmode
	   #:+vga-state-80x25+
	   #:+vga-state-80x50+
	   #:+vga-state-40x25+
	   #:+vga-state-40x50+
	   #:+vga-state-90x30+
	   #:+vga-state-90x60+
	   
	   #:pic8259-irq-mask
	   #:pic8259-end-of-interrupt
	   #:init-pic8259
	   ))
