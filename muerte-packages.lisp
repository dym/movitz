;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      muerte-packages.lisp
;;;; Description:   Defpackages.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Feb 13 19:25:41 2004
;;;;                
;;;; $Id: muerte-packages.lisp,v 1.1 2004/02/13 22:10:34 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage muerte.lib
  (:use muerte.cl muerte)
  (:export #:*scroll-offset*
	   #:cursor-x cursor-y
	   #:console-width console-height
	   #:console-char
	   #:scroll-down
	   #:clear-line
	   #:local-echo-p
	   #:with-saved-excursion
	   
	   ;; :lib/bcd
	   #:bcd-to-integer
	   #:integer-to-bcd

	   ;; :lib/console
	   #:console
	   #:console-width
	   #:console-height
	   #:cursor-x
	   #:cursor-y
	   #:console-char
	   #:scroll-down
	   #:put-string
	   #:clear-line
	   #:clear-console
	   #:local-echo-p
	   #:with-saved-excursion
	   
	   ;; :lib/misc
	   #:checksum-octets
	   #:make-counter-u32
	   #:u32-add
	   
	   ;; :lib/named-integers
	   #:define-named-integer
	   #:named-integer-case
	   #:named-integer
	   #:integer-name
	   #:name->integer
	   #:names->integer
	   #:with-named-integers-syntax
	   
	   ;; :lib/repl
	   #:*repl-level*
	   #:*repl-prompter*
	   #:*repl-prompt-context*
	   #:*repl-print-format*
	   #:*repl-readline-context*
	   #:read-eval-print
	   ))

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
	   
	   #:pic8259-irq-mask
	   #:pic8259-end-of-interrupt
	   #:init-pic8259
	   ))

(defpackage muerte.x86-pc.keyboard
  (:use muerte.cl muerte muerte.lib muerte.x86-pc)
  (:export poll-char
	   ;; read-char
	   poll-keypress
	   read-keypress
	   set-leds
	   cpu-reset))

(defpackage muerte.ethernet 
  (:use muerte.cl muerte muerte.lib)
  (:export #:make-ethernet-packet
	   #:ether-destination
	   #:ether-source
	   #:ether-type
	   #:ethernet-device
	   #:transmit
	   #:receive
	   #:packet-error
	   #:packet
	   #:packet-available-p
	   #:mac-address
	   #:accept-broadcasts-p
	   #:accept-multicast-addresses
	   #:promiscuous-p
	   #:pprint-mac
	   #:ether-mac-vendor
	   #:format-ethernet-packet
	   #:ether-802.3-p
	   #:ether-802.3-llc-type
	   #:ether-802.3-llc-dsap
	   #:ether-802.3-llc-ssap
	   #:ether-802.3-snap-p
	   #:ether-802.3-snap-type
	   #:+source-mac+
	   #:+destination-mac+
	   #:+max-ethernet-frame-size+
	   #:+min-ethernet-frame-size+
	   #:+broadcast-address+))

(defpackage muerte.ip4
  (:use muerte.cl muerte muerte.ethernet muerte.lib)
  (:export #:pprint-ip4
	   #:ip4-test
	   #:ip4-free))

(defpackage muerte.ip6
  (:use #:muerte.cl #:muerte.lib #:muerte.x86-pc #:muerte.ethernet)
  (:export #:packet-version
	   #:packet-source
	   #:packet-destination
	   #:packet-length
	   #:packet-traffic-class
	   #:packet-next-header
	   #:packet-flow-label
	   #:packet-hop-limit

	   #:pprint-ip6
	   #:ip6-test
	   #:ip6-free
	   ))

(defpackage muerte.readline
  (:use #:muerte.cl #:muerte.lib)
  (:export #:readline
	   #:readline-buffer
	   #:make-readline-buffer
	   #:readline-buffer-string
	   #:readline-buffer-cursor-position
	   #:readline-buffer-cursor-end
	   #:make-readline-context
	   #:contextual-readline
	   #:complete-symbol-name))

(defpackage muerte.debug
  (:use #:muerte.cl #:muerte #:muerte.x86-pc)
  (:export #:*debugger-function*
	   #:*debugger-condition*
	   #:*backtrace-conflate-names*
	   #:*backtrace-do-conflate*
	   #:*backtrace-max-frames*
	   #:*backtrace-max-args*
	   #:*backtrace-on-error*
	   #:*backtrace-stack-frame-barrier*
	   #:*backtrace-do-fresh-lines*
	   #:*backtrace-be-spartan-p*
	   #:*backtrace-print-length*
	   #:*backtrace-print-level*
	   #:backtrace
	   ))

(defpackage muerte.toplevel
  (:use #:muerte.cl #:muerte)
  (:export #:define-toplevel-command
	   #:invoke-toplevel-command
	   #:*toplevel-commands*))

(defpackage muerte.init
  (:use muerte.cl muerte muerte.lib
	muerte.x86-pc
	muerte.readline
	muerte.toplevel
;;;	muerte.ethernet
;;;	muerte.ip6
;;;	muerte.ip4
	muerte.mop
	muerte.debug
	#+ignore muerte.x86-pc.serial))