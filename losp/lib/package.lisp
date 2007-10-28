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
;;;; Created at:    Fri Sep 27 17:24:11 2002
;;;;                
;;;; $Id: package.lisp,v 1.6 2004/11/24 14:20:55 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage #:muerte.lib
  (:nicknames #:lib)
  (:use #:common-lisp #:muerte)
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
	   #:add-u16-ones-complement
	   #:extract-zero-terminated-string
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
;;;	   #:*repl-level*
;;;	   #:*repl-prompter*
;;;	   #:*repl-prompt-context*
;;;	   #:*repl-print-format*
;;;	   #:*repl-readline-context*
;;;	   #:read-eval-print

           ;; scheduling
           *ticks-per-second*
           *scheduler-function*
           scheduler
           process-run-function
           process-wait
           process-wait-with-timeout
           process-enable
           process-disable
           process-enable-run-reason
           process-disable-run-reason
           process-enable-arrest-reason
           process-disable-arrest-reason
           clear-process-run-time
           process-kill
           process-block-with-timeout
           process-block
           process-unblock

	   ))

(provide :lib/package)

(in-package muerte.lib)

(defvar *scroll-offset* 0)
