;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      cmos.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep 30 12:23:02 2002
;;;;                
;;;; $Id: cmos.lisp,v 1.3 2004/01/19 11:23:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :lib/named-integers)
(require :lib/bcd)
(provide :x86-pc/cmos)

(in-package muerte.x86-pc)

(defconstant +cmos-io-base+ #x70)

(define-named-integer rtc-register (:export-constants t)
  ;; These are BCD-encoded.
  (#x0 :second)
  (#x1 :alarm-second)
  (#x2 :minute)
  (#x3 :alarm-minute)
  (#x4 :hour)
  (#x5 :alarm-hour)
  (#x6 :day-of-week)			; (not used by the BIOS nor DOS)
  (#x7 :day-of-month)
  (#x8 :month)
  (#x9 :year))

(defun cmos-register (register)
  (setf (io-register8 +cmos-io-base+ 0) register)
  (io-register8 +cmos-io-base+ 1))

(defun rtc-register (register)
  "Read one of the CMOS Real-Time-Clock registers."
  (when (symbolp register)
    (setf register (named-integer 'rtc-register register)))
  (loop while (logbitp 7 (cmos-register #xa)))
  (bcd-to-integer (cmos-register register)))

(defun (setf cmos-register) (value register)
  (setf (io-register8 +cmos-io-base+ 0) register)
  (setf (io-register8 +cmos-io-base+ 1) value))


