;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pit8253.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Jan 15 11:30:55 2002
;;;;                
;;;; $Id: pit8253.lisp,v 1.3 2004/01/19 11:23:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :lib/named-integers)
(provide :x86-pc/pit8253)

(in-package muerte.x86-pc)

(defconstant +pit8253-frequency+ 1193181) ; Approx. 1.2 MHz
(defconstant +pit8253-nanosecond-period+ 838)

(define-named-integer pit8253-mode (:only-constants t :export-constants t)
  (0 single-timeout)
  (1 one-shot)
  (2 rate-generator)
  (3 square-wave)
  (4 software-strobe))


(defun (setf pit8253-timer-mode) (mode timer)
  "Assumes binary 16-bit timer mode, not BCD."
  (setf (io-port #x43 :unsigned-byte8)
    (dpb (+ 3 (* 4 timer))
	 (byte 4 4)
	 (ash mode 1)))
  mode)

(defun pit8253-timer-count (timer)
  (setf (io-port #x43 :unsigned-byte8) (ash timer 6)) ; latch counter
  (logior (io-port (+ #x40 timer) :unsigned-byte8)
	  (ash (io-port (+ #x40 timer) :unsigned-byte8) 8)))

(defun (setf pit8253-timer-count) (value timer)
  (setf (io-port (+ #x40 timer) :unsigned-byte8) (ldb (byte 8 0) value)
	(io-port (+ #x40 timer) :unsigned-byte8) (ldb (byte 8 8) value))
  value)

