;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      serial.lisp
;;;; Description:   Serial port interfacing.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 11 14:42:12 2002
;;;;                
;;;; $Id: serial.lisp,v 1.3 2005/03/09 07:21:42 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/named-integers)
(provide :x86-pc/serial)

(defpackage muerte.x86-pc.serial
  (:use muerte.cl muerte.lib muerte.x86-pc muerte)
  (:export uart-probe
	   uart-divisor
	   uart-baudrate
	   encode-uart-lcr
	   decode-uart-lcr
	   +uart-probe-addresses+
	   com))

(in-package muerte.x86-pc.serial)

(defconstant +uart-probe-addresses+
    '(#x3f8 #x2f8 #x3e8 #x2e8))

(define-named-integer uart-read (:only-constants t :export-constants t)
  ;; UART register map with DLAB=0
  (0 receiver-buffer)
  (1 ier)				; interrupt enable
  (2 iir)				; interrupt identification
  (3 lcr)				; Line Control
  (4 mcr)				; Modem Control
  (5 lsr)				; Line Status
  (6 msr)				; Modem Status
  (7 scratch))

(define-named-integer uart-dlab1-read (:only-constants t :export-constants t)
  ;; UART register map with DLAB=1
  (0 divisor-latch-lo)
  (1 divisor-latch-hi))

(define-named-integer uart-write (:only-constants t :export-constants t)
  ;; UART register map with DLAB=0
  (0 transmitter-buffer)
  (1 ier)				; interrupt enable
  (2 fcr)				; FIFO Control
  (3 lcr)				; Line Control
  (4 mcr)				; Modem Control
  (7 scratch))

(define-named-integer uart-dlab1-write (:only-constants t :export-constants t)
  ;; UART register map with DLAB=1
  (0 divisor-latch-lo)
  (1 divisor-latch-hi))

(defun uart-probe (io-base)
  "Return NIL if no UART is found. If an UART is found, return three values:
The io-base, the UART's name, and the FIFO size."
  (with-io-register-syntax (uart-io io-base)
    (let ((old-mcr (uart-io +uart-read-mcr+)))
      (setf (uart-io +uart-write-mcr+) #x10)
      (unless (= 0 (ldb (byte 4 4) (uart-io +uart-read-msr+)))
	(return-from uart-probe nil))
      (setf (uart-io +uart-write-mcr+) #x1f)
      (unless (= #xf (ldb (byte 4 4) (uart-io +uart-read-msr+)))
	(return-from uart-probe nil))
      (setf (uart-io +uart-write-mcr+) old-mcr))
    ;; next thing to do is look for the scratch register
    (let ((old-scratch (uart-io +uart-read-scratch+)))
      (when (or (/= (setf (uart-io +uart-write-scratch+) #x55)
		    (uart-io +uart-read-scratch+))
		(/= (setf (uart-io +uart-write-scratch+) #xaa)
		    (uart-io +uart-read-scratch+)))
	(return-from uart-probe 
	  (values io-base :uart-8250 0)))
      (setf (uart-io +uart-write-scratch+) old-scratch))
    ;; then check if there's a FIFO
    (setf (uart-io +uart-write-fcr+) #x21)
    (case (ldb (byte 3 5) (uart-io +uart-read-iir+))
      (0 (values io-base :16450 0)) ; No FIFO
      (4 (values io-base :16550 0)) ; FIFO enabled but unusable
      (6 (values io-base :16550a 16))
      (7 (values io-base :16750 64))
      (t (values io-base :unknown 0)))))

(defun uart-divisor (io-base)
  (with-io-register-syntax (uart-io io-base)
    (setf (ldb (byte 1 7) (uart-io +uart-write-lcr+)) 1)
    (prog1
	(dpb (uart-io +uart-dlab1-read-divisor-latch-hi+)
	     (byte 8 8)
	     (uart-io +uart-dlab1-read-divisor-latch-lo+))
      (setf (ldb (byte 1 7) (uart-io +uart-write-lcr+)) 0))))

(defun (setf uart-divisor) (value io-base)
  (with-io-register-syntax (uart-io io-base)
    (setf (ldb (byte 1 7) (uart-io +uart-write-lcr+)) 1
	  (uart-io +uart-dlab1-read-divisor-latch-hi+) (ldb (byte 8 8) value)
	  (uart-io +uart-dlab1-read-divisor-latch-lo+) (ldb (byte 8 0) value)
	  (ldb (byte 1 7) (uart-io +uart-write-lcr+)) 0))
  value)

(defun uart-baudrate (io-base)
  (truncate 115200 (uart-divisor io-base)))

(defun (setf uart-baudrate) (value io-base)
  (setf (uart-divisor io-base)
    (truncate 115200 value))
  value)

(defun decode-uart-lcr (x)
  "Return word-length, parity mode, stop-bits."
  (values (+ 5 (ldb (byte 2 0) x))
	  (case (ldb (byte 3 3) x)
	    ((0 2 4 6) :none)
	    (1 :odd)
	    (3 :even)
	    (5 :sticky-high)
	    (7 :sticky-low))
	  (if (logbitp 2 x) 2 1)
	  (logbitp 6 x)
	  (logbitp 7 x)))

(defun encode-uart-lcr (word-length parity stop-bits &optional (break nil) (dlab nil))
  (assert (<= 5 word-length 8))
  (assert (<= 1 stop-bits 2))
  (logior (- word-length 5)
	  (ecase parity
	    (:none 0)
	    (:odd  #x08)
	    (:even #x18)
	    (:sticky-high #x28)
	    (:sticky-low #x38))
	  (if (= 1 stop-bits) 0 4)
	  (if break #x40 0)
	  (if dlab #x80 0)))

;;;(defun uart-read-char (io-base)
;;;  (loop until ))

(defun uart-write-char (io-base char)
  (loop until (logbitp 5 (io-register8 io-base +uart-read-lsr+)))
  (setf (io-port (+ io-base +uart-write-transmitter-buffer+) :character)
    char))

(defun make-serial-write-char (&key (io-base (or (some #'uart-probe +uart-probe-addresses+)
						 (error "No serial port found.")))
				    (baudrate 9600)
				    (word-length 8)
				    (parity :none)
				    (stop-bits 1))
  (setf (uart-baudrate io-base) baudrate
	(io-register8 io-base +uart-write-lcr+) (encode-uart-lcr word-length parity stop-bits))
  (setf (io-register8 io-base +uart-write-fcr+) 0)
  (lambda (char &optional stream)
    (case char
      (#\newline
       (uart-write-char io-base #\return)))
    (uart-write-char io-base char)
    (muerte::%write-char char (muerte::output-stream-designator stream))))


(defun com (string &key (io-base (or (some #'uart-probe +uart-probe-addresses+)
				     (error "No serial port found.")))
			(baudrate 9600)
			(word-length 8)
			(parity :none)
			(stop-bits 1))
  (setf (uart-baudrate io-base) baudrate
	(io-register8 io-base +uart-write-lcr+) (encode-uart-lcr word-length parity stop-bits))
  (setf (io-register8 io-base +uart-write-fcr+) 0)
  (loop for c across string
      do (uart-write-char io-base c))
  io-base)

