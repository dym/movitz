;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      interrupt.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri May  4 18:08:50 2001
;;;;                
;;;; $Id: interrupt.lisp,v 1.9 2004/04/07 00:12:28 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/pic8259)
(provide :x86-pc/interrupt)

(in-package muerte.x86-pc)

(defmacro end-of-interrupt ()
  '(with-inline-assembly (:returns :nothing)
    (:movb #x20 :al)
    (:outb :al #x20)))

(defun idt-init ()
  (init-pic8259 32 40)
  (setf (pic8259-irq-mask) #xffff)
  (load-idt (load-global-constant interrupt-descriptor-table))
  nil)

(defun timer-init ()
  "Set timer 0 frequency to 100Hz (ie. 10ms intervals)."
  (setf (io-port #x40 :unsigned-byte8)
    #.(cl:ldb (cl:byte 8 0) #xffff))	; 11932))
  (setf (io-port #x40 :unsigned-byte8)
    #.(cl:ldb (cl:byte 8 8) #xffff))	; 11932))
  (setf (pic8259-irq-mask) #xfffe)
  (with-inline-assembly (:returns :nothing) (:sti)))

(defparameter *timer-counter* 0)

(defun timer-handler (number int-frame)
  (declare (ignore number int-frame))
  (unless (boundp '*timer-counter*)
    (setf *timer-counter* 0))
  (format t "~&timer: ~D" (incf *timer-counter*))
  (pic8259-end-of-interrupt 0))


