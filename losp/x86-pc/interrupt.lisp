;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      interrupt.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri May  4 18:08:50 2001
;;;;                
;;;; $Id: interrupt.lisp,v 1.11 2005/05/05 15:17:12 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/pic8259)
(provide :x86-pc/interrupt)

(in-package muerte.x86-pc)

(defun idt-init ()
  (init-pic8259 32 40)
  (setf (pic8259-irq-mask) #xffff)
  (load-idt (muerte::load-global-constant muerte::interrupt-descriptor-table))
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


