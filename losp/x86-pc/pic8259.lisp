;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pic8259.lisp
;;;; Description:   8259A Programmable Interrupt Controller
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue May 22 15:23:01 2001
;;;;                
;;;; $Id: pic8259.lisp,v 1.3 2004/01/19 11:23:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :x86-pc/pic8259)

(in-package muerte.x86-pc)

(defun pic8259-init-cycle (base icw1 icw2 icw3 &optional icw4)
  "Run the 8259 low-level initialization cycle."
  (setf (io-port base :unsigned-byte8) icw1 ; Init 1
	(io-port (1+ base) :unsigned-byte8) icw2 ; Init 2
	(io-port (1+ base) :unsigned-byte8) icw3) ; Init 3
  (when icw4
    (setf (io-port (1+ base) :unsigned-byte8) icw4))) ; Init 4

(defun init-pic8259 (vector-0-7 vector-8-15)
  "Initialize the two 8259 PICs found in AT computers. Bus IRQs 0-7 are
   routed to interrupts starting at VECTOR-0-7, IRQs 8-15 to VECTOR-8-15."
  ;; Set up PIC at #x20 as master
  (pic8259-init-cycle #x20 #x11 vector-0-7  #x04 #x01)
  ;; Set up PIC at #xa0 as slave
  (pic8259-init-cycle #xa0 #x11 vector-8-15 #x02 #x01))

(defun (setf pic8259-irq-mask) (value)
  (setf (io-port #x21 :unsigned-byte8) (ldb (byte 8 0) value) ; IRQ0-7 
	(io-port #xa1 :unsigned-byte8) (ldb (byte 8 8) value)) ; IRQ8-15
  value)

(defun pic8259-irq-mask ()
  (dpb (io-port #xa1 :unsigned-byte8)
       (byte 8 8)
       (io-port #x21 :unsigned-byte8)))

;; (defun pic8259-irq-mask (irq))
  

;; (defun pic8259-enable-irq (irq)
  
(defun pic8259-end-of-interrupt (irq)
  (if (< irq 8)
      (setf (io-port #x20 :unsigned-byte8) #x20)
    (setf (io-port #xa0 :unsigned-byte8) #x20
	  (io-port #x20 :unsigned-byte8) #x20))
  nil)
