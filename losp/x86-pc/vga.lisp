;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      vga.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 25 14:08:20 2001
;;;;                
;;;; $Id: vga.lisp,v 1.2 2004/01/15 17:13:53 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(provide :x86-pc/vga)

(in-package muerte.x86-pc)

(defun (setf vga-crt-controller-register) (value register)
  (let* ((address-register (if (logbitp 0 (io-port #x3cc :unsigned-byte8)) #x3d4 #x3b4))
	 (data-register (1+ address-register)))
    (setf (io-port address-register :unsigned-byte8) register
	  (io-port data-register :unsigned-byte8) value)))

(defun vga-crt-controller-register (register)
  (let* ((address-register (if (logbitp 0 (io-port #x3cc :unsigned-byte8)) #x3d4 #x3b4))
	 (data-register (1+ address-register)))
    (setf (io-port address-register :unsigned-byte8) register)
    (io-port data-register :unsigned-byte8)))

(defun vga-graphics-register (register)
  (setf (io-port #x3ce :unsigned-byte8) register)
  (io-port #x3cf :unsigned-byte8))

(defun (setf vga-graphics-register) (value register)
  (setf (io-port #x3ce :unsigned-byte8) register
	(io-port #x3cf :unsigned-byte8) value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun (setf vga-cursor-location) (value)
  (setf (vga-crt-controller-register #x0e) (ldb (byte 8 8) value) ; high
	(vga-crt-controller-register #x0f) (ldb (byte 8 0) value)) ; low
  value)

(defun vga-cursor-location ()
  (dpb (vga-crt-controller-register #x0e)
       (byte 8 8)
       (vga-crt-controller-register #x0f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vga-memory-map ()
  (case (ldb (byte 2 2)
	     (vga-graphics-register 6))
    (#b00 (values #xa0000 #xbffff))
    (#b01 (values #xa0000 #xaffff))
    (#b10 (values #xb0000 #xb7fff))
    (#b11 (values #xb8000 #xbffff))))
