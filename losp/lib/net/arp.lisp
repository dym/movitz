;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      arp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Mar 20 15:01:15 2003
;;;;                
;;;; $Id: arp.lisp,v 1.2 2004/01/15 17:34:49 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/net/ethernet)
(provide :lib/net/arp)

(in-package muerte.ip4)

(define-named-integer arp-op (:export-constants t)
  (1 request)
  (2 reply)
  (3 reverse-request)
  (4 reverse-reply))

(define-named-integer arp-hard-type (:export-constants t)
  (1 ethernet))

(defun format-arp-request (packet op
			   sender-ip-address
			   sender-hardware-address
			   target-ip-address
			   &key (start 14)
				(target-hardware-address #(0 0 0 0 0 0))
				(sender-hardware-address-start 0)
				(sender-ip-address-start 0)
				(target-hardware-address-start 0)
				(target-ip-address-start 0)
				(hard-type 1) (prot-type #x0800)
				(hard-size 6) (prot-size 4))
  (if packet
      (setf (fill-pointer packet) 64)
    (setf packet (make-array 64 :element-type 'muerte::u8)))
  (setf (aref packet (+ start 0)) (ldb (byte 8 8) hard-type)
	(aref packet (+ start 1)) (ldb (byte 8 0) hard-type)
	(aref packet (+ start 2)) (ldb (byte 8 8) prot-type)
	(aref packet (+ start 3)) (ldb (byte 8 0) prot-type)
	(aref packet (+ start 4)) hard-size
	(aref packet (+ start 5)) prot-size
	(aref packet (+ start 6)) (ldb (byte 8 8) op)
	(aref packet (+ start 7)) (ldb (byte 8 0) op))
  (replace packet sender-hardware-address
	   :start1 (+ start 8)
	   :end1 (+ start 14)
	   :start2 sender-hardware-address-start)
  (replace packet sender-ip-address
	   :start1 (+ start 14)
	   :end1 (+ start 18)
	   :start2 sender-ip-address-start)
  (replace packet target-hardware-address
	   :start1 (+ start 18)
	   :end1 (+ start 24)
	   :start2 target-hardware-address-start)
  (replace packet target-ip-address
	   :start1 (+ start 24)
	   :end1 (+ start 28)
	   :start2 target-ip-address-start))


(defun arp-operation (packet &optional (start 14))
  (bvref-u16 packet start 6))

(defun arp-hard-type (packet &optional (start 14))
  (bvref-u16 packet start 0))

(defun arp-prot-type (packet &optional (start 14))
  (bvref-u16 packet start 2))


(defvar *ne2000* nil)
	  
(defun test-arp (&optional (ip #(129 242 16 30)) (my-ip #(129 242 16 173))
			   (device (or *ne2000*
				       #+ignore
				       (setf *ne2000* (some #'muerte.x86-pc.ne2k:ne2k-probe muerte.x86-pc.ne2k:+ne2k-probe-addresses+)))))
  
  (loop for packet = (muerte.ethernet:receive device)
      with i = 9999
      do (when (= (incf i) 10000)
	   (setf i 0)
	   (transmit device
		     (format-ethernet-packet (format-arp-request nil +arp-op-request+ my-ip (mac-address device) ip)
					     (mac-address device)
					     muerte.ethernet:+broadcast-address+
					     muerte.ethernet:+ether-type-arp+)))
      until (or (muerte.x86-pc.keyboard:poll-char)
		(when (and packet
			   (or (eq +ether-type-arp+ (ether-type packet)) (warn "not type"))
			   (or (eq +arp-op-reply+ (arp-operation packet)) (warn "not op"))
			   (or (not (mismatch packet ip :start1 28 :end1 32)) (warn "mismatch: ~S" (subseq packet 28 32))))
		  (format t "The MAC of ~S is ~22/ethernet:pprint-mac/." ip packet)
		  t))))
