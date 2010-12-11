;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      arp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Mar 20 15:01:15 2003
;;;;                
;;;; $Id: arp.lisp,v 1.11 2008-06-13 16:21:18 aantoniadis Exp $
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
      (setf (fill-pointer packet) (max +min-ethernet-frame-size+
				       (+ start 28)))
    (setf packet (make-array +min-ethernet-frame-size+
			     :element-type '(unsigned-byte 8))))
  (setf (ip4-ref packet start 0 :unsigned-byte16) hard-type
	(ip4-ref packet start 2 :unsigned-byte16) prot-type
	(ip4-ref packet start 4 :unsigned-byte8) hard-size
	(ip4-ref packet start 5 :unsigned-byte8) prot-size
	(ip4-ref packet start 6 :unsigned-byte16) op)
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
  (ip4-ref packet start 6 :unsigned-byte16))

(defun arp-hard-type (packet &optional (start 14))
  (ip4-ref packet start 0 :unsigned-byte16))

(defun arp-prot-type (packet &optional (start 14))
  (ip4-ref packet start 2 :unsigned-byte16))

(defvar *ne2000* nil)

(defun polling-arp (ip &optional (breaker (constantly nil)))
  (loop with ip = (ip4-address ip) and nic = *ip4-nic* and transmit-time = 0
      for packet = (muerte.ethernet:receive nic)
      until (funcall breaker)
      do (when (and packet
		    (eq +ether-type-arp+ (ether-type packet))
		    (eq +arp-op-reply+ (arp-operation packet))
		    (not (mismatch packet ip :start1 28 :end1 32)))
	   (return (subseq packet 22 28)))
	 (when (< internal-time-units-per-second
		  (- (get-internal-run-time) transmit-time))
	   (setf transmit-time (get-internal-run-time))
	   (transmit nic
		     (format-ethernet-packet (format-arp-request nil +arp-op-request+ *ip4-ip*
								 (mac-address nic) ip)
					     (mac-address nic)
					     muerte.ethernet:+broadcast-address+
					     muerte.ethernet:+ether-type-arp+)))))


(defun device-init ()
    (let ((ethernet
	   (some #'muerte.x86-pc.ne2k:ne2k-probe
		 muerte.x86-pc.ne2k:*ne2k-probe-addresses*)))
      (assert ethernet ethernet "No ethernet device.")
      ethernet))


(defun test-arp (&optional (ip #(192 168 178 1)) (my-ip #(147 52 192 157))
			   (device (device-init)))
  
  (loop with ip = (ip4-address ip) and my-ip = (ip4-address my-ip)
      for packet = (muerte.ethernet:receive device)
      with i = 9999 ;;this way we go into the do in the first iteration
      do 
      (when (= (incf i) 10000)
	(setf i 0)
	(transmit device
		  (format-ethernet-packet (format-arp-request nil +arp-op-request+
							      my-ip (mac-address device) ip)
					  (mac-address device)
					  muerte.ethernet:+broadcast-address+
					  muerte.ethernet:+ether-type-arp+)))
      until (or (muerte.x86-pc.keyboard:poll-char)
			;		(format t "~a~%" packet) ;;mine
		(when (and packet
			   (or (eq +ether-type-arp+ (ether-type packet))
			       (warn "not type"))
			   (or (eq +arp-op-reply+ (arp-operation packet))
			       (warn "not op"))
			   (or (not (mismatch packet ip :start1 28 :end1 32))
			       (warn "mismatch: ~S" (subseq packet 28 32))))
		  (format t "The MAC of ~S is ~22/ethernet:pprint-mac/." ip packet)
		  t))))
