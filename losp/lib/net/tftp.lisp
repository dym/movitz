;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      tftp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Oct  6 12:42:51 2004
;;;;                
;;;; $Id: tftp.lisp,v 1.4 2004/12/08 23:40:15 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/net/ethernet)
(provide :lib/net/tftp)

(in-package muerte.ip4)

(defpackage muerte.ip4
  (:export #:format-tftp-request
	   #:tftp/ethernet-write))

(defun format-tftp-request (packet start opcode &rest strings)
  (declare (dynamic-extent strings))
  (let ((i 0))
    (macrolet ((i++ (&optional (delta 1)) `(prog1 i (incf i ,delta))))
      (setf (ip4-ref packet start (i++ 2) :unsigned-byte16) opcode)
      (if (integerp (car strings))
	  (setf (ip4-ref packet start (i++ 2) :unsigned-byte16)
	    (car strings))
	(dolist (string strings)
	  (loop for c across string
	      do (setf (ip4-ref packet start (i++) :unsigned-byte8)
		   (char-code c))
	      finally
		(setf (ip4-ref packet start (i++) :unsigned-byte8) 0))))
      (when (oddp i)
	(setf (ip4-ref packet start (i++) :unsigned-byte8) 0))
      (setf (fill-pointer packet) (+ start i))
      packet)))

(defun fvf-tftp (&optional (file-name "foo.txt") (data "hei"))
  (ip4-init)
  (let ((data (etypecase data
		(vector data)
		(integer
		 ;; Make a test-string of length data.
		 (let ((x (make-string data)))
		   (loop for i from 0 below data
		       as c = 0 then (mod (1+ c) 8)
		       do (setf (char x i) (code-char (+ (char-code #\0) c)))
		       finally (return x)))))))
    (tftp/ethernet-write :129.242.16.151 file-name data
			 :mac (polling-arp :129.242.16.1
					   (lambda ()
					     (eql #\space (muerte.x86-pc.keyboard:poll-char)))))))

(defun tftp/ethernet-write (ip file-name data-vector
			    &key (mode "octet") mac quiet
				 (timeout 2)
				 (data-length (length data-vector))
				 (breaker (lambda ()
					    (eql #\space (muerte.x86-pc.keyboard:poll-char)))))
  "TFTP write data-vector to file-name on host ip using *ip4-nic*.
The host's MAC is looked up by ARP unless provided."
  (let ((speak (if quiet nil *query-io*))
	(ip (ip4-address ip)))
    (check-type file-name string)
    (check-type data-vector vector)
    (check-type mode string)
    (unless mac
      (format speak "~&ARP-resolving ~/ip4:pprint-ip4/.." ip)
      (assert (setf mac (polling-arp ip breaker))
	  (ip) "TFTP/ARP failed.")
      (format speak " ..~/ethernet:pprint-mac/.~%" mac))
    (flet ((transmit-stop-and-wait (packet ack-block-number &optional port)
	     (loop with transmit-time = 0
		 with ip-start = 14
		 with udp-start = (+ ip-start 20)
		 with tftp-start = (+ udp-start 8)
		 for ack = nil then (receive *ip4-nic* ack)
		 until
		   (with-simple-restart (continue
					 "Continue TFTP stop-and-wait for ~S block ~D~@[, port ~D~]."
					 file-name ack-block-number port)
		     (when (funcall breaker)
		       (break "TFTP/Ethernet"))
		     (when (< (* timeout internal-time-units-per-second)
			      (- (get-internal-run-time) transmit-time))
		       (setf transmit-time (get-internal-run-time))
		       (transmit *ip4-nic* packet))
		     (and ack
			  (eq +ether-type-ip4+ (ether-type ack))
			  (not (mismatch *ip4-ip* (ip-header-destination ack)))
			  (not (mismatch ip (ip-header-source ack)))
			  (= +ip-protocol-udp+ (ip-protocol ack))
			  (or (checksum-ok (checksum-octets ack (+ ip-start 12) (+ ip-start 20))
					   +ip-protocol-udp+
					   (udp-length ack)
					   (checksum-octets ack udp-start))
			      (warn "UDP bad checksum from ~/ip4:pprint-ip4/."
				    (ip-header-source ack)))
			  (or (not port)
			      (= port (udp-src-port ack udp-start)))
			  (let ((opcode (ip4-ref ack tftp-start 0 :unsigned-byte16)))
			    (case opcode
			      (4	; TFTP ACK
			       (= ack-block-number
				  (ip4-ref ack tftp-start 2 :unsigned-byte16)))
			      (5	; TFTP NACK
			       (error "TFTP Error code ~D: ~S."
				      (ip4-ref ack tftp-start 2 :unsigned-byte16)
				      (extract-zero-terminated-string ack (+ tftp-start 4))))
			      (t (error "TFTP unknown response opcode ~D." opcode))))))
		 finally
		   (unless port
		     (assert ack)
		     (return (udp-src-port ack))))))
      (let ((start (+ 14 20 8))
	    (packet (make-ethernet-packet)))
	(format-tftp-request packet start 2 file-name mode)
	(format-udp-header packet :destination ip :destination-port 69)
	(format-ethernet-packet packet (mac-address *ip4-nic*) mac +ether-type-ip4+)
	(let ((port (transmit-stop-and-wait packet 0)))
	  (format speak "~&Sending TFTP data to ~/ip4:pprint-ip4/:~D." ip port)
	  (loop for block-number upfrom 1
	      for i from 0 to data-length by 512
	      do (format-tftp-request packet start 3 block-number)
		 (loop for j upfrom (fill-pointer packet)
		     as k upfrom i below (min data-length (+ i 512))
		     do (setf (ip4-ref packet 0 j :unsigned-byte8)
			  (ip4-ref data-vector 0 k :unsigned-byte8))
		     finally
		       (setf (fill-pointer packet) j))
		 (format-udp-header packet :destination ip :destination-port port)
		 (format-ethernet-packet packet (mac-address *ip4-nic*) mac +ether-type-ip4+)
		 (when speak
		   (write-char #\. speak))
		 (transmit-stop-and-wait packet block-number port)))
	(format speak "done.")
	(values)))))


