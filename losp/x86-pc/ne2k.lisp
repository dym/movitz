;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ne2k.lisp
;;;; Description:   ISA NE2000 ethernet NIC driver.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 17 15:16:00 2002
;;;;                
;;;; $Id: ne2k.lisp,v 1.4 2004/01/19 11:23:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :lib/net/ethernet)

(defpackage muerte.x86-pc.ne2k
  (:use muerte.cl muerte muerte.lib muerte.x86-pc muerte.ethernet)
  (:export #:ne2k-probe
	   #:+ne2k-probe-addresses+
	   
	   #:with-dp8390
	   #:with-dp8390-dma
	   #:dp8390-initialize
	   #:dp8390-device
	   #:ring-start
	   #:ring-stop
	   #:io-base
	   #:ring-overflow-count
	   #:transmit-buffer
	   ))

(require :lib/net/ethernet)
(require :x86-pc/dp8390)

(provide :x86-pc/ne2k)


(in-package muerte.x86-pc.ne2k)

(defconstant +ne2k-probe-addresses+ '(#x240 #x260 #x280 #x300 #x320 #x340))

(defun ne2k-probe (io-base)
  (let ((io-space (make-io-space :range io-base #x20)))
    (with-io-space-lock ()
      (when (null (io-space-occupants io-space))
	(format t "Probing for ne2k NIC at #x~X.." io-base)
	(with-dp8390 (dp8390 io-base)
	  (let ((tmp (dp8390 #x1f)))
	    (io-delay 5000)
	    (setf (dp8390 #x1f) tmp))
	  (cond
	   ((not (and (= (logand #b00111111 (dp8390 ($page0-read cr)))
			 ($command stop abort-complete))
		      (eq 'ne2000 (ne-x000-probe io-base))))
	    (format t "failed.~%"))
	   (t (let ((device (make-ne2000 io-base)))
		(allocate-io-space device io-space)
		(format t "found ~S with MAC ~/ethernet:pprint-mac/.~%"
			device (mac-address device))
		device))))))))

(defun ne-x000-probe (&optional (io-base #x300))
  "Probe for the presence of a NE2000 compatible card at IO-address io-base." 
  (with-dp8390 (dp8390 io-base)
    (let ((test-vector (copy-seq #(#xab #xba #x00 #xff #x55 #x99 #x01 #x23 #x45 #xde #xad #xbe #xef #x23))))
      (declare (dynamic-extent test-vector))
      ;; NE1000 has RAM buffer located at 8192
      ;; NE2000 has RAM buffer located at 16384
      ;; We have detected NE2000, check if 16-bit access works:
      (setf (dp8390 ($page0-write cr)) ($command page-0)
	    (dp8390 ($page0-write dcr)) ($data-config fifo-threshold-8-bytes
						      loopback-off
						      dma-16-bit))
      (with-dp8390-dma (dp8390 remote-write (length test-vector) 16384)
	(io-port-write-sequence test-vector (+ io-base #x10) :unsigned-byte8 :16-bits))
      (let ((mismatch nil))
	(with-dp8390-dma (dp8390 remote-read (length test-vector) 16384)
	  (dotimes (i (truncate (length test-vector) 2))
	    (let ((nic-byte (io-port (+ io-base #x10) :unsigned-byte16)))
	      (unless (and (= (aref test-vector (* 2 i))
			      (ldb (byte 8 0) nic-byte))
			   (= (aref test-vector (1+ (* 2 i)))
			      (ldb (byte 8 8) nic-byte)))
		(setf mismatch t)))))
	(unless mismatch
	  'ne2000)))))

(defclass ne2000 (dp8390-device)
  ((asic-io-base
    :initarg :asic-io-base
    :reader asic-io-base)))

(defun make-ne2000 (io-base)
  (let ((ne2000 (make-instance 'ne2000
		  :io-base io-base
		  :asic-io-base (+ io-base #x10))))
    (reset-device ne2000)
    (let ((mac (make-array 6 :element-type 'muerte::u8)))
      (with-dp8390 (dp8390 io-base)
	(with-dp8390-dma (dp8390 remote-read 12 0)
	  (io-port-read-sequence mac (asic-io-base ne2000)
				 :unsigned-byte16 :16-bits)))
      (setf (mac-address ne2000) mac))
    ne2000))



;;; Packet IO handling

(defun pop-ringbuffer (device &optional packet (start 0))
  "When the ring-buffer isn't empty, fetch the next packet."
  (unless (ring-empty-p device)
    (let ((asic-io (asic-io-base device))
	  (bnry (cached-bnry device))
	  (packet (or packet (make-array +max-ethernet-frame-size+ :element-type 'muerte::u8))))
      (with-dp8390 (dp8390 (io-base device))
	(multiple-value-bind (packet-status next-bnry packet-length)
	    (with-dp8390-dma (dp8390 remote-read 4 (* 256 bnry))
	      (let ((b (io-port asic-io :unsigned-byte16)))
		(values (ldb (byte 8 0) b)
			(ldb (byte 8 8) b)
			(+ -4 (io-port asic-io :unsigned-byte16)))))
	  ;; (declare (ignore packet-status))
	  (assert (logbitp 0 packet-status) ()
	    "Packet error status #x~X at #x~X, length ~D, next #x~X."
	    packet-status bnry packet-length next-bnry)
	  (assert (and (<= (ring-start device) next-bnry)
		       (< next-bnry (ring-stop device))) ()
	    "Illegal next-bnry #x~X at #x~X, length ~D."
	    next-bnry bnry packet-length)
	  (let ((rx-end (+ start packet-length)))
	    (declare (type (unsigned-byte 16) rx-end))
	    (assert (evenp start))
	    (setf (fill-pointer packet) rx-end)
	    (cond
	     ((< (+ bnry (ash (1- packet-length) -8))
		 (ring-stop device))
	      (with-dp8390-dma (dp8390 remote-read packet-length (+ (* 256 bnry) 4))
		(io-port-read-sequence packet asic-io :unsigned-byte8 :16-bits :start start)
		(when (oddp rx-end)
		  (setf (aref packet (1- rx-end))
		    (ldb (byte 8 0) (io-port asic-io :unsigned-byte16)))))
	      (setf (dp8390 ($page0-write bnry)) next-bnry
		    (cached-bnry device) next-bnry))
	     (t (let ((split-point (+ -4 (ash (- (ring-stop device) bnry) 8))))
		  (with-dp8390-dma (dp8390 remote-read split-point)
		    (io-port-read-sequence packet asic-io :unsigned-byte8 :16-bits
					   :start start :end (+ start split-point)))
		  (with-dp8390-dma (dp8390 remote-read
					   (- rx-end start split-point)
					   (* 256 (ring-start device)))
		    (io-port-read-sequence packet asic-io :unsigned-byte8 :16-bits
					   :start (+ start split-point))
		    (when (oddp rx-end)
		      (setf (aref packet (1- rx-end))
			(ldb (byte 8 0)
			     (io-port asic-io :unsigned-byte16)))))
		  (setf (dp8390 ($page0-write bnry)) next-bnry
			(cached-bnry device) next-bnry)
		  #+ignore (warn "split-point: ~D/~D bnry: ~S"
				 split-point packet-length bnry))))
	    packet))))))

(defun recover-from-ring-overflow (device packet start isr)
  (with-dp8390 (dp8390 (io-base device))
    (warn "Recovering ~S from ring overflow." device)
    (incf (ring-overflow-count device))
    ;; 1. Read and store the value of TXP
    (let ((saved-txp (logbitp ($command-bit transmit) (dp8390 ($page0-read cr)))))
      ;; 2. Issue the STOP command
      (setf (dp8390 ($page0-write cr)) ($command abort-complete stop))
      ;; 3. Wait for at least 1.6 ms. XXX
      (io-delay 1000)
      ;; 4. Clear Remote Byte Count registers
      ;; (setf (rbcr io-base) 0)
      (setf (io-register8x2 dp8390 ($page0-write rbcr1) ($page0-write rbcr0)) 0)
      ;; 5. Determine if there was a transmission in progresss
      (let ((resend (and saved-txp
			 (not (or (logbitp ($interrupt-status packet-transmitted) isr)
				  (logbitp ($interrupt-status transmit-error) isr))))))
	;; 6. Place the NIC in mode 1 loopback
	(setf (dp8390 ($page0-write tcr)) ($tx-config loopback-mode-1))
	;; 7. Issue START command
	(setf (dp8390 ($page0-write cr)) ($command abort-complete start))
	;; 8. Remove one or more packets from the ring
	(multiple-value-prog1
	    (pop-ringbuffer device packet start)
	  ;; 9. Reset overflow state
	  (setf (dp8390 ($page0-write isr)) (ash 1 ($interrupt-status overwrite-warning)))
	  ;; 10. Take NIC out of loopback
	  (setf (dp8390 ($page0-write tcr)) ($tx-config loopback-mode-0))
	  ;; 11. Reissue if necessary transmit command
	  (when resend
	    (setf (dp8390 ($page0-write cr)) ($command transmit))))))))

(defmethod reset-device ((device ne2000))
  (setf (slot-value device 'transmit-buffer) #x40
	(slot-value device 'ring-start) #x46
	(slot-value device 'ring-stop) #x80
	(slot-value device 'cached-bnry) #x46
	(slot-value device 'cached-curr) #x46)
  (dp8390-initialize device)
  device)

(defmethod packet-available-p ((device ne2000))
  (not (ring-empty-p device)))

(defmethod transmit ((device ne2000) packet &key (start 0) (end (length packet)))
  (with-dp8390 (dp8390 (io-base device))
    ;; (setf (r8 +page0-write-cr+) +command-page-0+)
    (let ((packet-length (- end start)))
      (with-dp8390-dma (dp8390 remote-write packet-length
			       (ash (transmit-buffer device) 8))
	(io-port-write-sequence packet (asic-io-base device) :unsigned-byte8 :16-bits
				:start start :end end)
	(when (oddp packet-length)
	  (setf (io-port (asic-io-base device) :unsigned-byte16)
	    (aref packet (1- end)))))
      (loop while (logbitp ($command-bit transmit) (dp8390 ($page0-read cr))))
      (setf (io-register8x2 dp8390 ($page0-write tbcr1) ($page0-write tbcr0)) packet-length
	    (dp8390 ($page0-write cr)) ($command transmit start abort-complete))
      (loop while (= (dp8390 ($page0-read cr))
		     ($command start transmit abort-complete)))
      ;; (loop while (= command (command-value :start t :txp t :rdma :abort-complete)))
      ))
  nil)

(defmethod receive ((device ne2000) &optional packet (start 0))
  (with-dp8390 (dp8390 (io-base device))
    (let ((isr (dp8390 ($page0-read isr))))
      (if (logbitp ($interrupt-status overwrite-warning) isr)
	  (recover-from-ring-overflow device packet start isr)
	(pop-ringbuffer device packet start)))))

#+ignore
(defun spinning-receive (ne2000
			 &optional (packet (make-array 1500 :element-type 'muerte::u8))
			 &key (start 0))
  (multiple-value-bind (recovered-packet recovered-packet-length)
      (recover-when-ring-overflow ne2000 packet :start start)
    (if recovered-packet
	(values recovered-packet recovered-packet-length)
      (with-io-register-syntax (r8 io-base (io-base ne2000))
	(setf (r8 +page0-write-cr+) +command-page-1+)
	(loop with read-pointer = (next-packet ne2000)
	    for current-pointer = (r8 +page1-read-curr+)
	    while (= read-pointer current-pointer)
	    finally
	      (return (pop-ringbuffer ne2000 packet start current-pointer)))))))
