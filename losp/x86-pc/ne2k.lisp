;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ne2k.lisp
;;;; Description:   ISA NE2000 ethernet NIC driver.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 17 15:16:00 2002
;;;;                
;;;; $Id: ne2k.lisp,v 1.15 2005/06/05 01:07:50 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :lib/net/ethernet)

(defpackage muerte.x86-pc.ne2k
  (:use muerte.cl muerte muerte.lib muerte.x86-pc muerte.ethernet)
  (:export #:ne2k-probe
	   #:*ne2k-probe-addresses*
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

(defparameter *ne2k-probe-addresses*
    '(#x300 #x240 #x260 #x280 #x300 #x320 #x340))

(defun ne2k-probe (io-base)
  (let ((io-space (make-io-space :range io-base #x20)))
    (with-io-space-lock ()
      (when (null (io-space-occupants io-space))
	(format *query-io* "~&Probing for ne2k NIC at #x~X.." io-base)
	(with-dp8390 (dp8390 io-base)
	  (let ((tmp (dp8390 #x1f)))
	    (io-delay 5000)
	    (setf (dp8390 #x1f) tmp))
	  (cond
	   ((not (and #+ignore (= (logand #b00111111 (dp8390 ($page0-read cr)))
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
    (let ((test-vector #(#xabba #x00ff #x5599 #x0123 #x45de #xadbe #xef23)))
      ;; NE1000 has RAM buffer located at 8192
      ;; NE2000 has RAM buffer located at 16384
      ;; Check if 16-bit access works to NE2000 RAM works:
      (setf (dp8390 ($page0-write cr)) ($command page-0)
	    (dp8390 ($page0-write dcr)) ($data-config fifo-threshold-8-bytes
						      loopback-off
						      dma-16-bit))
      (with-dp8390-dma (dp8390 remote-write (* 2 (length test-vector)) 16384)
	(loop with asic = (+ io-base #x10)
	    for x across test-vector
	    do (setf (io-port asic :unsigned-byte16) x)))
      (let ((mismatch nil))
	(with-dp8390-dma (dp8390 remote-read (* 2 (length test-vector)) 16384)
	  (loop for x across test-vector
	      do (unless (= x (io-port (+ io-base #x10) :unsigned-byte16))
		   (setf mismatch t))))
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
    (let ((mac (make-array 6 :element-type '(unsigned-byte 8))))
      (with-dp8390 (dp8390 io-base)
	(with-dp8390-dma (dp8390 remote-read 12 0)
	  (dotimes (i 6)
	    (setf (aref mac i)
	      (ldb (byte 8 0)
		   (io-port (asic-io-base ne2000) :unsigned-byte16))))))
      (setf (mac-address ne2000) mac))
    ne2000))



;;; Packet IO handling

(defun read-from-ne2k-ring (io-base asic-io packet start length ring-start ring-pointer ring-stop)
  "Read from a NE2000 ring buffer into packet, starting at start,
   length number of bytes."
  (check-type packet (simple-array (unsigned-byte 8) 1))
  (let* ((ring-space (- ring-stop ring-pointer)))
    (if (<= length ring-space)
	(with-dp8390 (dp8390 io-base)
	  (with-dp8390-dma (dp8390 remote-read length ring-pointer)
	    (%io-port-read-succession asic-io packet 2 start (+ start length) :16-bit)))
      ;; If the read crosses the ring wrap-around boundary,
      ;; that read is factored into two unwrapped reads.
      (let ((split-point (+ start ring-space)))
	(read-from-ne2k-ring io-base asic-io packet start split-point
			     ring-start ring-pointer ring-stop)
	(read-from-ne2k-ring io-base asic-io packet split-point (- length split-point)
			     ring-start ring-start ring-stop)))))

(defun pop-ringbuffer (device packet start)
  "When the ring-buffer isn't empty, fetch the next packet."
  (assert (evenp start))
  (let ((read-pointer (next-packet device)))
    (when read-pointer
      (let ((asic-io (asic-io-base device))
	    (packet (or packet (make-array +max-ethernet-frame-size+
					   :element-type '(unsigned-byte 8))))
	    (ring-start (ring-start device))
	    (ring-stop (ring-stop device)))
	(with-dp8390 (dp8390 (io-base device))
	  (multiple-value-bind (packet-status next-bnry packet-length)
	      ;; Read the packet status-and-size header from the ring.
	      (with-dp8390-dma (dp8390 remote-read 4 read-pointer)
		(let ((b (io-port asic-io :unsigned-byte16)))
		  (values (ldb (byte 8 0) b)
			  (ldb (byte 8 8) b)
			  (+ -4 (io-port asic-io :unsigned-byte16)))))
	    (assert (logbitp 0 packet-status) ()
	      "Packet error status #x~X at #x~X, length ~D, next #x~X."
	      packet-status read-pointer packet-length next-bnry)
	    (let ((next-read-pointer (* 256 next-bnry))
		  (io-length (if (evenp packet-length) packet-length (1+ packet-length))))
	      (assert (and (<= ring-start next-read-pointer)
			   (< next-read-pointer ring-stop)) ()
		"Illegal next-bnry #x~X at #x~X, length ~D."
		next-read-pointer read-pointer packet-length)
	      (setf (fill-pointer packet) (+ start packet-length))
	      (read-from-ne2k-ring dp8390 asic-io packet start io-length
				   ring-start (+ 4 read-pointer) ring-stop)
	      (setf (dp8390 ($page0-write bnry)) next-bnry
		    (read-pointer device) next-read-pointer)
	      packet)))))))

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
  (setf (slot-value device 'transmit-buffer) #x4000
	(slot-value device 'ring-start) #x4600
	(slot-value device 'ring-stop) #x8000
	(slot-value device 'write-pointer) #x4600
	(slot-value device 'read-pointer) #x4600)
  (dp8390-initialize device)
  device)

(defmethod packet-available-p ((device ne2000))
  (when (next-packet device)
    t))

(defmethod transmit ((device ne2000) packet &key (start 0) (end (length packet)))
  (check-type packet (simple-array (unsigned-byte 8) 1))
  (assert (and (evenp start)))
  (with-dp8390 (dp8390 (io-base device))
    (loop while (logbitp ($command-bit transmit)
			 (dp8390 ($page0-read cr))))
    (let ((packet-length (- end start)))
      (with-dp8390-dma (dp8390 remote-write packet-length (transmit-buffer device))
	(%io-port-write-succession (asic-io-base device) packet 2 start end :16-bit))
      (setf (io-register8x2 dp8390 ($page0-write tbcr1) ($page0-write tbcr0)) packet-length
	    (dp8390 ($page0-write cr)) ($command transmit start abort-complete))
      #+ignore
      (loop while (= (dp8390 ($page0-read cr))
		     ($command start transmit abort-complete)))))
  nil)

(defmethod receive ((device ne2000) &optional packet (start 0))
  (with-dp8390 (dp8390 (io-base device))
    (let ((isr (dp8390 ($page0-read isr))))
      (if (logbitp ($interrupt-status overwrite-warning) isr)
	  (recover-from-ring-overflow device packet start isr)
	(pop-ringbuffer device packet start)))))

#+ignore
(defun spinning-receive (ne2000
			 &optional (packet (make-array 1500 :element-type '(unsigned-byte 8)))
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
