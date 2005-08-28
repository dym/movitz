;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      dp8390.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Sep 18 12:21:36 2002
;;;;                
;;;; $Id: dp8390.lisp,v 1.9 2005/08/28 20:56:00 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(require :x86-pc/io-space)
(require :lib/net/ethernet)
(provide :x86-pc/dp8390)

(in-package muerte.x86-pc.ne2k)

(defconstant +page0-read-map+
    '(:enum cr clda0 clda1 bnry tsr ncr fifo isr crda0 crda1 rbcr0 rbcr1 rsr cntr0 cntr1 cntr2))

(defconstant +page0-write-map+
    '(:enum cr pstart pstop bnry tpsr tbcr0 tbcr1 isr rsar0 rsar1 rbcr0 rbcr1 rcr tcr dcr imr))

(defconstant +page1-read-map+
    '(:enum nil nil nil nil nil nil nil curr))

(defconstant +page1-write-map+
    '(:enum cr par0 par1 par2 par3 par4 par5 curr mar0 mar1 mar2 mar3 mar4 mar5 mar6 mar7))

(defconstant +command-map+
    '(:rassoc
      (#b001 . stop)
      (#b010 . start)
      (#b100 . transmit)
      (#o10  . remote-read)
      (#o20  . remote-write)
      (#o30  . send-packet)
      (#o40  . abort-complete)
      (#x00  . page-0)
      (#x40  . page-1)
      (#x80  . page-2)
      (#xc0  . page-3)))

(defconstant +interrupt-status-map+
    '(:enum
      packet-received
      packet-transmitted
      receive-error
      transmit-error
      overwrite-warning
      counter-overflow
      dma-complete
      reset-status))

(defconstant +data-config-map+
    '(:rassoc
      (#x01 . dma-16-bit)
      (#x02 . big-endian)
      (#x04 . dma-address-32bit)
      (#x08 . loopback-off)
      (#x10 . auto-initialize)
      (#x00 . fifo-threshold-2-bytes)
      (#x20 . fifo-threshold-4-bytes)
      (#x40 . fifo-threshold-8-bytes)
      (#x60 . fifo-threshold-12-bytes)))

(defconstant +tx-config-map+
    '(:rassoc
      (#x00 . loopback-mode-0)
      (#x02 . loopback-mode-1)
      (#x04 . loopback-mode-2)
      (#x06 . loopback-mode-3)))

(defconstant +rx-config-map+
    '(:rassoc
      (#x01 . save-error-packets)
      (#x02 . runt-packets)
      (#x04 . broadcast)
      (#x08 . multicast)
      (#x10 . promiscuous)
      (#x20 . monitor-mode)))

(defconstant +command-bit-map+
    '(:enum stop start transmit))

;;; Convenience syntax

(defmacro with-dp8390 ((&optional var io-base-form) &body body)
  `(with-named-integers-syntax (($page0-read +page0-read-map+)
				($page0-write +page0-write-map+)
				($page1-read +page1-read-map+)
				($page1-write +page1-write-map+)
				($command +command-map+)
				($interrupt-status +interrupt-status-map+)
				($data-config +data-config-map+)
				($rx-config +rx-config-map+)
				($tx-config +tx-config-map+)
				($command-bit +command-bit-map+))
     ,@(if (not var)
	   body
	 `((with-io-register-syntax (,var ,io-base-form)
	     ,@body)))))

(defun wait-for-dma-completion (io-base &optional command)
  (with-dp8390 (dp8390 io-base)
    (setf (dp8390 ($page0-write cr)) ($command page-0 abort-complete))
    (if (logbitp ($interrupt-status dma-complete)
		 (dp8390 ($page0-read isr)))
	(setf (dp8390 ($page0-write isr))
	  (ash 1 ($interrupt-status dma-complete)))
      (error "Incomplete dp8390~@[ ~A~] @ #x~X DMA: crda=#x~X~@[, rbcr=#x~X~]."
	     command io-base
	     (io-register8x2 dp8390 ($page0-read crda1) ($page0-read crda0))
	     (let ((x (io-register8x2 dp8390 ($page0-read rbcr1) ($page0-read rbcr0))))
	       (unless (= x #xffff) x)))))
  nil)

(defun initialize-dma (io-base command size &optional address)
  (with-dp8390 (dp8390 io-base)
    (setf (dp8390 ($page0-write cr)) ($command page-0 abort-complete))
    (when address
      (setf (io-register8x2 dp8390 ($page0-write rsar1) ($page0-write rsar0))
	address))
    (setf (io-register8x2 dp8390 ($page0-write rbcr1) ($page0-write rbcr0)) size
	  (dp8390 ($page0-write cr)) command))
  nil)

(defmacro with-dp8390-dma ((dp8390-var rdma-command size &optional address) &body body)
  ;; Must be located inside with-dp8390.
  `(multiple-value-prog1
       (macrolet ((dp8390-abort-dma ()
		    `(setf (,',dp8390-var ($page0-write cr)) ($command abort-complete))))
	 (initialize-dma ,dp8390-var ($command ,rdma-command) ,size ,address)
	 ,@body)
     (wait-for-dma-completion ,dp8390-var ',rdma-command)))

;;; Utility functions

(defun multicast-crc (packet &optional (start 0) (end (length packet)))
  (loop with crc-low26 = #x3ffffff with crc-hi6 = #x3f
      for i from start below end as byte = (aref packet i)
      do (loop for bit from 0 below 8
	     do (if (or (and (logbitp bit byte)
			     (not (logbitp 5 crc-hi6)))
			(and (not (logbitp bit byte))
			     (logbitp 5 crc-hi6)))
		    (setf crc-hi6 (logior (if (logbitp 25 crc-low26) 0 1)
					  (ldb (byte 6 0) (+ crc-hi6 crc-hi6)))
			  crc-low26 (logxor (ldb (byte 26 0) (+ crc-low26 crc-low26 1))
					    #xc11db6))
		  (setf crc-hi6 (logior (ldb (byte 1 25) crc-low26)
					(ldb (byte 6 0) (+ crc-hi6 crc-hi6)))
			crc-low26 (ldb (byte 26 0) (+ crc-low26 crc-low26)))))
      finally (return (values crc-hi6 crc-low26))))

(defun calculate-mar-octet (octet addresses)
  (if (eq t addresses)
      #xff
    (let ((bit-pos (* 8 octet))
	  (result 0))
      (dolist (address addresses)
	(let ((crc (multicast-crc address)))
	  (when (<= bit-pos crc (+ 7 bit-pos))
	    (setf result
	      (logior result (ash 1 (- crc bit-pos)))))))
      result)))

;;; Stateful stuff

(defclass dp8390-device (ethernet-device io-space-device)
  ((io-base
    :initarg :io-base
    :reader io-base)
   (write-pointer			; This is (* 256 CURR)
    :documentation "This register is written by the device and read by the driver when neccessary."
    :initarg :write-pointer
    :accessor write-pointer)
   (read-pointer			; This is (* 256 BNRY)
    :documentation "This register is cached on a write-through basis. It's only read by the device."
    :initarg :read-pointer
    :accessor read-pointer)
   (transmit-buffer
    :initarg :transmit-buffer
    :reader transmit-buffer)
   (ring-start
    :initarg :ring-start
    :reader ring-start)
   (ring-stop
    :initarg :ring-stop
    :reader ring-stop)
   (ring-overflow-count
    :initform 0
    :accessor ring-overflow-count)))

(defun next-packet (device)
  "If there's a packet available in the ring, return its ring pointer address.
   Otherwise, return nil."
  (let ((read-pointer (read-pointer device)))
    (if (/= (write-pointer device)	; Can we tell from the cached values alone?
	    read-pointer)
	read-pointer
      (with-dp8390 (dp8390 (io-base device))
	(setf (dp8390 ($page0-write cr)) ($command page-1))
	(let ((new-write-pointer (* 256 (dp8390 ($page1-read curr))))) ; update CURR register cache.
	  (setf (dp8390 ($page1-write cr)) ($command page-0)) ; restore page 0
	  (unless (= new-write-pointer read-pointer)
	    (setf (write-pointer device) new-write-pointer)
	    read-pointer))))))

(defmethod (setf mac-address) :after (mac-address (device dp8390-device))
  "Keep the dp8390 device registers in sync with mac-address."
  (check-type mac-address vector)
  (with-dp8390 (dp8390 (io-base device))
    (setf (dp8390 ($page0-write cr))	; go to page1
      ($command page-1 abort-complete start))
    (loop for a across mac-address as i from 1 to 6
	do (setf (dp8390 i) a))
    (setf (dp8390 ($page0-write cr))	; go back to page0
      ($command page-0 abort-complete start)))
  nil)

(defun rcr-value (device)
  (with-dp8390 ()
    (logior (if (not (null (accept-multicast-addresses device))) ($rx-config multicast) 0)
	    (if (accept-broadcasts-p device) ($rx-config broadcast) 0)
	    (if (promiscuous-p device) ($rx-config promiscuous) 0))))

(defun install-rcr (device)
  (with-dp8390 (dp8390 (io-base device))
    (setf (dp8390 ($page0-write cr)) ($command page-0)
	  (dp8390 ($page0-write rcr)) (rcr-value device))))

(defmethod (setf accept-multicast-addresses) :after (multicast-addresses (device dp8390-device))
  (with-dp8390 (dp8390 (io-base device))
    (cond
     ((not (null multicast-addresses))
      (setf (dp8390 ($page0-write cr)) ($command page-1))
      (with-io-register-syntax (mar (+ ($page1-write mar0) (io-base device)))
	(dotimes (i 8)
	  (setf (mar i) (calculate-mar-octet i multicast-addresses)))))
     ((null multicast-addresses)
      (with-io-register-syntax (mar (+ ($page1-write mar0) (io-base device)))
	(dotimes (i 8)
	  (setf (mar i) 0)))))
    (setf (dp8390 ($page0-write cr)) ($command page-0)
	  (dp8390 ($page0-write rcr)) (rcr-value device)))
  nil)

(defmethod (setf accept-broadcasts-p) :after (accept-broadcasts-p (device dp8390-device))
  (install-rcr device))

(defmethod (setf promiscuous-p) :after (promiscuous-p (device dp8390-device))
  (install-rcr device))

(defun dp8390-initialize (device &key (rx-config (rcr-value device)) (tx-config 0) (interrupt-mask #x1b)
				      (data-config (with-dp8390 ()
						     ($data-config dma-16-bit
								   loopback-off
								   fifo-threshold-8-bytes))))
  (with-dp8390 (dp8390 (io-base device))
    (setf (dp8390 ($page0-write cr)) ($command page-0 stop) ; stop mode
	  (dp8390 ($page0-write dcr)) data-config
	  (dp8390 ($page0-write rbcr0)) 0
	  (dp8390 ($page0-write rbcr1))	0
	  (dp8390 ($page0-write rcr)) rx-config
	  (dp8390 ($page0-write tpsr)) (truncate (slot-value device 'transmit-buffer) 256) ; address
	  (dp8390 ($page0-write tcr)) ($tx-config loopback-mode-1) ; internal loopback
	  (dp8390 ($page0-write pstart)) (truncate (slot-value device 'ring-start) 256)
	  (dp8390 ($page0-write bnry)) (truncate (slot-value device 'ring-start) 256)
	  (dp8390 ($page0-write pstop)) (truncate (slot-value device 'ring-stop) 256)
	  (dp8390 ($page0-write cr)) ($command page-1 stop)
	  (dp8390 ($page1-write curr)) (truncate (slot-value device 'ring-start) 256)
	  (dp8390 ($page1-write cr)) ($command page-0 start)
	  (dp8390 ($page0-write isr)) #xff
	  (dp8390 ($page0-write imr)) interrupt-mask
	  (dp8390 ($page0-write tcr)) tx-config))
  t)


;;;


