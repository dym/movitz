;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ip4.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Apr 30 13:52:57 2003
;;;;                
;;;; $Id: ip4.lisp,v 1.11 2004/11/24 14:22:57 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(require :lib/misc)
(require :lib/net/ethernet)
(provide :lib/net/ip4)

(defpackage muerte.ip4
  (:use #:muerte.cl #:muerte #:muerte.ethernet #:muerte.lib)
  (:export #:pprint-ip4
	   #:read-ip4-address
	   #:ip4-address
	   #:ip4-test
	   #:ip4-free
	   #:format-ip4-header
	   #:format-udp-header
	   #:*ip4-nic*
	   #:*ip4-ip*))

(in-package muerte.ip4)

(defvar *ip4-nic* nil)
(defvar *ip4-ip* nil)

(defmacro ip4-ref (packet start offset type)
  `(memref ,packet (+ (muerte:movitz-type-slot-offset 'movitz-basic-vector 'data)
		      ,start ,offset)
	   :endian :big
	   :type ,type))

(require :lib/net/arp)

(defclass ip4-stack ()
  ((interface
    :initarg :interface
    :reader interface)
   (address
    :initarg :address
    :accessor address)))

(defmethod unknown-packet ((stack ip4-stack) packet)
  (declare (ignore packet)))
  

(define-named-integer ip-protocol (:export-constants t)
  (1 icmp)
  (6 tcp)
  (17 udp))

(define-named-integer ip-header (:only-constants t :export-constants t)
  (0 version-header-length)
  (1 tos)
  (2 length)
  (4 id)
  (6 flags-frament-offset)
  (8 ttl)
  (9 protocol)
  (10 checksum)
  (12 source)
  (16 destination)
  (20 options))

(defun ip-protocol (packet &optional (start 14))
  (ip4-ref packet start +ip-header-protocol+ :unsigned-byte8))

(defun ip-header-length (packet &optional (start 14))
  (ldb (byte 4 0)
       (ip4-ref packet start +ip-header-version-header-length+ :unsigned-byte8)))

(defun ip-header-source (packet &optional (start 14))
  (subseq packet (+ start 12) (+ start 16)))

(defun ip-header-destination (packet &optional (start 14))
  (subseq packet (+ start 16) (+ start 20)))

(defun format-ip4-header (packet &key (start 14) (payload 0)
				      (id 0) (ttl 64) (checksum t)
				      (protocol 0) (flags 0)
				      (fragment-offset 0)
				      source destination)
  (setf (ip4-ref packet start 0 :unsigned-byte16) #x4500
	(ip4-ref packet start 2 :unsigned-byte16) (+ payload 20)
	(ip4-ref packet start 4 :unsigned-byte16) id
	(ip4-ref packet start 6 :unsigned-byte16) (dpb flags (byte 3 13) fragment-offset)
	(ip4-ref packet start 8 :unsigned-byte8) ttl
	(ip4-ref packet start 9 :unsigned-byte8) protocol)
  (when source
    (replace packet source :start1 (+ start 12)))
  (when destination
    (replace packet destination :start1 (+ start 16)))
  (cond
   ((eq t checksum)
    (setf (ip4-ref packet start 10 :unsigned-byte16) 0)
    (setf (ip4-ref packet start 10 :unsigned-byte16)
      (logxor #xffff
	      (checksum-octets packet start (+ start 20)))))
   ((integerp checksum)
    (setf (ip4-ref packet start 10 :unsigned-byte16) checksum)))
  packet)

(defun checksum-ok (x &rest more-xes)
  (declare (dynamic-extent more-xes))
  (let ((x (reduce #'add-u16-ones-complement more-xes :initial-value x)))
    (= #xffff
       (+ (ldb (byte 16 0) x)
	  (ash x -16)))))

(defun ip-input (stack packet start)
  (let ((header-size (* 4 (ip-header-length packet start))))
    (cond
     ((not (checksum-ok (checksum-octets packet start (+ start header-size))))
      (warn "IP4 header checksum failed (from ~@/ip4:pprint-ip4/ to ~:/ip4:pprint-ip4/ proto ~A len ~D)."
	    packet packet
	    (integer-name 'ip-protocol (ip-protocol packet start) nil)
	    (length packet))
      #+ignore
      (loop for y from 0 below (length packet) by 16
	  do (fresh-line)
	     (loop for x from y below (min (length packet) (+ y 16))
		 when (zerop (rem x 4))
		 do (format t " ")
		 do (format t " ~2,'0X" (aref packet x)))
	     (write-string "   ")
	     (loop for x from y below (min (length packet) (+ y 16))
		 as c = (code-char (aref packet x))
		 do (write-char (if (alphanumericp c) c #\.)))))
     ((mismatch packet (address stack)
		:start1 (+ start +ip-header-destination+)
		:end1 (+ start +ip-header-destination+ 4))
      #+ignore
      (warn "IPv4 Packet from ~@/ip4:pprint-ip4/ not for me, but for ~:/ip4:pprint-ip4/."
	    packet packet))
     (t (named-integer-case ip-protocol (ip-protocol packet start)
	  (icmp
	   (icmp-input stack packet start (+ start header-size)))
	  (udp
	   (udp-input stack packet start (+ start header-size)))
	  (tcp
	   (tcp-input stack packet start (+ start header-size)))
	  (t (warn "Unknown IPv4 protocol ~A received from ~@/ip4:pprint-ip4/."
		   (integer-name 'ip-protocol (ip-protocol packet start) nil)
		   packet)))))))



(defun pprint-ip4 (stream address &optional colon at (start 0 start-p))
  "@ means default packet source, : means default packet destination."
  (incf start (cond (colon +ip-header-destination+)
		    (at +ip-header-source+)
		    (t 0)))
  (when (and (not start-p) (or colon at))
    (incf start 14))
  (format stream "~D.~D.~D.~D"
	  (aref address (+ start 0))
	  (aref address (+ start 1))
	  (aref address (+ start 2))
	  (aref address (+ start 3)))
  nil)

(defun arp-input (stack packet start)
;;;  (warn "arp operation: ~S ~S ~S"
;;;	(integer-name 'arp-op (arp-operation packet start) nil)
;;;	(integer-name 'arp-hard-type (arp-hard-type packet start) nil)
;;;	(integer-name 'ether-type (arp-prot-type packet start) nil))
  (case (arp-operation packet start)
    (#.+arp-op-request+
     (cond
      ((and (= +arp-hard-type-ethernet+
	       (arp-hard-type packet start))
	    (= +ether-type-ip4+
	       (arp-prot-type packet start))
	    (not (mismatch (address stack) packet :start2 (+ start 24) :end2 (+ start 28))))
       (warn "arp request from ~v/ip4:pprint-ip4/." (+ start 14) packet)
       (transmit (interface stack)
		 (format-ethernet-packet (format-arp-request nil +arp-op-reply+
							     (address stack)
							     (mac-address (interface stack))
							     packet :target-ip-address-start (+ start 14)
							     :target-hardware-address packet
							     :target-hardware-address-start (+ start 8))
					 (mac-address (interface stack))
					 packet
					 muerte.ethernet:+ether-type-arp+
					 :destination-start (+ start 8))))
      (t (unknown-packet stack packet)
	 #+ignore (warn "ARP request for not me ~/ip4:pprint-ip4/: ~v/ip4:pprint-ip4/."
			(address stack) (+ start 24) packet))))
    (#.+arp-op-reply+
     (warn "Received an ARP reply: ~v/ip4:pprint-ip4/ is ~v/ethernet:pprint-mac/."
	   (+ start 14) packet
	   (+ start 8) packet))
    (t (unknown-packet stack packet)
       (warn "Received unknown ARP packet of type ~D~@[ ~A~]"
	     (arp-operation packet start)
	     (integer-name 'arp-op (arp-operation packet start) nil)))))

;;; ICMP

(define-named-integer icmp-type ()
  (0 echo-reply)
  (3 destination-unreachable)
  (4 source-quench)
  (5 redirect)
  (8 echo-request))

(defun icmp-type (packet &optional (start 34))
  (ip4-ref packet start 0 :unsigned-byte8))

(defun (setf icmp-type) (value packet &optional (start 34))
  (setf (ip4-ref packet start 0 :unsigned-byte8)
    value))

(defun icmp-code (packet &optional (start 34))
  (ip4-ref packet start 1 :unsigned-byte8))

(defun icmp-checksum (packet &optional (start 34))
  (ip4-ref packet start 2 :unsigned-byte16))

(defun icmp-identifier (packet &optional (start 34))
  (ip4-ref packet start 4 :unsigned-byte16))

(defun icmp-seqno (packet &optional (start 34))
  (ip4-ref packet start 6 :unsigned-byte16))

(defun (setf icmp-checksum) (value packet &optional (start 34))
  (setf (ip4-ref packet start 2 :unsigned-byte16)
    value))

(defmethod icmp-input ((stack ip4-stack) packet ip-start icmp-start)
  (named-integer-case icmp-type (icmp-type packet icmp-start)
    (echo-request
     (icmp-echo-request stack packet ip-start icmp-start))))

(defun icmp-echo-request (stack packet ip-start icmp-start)
  (let ((checksum-ok (checksum-octets packet icmp-start)))
    #+ignore
    (warn "got ping at ~D size ~D from ~v@/ip4:pprint-ip4/ checksum is ~:[WRONG!~;Ok~]."
	  icmp-start
	  (- (length packet) icmp-start)
	  ip-start packet
	  checksum-ok)
    (cond
     ((not checksum-ok)
      (warn "ICMP checksum failed from ~v@/ip4:pprint-ip4/." ip-start packet)
      (loop for i upfrom (+ icmp-start 8 8) below (length packet)
	  when (/= (aref packet i)
		   (ldb (byte 8 0)
			(- i icmp-start 8)))
	  do (warn "mismatch at ~D of ~D: Got #x~X, wanted #x~X."
		   i (length packet)
		   (aref packet i)
		   (ldb (byte 8 0)
			(- i icmp-start 8)))
	  and do (return)
	  finally (warn "No mismatch.")))
     (checksum-ok
      #+ignore
      (format t "~&Got ping ID #x~X seqno #x~X len ~D. icmp-start=~d~%"
	      (icmp-identifier packet icmp-start)
	      (icmp-seqno packet icmp-start)
	      (length packet)
	      icmp-start)
      (replace packet packet
	       :start1 (+ ip-start +ip-header-destination+)
	       :start2 (+ ip-start +ip-header-source+)
	       :end2 (+ ip-start +ip-header-source+ 4))
      (replace packet packet
	       :start1 +ether-header-destination+
	       :start2 +ether-header-source+
	       :end2 (+ +ether-header-source+ 6))
      (replace packet (address stack)
	       :start1 (+ ip-start +ip-header-source+))
      (replace packet (mac-address (interface stack))
	       :start1 +ether-header-source+)
      (setf (icmp-type packet icmp-start) +icmp-type-echo-reply+)
      (let ((new-checksum (+ (icmp-checksum packet icmp-start)
			     (ash +icmp-type-echo-request+ 8))))
	(setf (icmp-checksum packet icmp-start)
	  (+ (ldb (byte 16 0) new-checksum)
	     (ash new-checksum -16))))
      (transmit (interface stack) packet)
      #+ignore (write-char #\.)))))

;;;; UDP

(defun udp-src-port (packet &optional (start 34))
  (ip4-ref packet start 0 :unsigned-byte16))

(defun (setf udp-src-port) (value packet &optional (start 34))
  (setf (ip4-ref packet start 0 :unsigned-byte16)
    value))

(defun udp-dst-port (packet &optional (start 34))
  (ip4-ref packet start 2 :unsigned-byte16))

(defun (setf udp-dst-port) (value packet &optional (start 34))
  (setf (ip4-ref packet start 2 :unsigned-byte16)
    value))

(defun udp-length (packet &optional (start 34))
  (ip4-ref packet start 4 :unsigned-byte16))

(defun (setf udp-length) (value packet &optional (start 34))
  (setf (ip4-ref packet start 4 :unsigned-byte16)
    value))

(defun udp-checksum (packet &optional (start 34))
  (ip4-ref packet start 6 :unsigned-byte16))

(defun (setf udp-checksum) (value packet &optional (start 34))
  (setf (ip4-ref packet start 6 :unsigned-byte16)
    value))

(defun format-udp-header (packet &key (start 34)
				      (source *ip4-ip*) (source-port 1024)
				      destination (destination-port 0)
				      (payload (- (length packet) start 8))
				      (checksum t))
  (let ((udp-length (+ payload 8)))
    (format-ip4-header packet
		       :source source
		       :destination destination
		       :payload udp-length
		       :protocol +ip-protocol-udp+)
    (setf (ip4-ref packet start 0 :unsigned-byte16) source-port
	  (ip4-ref packet start 2 :unsigned-byte16) destination-port
	  (ip4-ref packet start 4 :unsigned-byte16) udp-length)
    (cond
     ((integerp checksum)
      (setf (ip4-ref packet start 6 :unsigned-byte16) checksum))
     ((eq t checksum)
      (setf (ip4-ref packet start 6 :unsigned-byte16) 0)
      (when (oddp udp-length)		; Ensure zero-padding for checksum.
	(setf (ip4-ref packet start udp-length :unsigned-byte8) 0))
      (setf (ip4-ref packet start 6 :unsigned-byte16)
	(logxor #xffff
		(add-u16-ones-complement (checksum-octets source)
					 (checksum-octets destination)
					 +ip-protocol-udp+ udp-length
					 (checksum-octets packet start (+ start udp-length)))))))
    packet))
  

(defmethod udp-input ((stack ip4-stack) packet ip-start udp-start)
  (warn "Got UDP packet of length ~D from ~@v/ip4:pprint-ip4/."
	(- (length packet) udp-start)
	ip-start packet))


;;;; TCP

(define-named-integer tcp-header (:only-constants t)
  ( 0 src-port)
  ( 2 dst-port)
  ( 4 seqno)
  ( 8 ackno)
  (12 flags-length)
  (14 window-size)
  (16 checksum)
  (18 urgent-pointer)
  (20 options))

(define-named-integer tcp-flag (:only-constants t)
  (0 fin)
  (1 syn)
  (2 rst)
  (3 psh)
  (4 ack)
  (5 urg))

(defun tcp-src-port (packet &optional (start 34))
  (ip4-ref packet start +tcp-header-src-port+ :unsigned-byte16))

(defun tcp-dst-port (packet &optional (start 34))
  (ip4-ref packet start +tcp-header-dst-port+ :unsigned-byte16))

(defun tcp-header-length (packet &optional (start 34))
  (ldb (byte 4 4)
       (ip4-ref packet start +tcp-header-flags-length+ :unsigned-byte8)))

(defun tcp-flags (packet &optional (start 34))
  (ldb (byte 6 0)
       (ip4-ref packet start (+ +tcp-header-flags-length+ 1) :unsigned-byte8)))

(defun tcp-window-size (packet &optional (start 34))
  (ip4-ref packet start +tcp-header-window-size+ :unsigned-byte16))

(defun tcp-checksum (packet &optional (start 34))
  (ip4-ref packet start +tcp-header-checksum+ :unsigned-byte16))

(defun print-flags (x set)
  (loop with first = t
      for bit = 1 then (* bit 2) while (<= bit x)
      as flag in set
      do (when (plusp (logand bit x))
	   (unless first
	     (write-char #\space))
	   (write flag)
	   (setf first nil))
      finally (when first (write "[none]"))
	      (return (values))))

(defmethod tcp-input ((stack ip4-stack) packet ip-start tcp-start)
  (format t "TCP length ~D from ~@v/ip4:pprint-ip4/, win ~D, hlen ~D, flags: "
	  (- (length packet) tcp-start)
	  ip-start packet
	  (tcp-window-size packet tcp-start)
	  (tcp-header-length packet tcp-start))
  (print-flags (tcp-flags packet tcp-start) '(fin syn rst psh ack urg)))

;;;;;

(defun read-ip4-address (string &optional (start 0))
  (prog (a b c d (i start))
    (multiple-value-setq (a i)
      (parse-integer string :start i :junk-allowed t))
    (unless (and (<= 0 a #xff) (char= #\. (char string i)))
      (go parse-failure))
    (multiple-value-setq (b i)
      (parse-integer string :start (1+ i) :junk-allowed t))
    (unless (and (<= 0 b #xff) (char= #\. (char string i)))
      (go parse-failure))
    (multiple-value-setq (c i)
      (parse-integer string :start (1+ i) :junk-allowed t))
    (unless (and (<= 0 b #xff) (char= #\. (char string i)))
      (go parse-failure))
    (multiple-value-setq (d i)
      (parse-integer string :start (1+ i) :junk-allowed t))
    (unless (<= 0 b #xff)
      (go parse-failure))
    (let ((x (make-array 4 :element-type '(unsigned-byte 8))))
      (setf (aref x 0) a (aref x 1) b (aref x 2) c (aref x 3) d)
      (return x))
   parse-failure
    (error "Not an IPv4 address at position ~D in ~S."
	   i string)))
    

(defun ip4-address (specifier &optional (start 0))
  (or (ignore-errors
       (typecase specifier
	 ((or string symbol)
	  (read-ip4-address (string specifier) start))
	 (vector
	  (loop with address = (make-array 4 :element-type '(unsigned-byte 8))
	      for i from 0 to 3
	      as n = (aref specifier (+ start i))
	      do (check-type n (unsigned-byte 8))
		 (setf (aref address i) n)
	      finally (return address)))))
      (error "Not an IPv4 address: ~S." specifier)))
       
	       

(defun ip4-free ()
  (when *ne2000*
    (muerte.x86-pc::free-io-space *ne2000*)
    (setf *ne2000* nil))
  (values))

(defun ip4-init ()
  (unless *ip4-nic*
    (let ((ethernet
	   (some #'muerte.x86-pc.ne2k:ne2k-probe
		 muerte.x86-pc.ne2k:*ne2k-probe-addresses*)))
      (assert ethernet ethernet "No ethernet device.")
      (setf *ip4-nic* ethernet)))
  (unless *ip4-ip*
    (setf *ip4-ip* (ip4-address :129.242.16.173)))
  (values *ip4-nic* *ip4-ip*))

(defun ip4-test (&key (router #(129 242 16 1)))
  (ip4-init)
  (let ((ethernet *ip4-nic*)
	(stack (make-instance 'ip4-stack
		 :interface *ip4-nic*
		 :address *ip4-ip*)))
    (when router
      (transmit (interface stack)
		(format-ethernet-packet (format-arp-request nil +arp-op-request+
							    (address stack)
							    (mac-address (interface stack))
							    (ip4-address router))
					(mac-address (interface stack))
					+broadcast-address+
					+ether-type-arp+)))
    (loop
      (case (muerte.x86-pc.keyboard:poll-char)
	((nil))
	((#\esc) (break "You broke ip4!"))
	(t (return (values))))
      (let ((packet (and (packet-available-p ethernet)
			 (receive ethernet))))
	(when packet
	  #+ignore
	  (format t "~&From ~@/ethernet:pprint-mac/ to ~:/ethernet:pprint-mac/ of type ~S.~%"
		  packet packet (integer-name 'ether-type (ether-type packet) nil))
	  (case (ether-type packet)
	    (#.+ether-type-arp+ (arp-input stack packet 14))
	    (#.+ether-type-ip4+ (ip-input stack packet 14))
	    (#.+ether-type-mswin-heartbeat+
	     (format t "~&MS heartbeat from ~@/ethernet:pprint-mac/: [" packet)
	     (loop for i from 40 below (length packet) by 2
		 do (write-char (code-char (aref packet i))))
	     (format t "]~%")
	     (let ((pos (or (search packet #(129 242 16) :start1 14)
			    (search packet #(129 242) :start1 14))))
	       (if pos
		   (format t "~&MS heartbeat from ~@/ethernet:pprint-mac/ found possible IP at ~D: ~/ip4:pprint-ip4.~%"
			   packet pos (subseq packet pos (+ pos 6)))
		 (progn
		   (format t "~&MS heartbeat found no IP from ~:@/ethernet:pprint-mac/.~%"
			   packet)
		   (loop for y from 0 below (length packet) by 16
		       do (format t "~&  ")
			  (loop for x from y below (min (length packet) (+ y 16))
			      when (zerop (rem x 4))
			      do (format t "  ")
			      do (format t " ~2,'0X" (aref packet x))))
		   (fresh-line)))))
	    (t (cond
		((ether-802.3-snap-p packet)
		 (format t "~&~:@/ethernet:pprint-mac/ IEEE 802.3 SNAP type ~A len ~D.~%"
			 packet (integer-name 'ether-type (ether-802.3-snap-type packet) nil)
			 (length packet)))
		((ether-802.3-p packet)
		 (format t "~&~:@/ethernet:pprint-mac/ IEEE 802.3 LLC ssap ~S, dsap ~S, type ~D len ~D.~%"
			 packet
			 (ether-802.3-llc-ssap packet)
			 (ether-802.3-llc-dsap packet)
			 (ether-802.3-llc-type packet)
			 (length packet)))
		(t (format t "~&From ~:@/ethernet:pprint-mac/ unknown ether type ~S."
			   packet (integer-name 'ether-type (ether-type packet) nil))))))))))
  (values))
