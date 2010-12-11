;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ip6.lisp
;;;; Description:   Internet Protocol version 6.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov 14 17:25:31 2001
;;;;                
;;;; $Id: ip6.lisp,v 1.8 2008-06-13 16:25:31 aantoniadis Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/all)
(require :x86-pc/pit8253)
(require :x86-pc/ne2k)
(require :lib/named-integers)
(require :lib/misc)
(require :lib/net/ethernet)
(provide :lib/net/ip6)

(defpackage muerte.ip6
  (:use #:muerte.cl #:muerte.lib #:muerte.x86-pc #:muerte.ethernet)
  (:export #:packet-version
	   #:packet-source
	   #:packet-destination
	   #:packet-length
	   #:packet-traffic-class
	   #:packet-next-header
	   #:packet-flow-label
	   #:packet-hop-limit

	   #:pprint-ip6
	   #:ip6-test
	   #:ip6-free
	   ))

(in-package muerte.ip6)

;; (defvar *address-cache* (make-hash-table #'equalp))
(defconstant +unspecified-address+
    #(#x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00))
(defconstant +loopback-address+
    #(#x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x01))
(defconstant +link-local-routers+
    #(#xff #x02 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x02))
(defconstant +site-local-routers+
    #(#xff #x05 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x02))

(defun address-prefix-type (address &key (start 0))
  "RFC 2373, sec. 2.4: Address Type Representation."
  (case (aref address start)
    (#x00 (cond
	   ((not (mismatch address +unspecified-address+ :start1 start :end1 (+ start 16)))
	    :unspecified-address)
	   ((not (mismatch address +loopback-address+ :start1 start :end1 (+ start 16)))
	    :loopback-address)
	   ((not (mismatch address #(0 0 0 0 0 0 0 0 0 0 0 0) :start1 start :end1 (+ start 12)))
	    :ip4-transition-address)
	   (t :unknown-reserved)))
    (#xff :multicast)
    (#xfe (case (ldb (byte 2 6) (aref address (1+ start)))
	    (#b10 :link-local-unicast)
	    (#b11 :site-local-unicast)))
    (t (when (= #b001 (ldb (byte 3 5) (aref address start)))
	 :global-unicast))))

;;; IP header fields accessors. RFC 2460 Sec. 3.

(defun packet-version (packet &optional (start 14))
  (ldb (byte 4 4) (aref packet start)))

(defun (setf packet-version) (version packet &optional (start 14))
  (setf (aref packet start) (dpb version (byte 4 4) (or (aref packet start) 0)))
  version)

(defun packet-traffic-class (packet &optional (start 14))
  (dpb (ldb (byte 4 0) (aref packet (+ start 0)))
       (byte 4 4)
       (ldb (byte 4 4) (aref packet (+ start 1)))))

(defun (setf packet-traffic-class) (traffic-class packet &optional (start 14))
  (setf (aref packet (+ start 0)) (logior #x60 (ldb (byte 4 4) traffic-class))
	(aref packet (+ start 1)) (dpb (ldb (byte 4 0) traffic-class)
				       (byte 4 4)
				       (or (aref packet (+ start 1)) 0)))
  traffic-class)

(defun packet-flow-label (packet &optional (start 14))
  (logior (ash (ldb (byte 4 0) (aref packet (+ start 1))) 16)
	  (ash (aref packet (+ start 2)) 8)
	  (aref packet (+ start 3))))

(defun (setf packet-flow-label) (flow-label packet &optional (start 14))
  (setf (aref packet (+ start 1)) (dpb (ldb (byte 4 16) flow-label)
				       (byte 4 0)
				       (aref packet (+ start 1)))
	(aref packet (+ start 2)) (ldb (byte 8 8) flow-label)
	(aref packet (+ start 3)) (ldb (byte 8 0) flow-label))
  flow-label)

(defun packet-length (packet &optional (start 14))
  (logior (ash (aref packet (+ start 4)) 8)
	  (aref packet (+ start 5))))

(defun (setf packet-length) (length packet &optional (start 14))
  (setf (aref packet (+ start 4)) (ldb (byte 8 8) length)
	(aref packet (+ start 5)) (ldb (byte 8 0) length))
  length)

(define-named-integer ip-header-type ()
  (17 udp)
  (58 icmp))

(defun packet-next-header (packet &optional (start 14))
  (aref packet (+ start 6)))

(defun (setf packet-next-header) (next-header packet &optional (start 14))
  (setf (aref packet (+ start 6)) next-header))

(defun packet-hop-limit (packet &optional (start 14))
  (aref packet (+ start 7)))

(defun (setf packet-hop-limit) (hop-limit packet &optional (start 14))
  (setf (aref packet (+ start 7)) hop-limit))

(defun packet-source (packet &optional (start 14))
  (subseq packet (+ start 8) (+ start 24)))

(defun (setf packet-source) (source packet &optional (start 14) &key (source-start 0))
  (replace packet source :start1 (+ start 8) :end1 (+ start 24) :start2 source-start)
  source)

(defun packet-destination (packet &optional (start 14))
  (subseq packet (+ start 24) (+ start 40)))

(defun (setf packet-destination) (destination packet &optional (start 14) &key (destination-start 0))
  (replace packet destination :start1 (+ start 24) :end1 (+ start 40) :start2 destination-start)
  destination)

(defun format-ip6-header (packet &key (start 14) (traffic-class 0) (flow-label 0)
				      payload-length next-header (hop-limit 64)
				      source (source-start 0) destination (destination-start 0))
  (setf ;; (packet-version packet :start start) 6
	(packet-traffic-class packet start) traffic-class
	(packet-flow-label packet start) flow-label)
  (when payload-length
    (setf (packet-length packet start) payload-length))
  (when next-header
    (setf (packet-next-header packet start) next-header))
  (when hop-limit
    (setf (packet-hop-limit packet start) hop-limit))
  (when source
    (setf (packet-source packet start :source-start source-start) source))
  (when destination
    (setf (packet-destination packet start :destination-start destination-start)
      destination))
  packet)

;;; General purpose checksum functions.

(defun checksum-pseudo-header (source destination length next-header
			       &key (source-start 0) (destination-start 0))
  "Generate sum of 16-bit big-endian words for a IPv6 pseudo-header.
RFC 2460, Section 8.1: Upper-Layer Checksums."
  (+ (checksum-octets source source-start (+ source-start 16))
     (checksum-octets destination destination-start (+ destination-start 16))
     (ash length -16)
     (ldb (byte 16 0) length)
     next-header))

;;; UDP, RFC 768

(defun udp-header-source (packet &optional (start 54))
  (logior (ash (aref packet (+ start 0)) 8)
	  (aref packet (+ start 1))))

(defun (setf udp-header-source) (value packet &optional (start 54))
  (setf (aref packet (+ start 0)) (ldb (byte 8 8) value)
	(aref packet (+ start 1)) (ldb (byte 8 0) value))
  value)

(defun udp-header-destination (packet &optional (start 54))
  (logior (ash (aref packet (+ start 2)) 8)
	  (aref packet (+ start 3))))

(defun (setf udp-header-destination) (value packet &optional (start 54))
  (setf (aref packet (+ start 2)) (ldb (byte 8 8) value)
	(aref packet (+ start 3)) (ldb (byte 8 0) value))
  value)

(defun udp-header-length (packet &optional (start 54))
  (logior (ash (aref packet (+ start 4)) 8)
	  (aref packet (+ start 5))))

(defun (setf udp-header-length) (value packet &optional (start 54))
  (setf (aref packet (+ start 4)) (ldb (byte 8 8) value)
	(aref packet (+ start 5)) (ldb (byte 8 0) value))
  value)

(defun udp-header-checksum (packet &optional (start 54))
  (logior (ash (aref packet (+ start 6)) 8)
	  (aref packet (+ start 7))))

(defun udp-checksum (packet &key (udp-header-start 54) (ip-header-start 14)
				 (length (udp-header-length packet udp-header-start)))
  (let ((x (+ (checksum-pseudo-header packet packet length 17
				      :source-start (+ 8 ip-header-start)
				      :destination-start (+ 24 ip-header-start))
	      length
	      (udp-header-source packet udp-header-start)
	      (udp-header-destination packet udp-header-start)
	      (checksum-octets packet (+ udp-header-start 8) (+ udp-header-start length)))))
    (setf x (+ (ldb (byte 16 0) x)
	       (ash x -16)))
    (logxor (+ (ldb (byte 16 0) x)
	       (ash x -16))
	    #xffff)))



;;; ICMP

(define-named-integer icmp-header-type ()
  (1 destination-unreachable)
  (2 packet-too-big)
  (3 time-exceeded)
  (4 parameter-problem)
  (128 echo-request)
  (129 echo-reply)
  (135 neighbor-solicitation)
  (136 neighbor-advertisment))

(defun icmp-header-type (packet &optional (start 54))
  (aref packet start))

(defun (setf icmp-header-type) (header-type packet &optional (start 54))
  (setf (aref packet start) header-type))

(defun icmp-header-code (packet &optional (start 54))
  (aref packet (1+ start)))

(defun (setf icmp-header-code) (code packet &optional (start 54))
  (setf (aref packet (1+ start)) code))

(defun icmp-header-checksum (packet &optional (start 54))
  (logior (ash (aref packet (+ start 2)) 8)
	  (aref packet (+ start 3))))

(defun (setf icmp-header-checksum) (checksum packet &optional (start 54))
  (setf (aref packet (+ start 2)) (ldb (byte 8 8) checksum)
	(aref packet (+ start 3)) (ldb (byte 8 0) checksum))
  checksum)

(defun icmp-checksum (packet &key (icmp-header-start 54) (ip-header-start 14)
				  (length (packet-length packet ip-header-start)))
  (let ((x (+ (checksum-pseudo-header packet packet length 58
				      :source-start (+ 8 ip-header-start)
				      :destination-start (+ 24 ip-header-start))
	      (ash (aref packet icmp-header-start) 8)
	      (aref packet (+ icmp-header-start 1))
	      (checksum-octets packet (+ icmp-header-start 4) (+ icmp-header-start length)))))
    (setf x (+ (ldb (byte 16 0) x)
	       (ash x -16)))
    (logxor (+ (ldb (byte 16 0) x)
	       (ash x -16))
	    #xffff)))

;;;

(defstruct neighbor-cache
  (vector (make-array 31))
  (vector-size 31)
  (elements 0))

;; A neighbor-cache is an hash-table IP6-address => ethernet MAC-address.

(defun sxhash-address (neighbor-cache address start)
  (declare (type (unsigned-byte 16) start))
  (rem (+ (aref address (+ start 1))
	  (aref address (+ start 15))
	  (- (aref address (+ start 14))))
       (neighbor-cache-vector-size neighbor-cache)))

(defun look-up-neighbor (neighbor-cache neighbor-address &key (start 38))
  (dolist (l (svref (neighbor-cache-vector neighbor-cache)
		    (sxhash-address neighbor-cache neighbor-address start)))
    (unless (mismatch neighbor-address (car l) :start1 start :end1 (+ start 16))
      (return (cdr l)))))

(defun (setf look-up-neighbor) (mac-address neighbor-cache neighbor-address
				&key (start 38) (mac-start 0))
  (let ((slot (sxhash-address neighbor-cache neighbor-address start)))
    (or (dolist (l (aref (neighbor-cache-vector neighbor-cache) slot))
	  (unless (mismatch neighbor-address (car l) :start1 start :end1 (+ start 16))
	    (replace (cdr l) mac-address :start2 mac-start)
	    (return t)))
	(progn
	  (when (> (+ 10 (neighbor-cache-elements neighbor-cache))
		   (length (neighbor-cache-vector neighbor-cache)))
	    (warn "Rehashing neighbors..")
	    (let* ((old-vector (neighbor-cache-vector neighbor-cache))
		   (new-size (1- (* 2 (length old-vector)))))
	      (setf (neighbor-cache-vector neighbor-cache) (make-array new-size)
		    (neighbor-cache-vector-size neighbor-cache) new-size)
	      (loop for x across old-vector do
		    (loop for (addr . mac) in x do 
			  (setf (look-up-neighbor addr neighbor-cache) mac)))))
	  (push (cons (subseq neighbor-address start (+ start 16))
		      (subseq mac-address mac-start (+ mac-start 6)))
		(aref (neighbor-cache-vector neighbor-cache) slot))
	  (incf (neighbor-cache-elements neighbor-cache)))))
  mac-address)

;;;

(defun pprint-ip6 (stream address &optional colon at (start 0))
  "Pretty-print an IPv6 address. Callable from format ~/ip6:pprint-ip6/."
  (declare (ignore at))
  (flet ((addr-elt (address start index)
	   (+ (* 256 (aref address (+ start (* 2 index))))
	      (aref address (+ start 1 (* 2 index))))))
    (let ((null-position nil)
	  (null-length 0))
      (unless colon
	(do ((i start (+ i 2))
	     (j 0 (1+ j)))
	    ((>= j 8) null-position)
	  (let ((x (- (or (position-if #'plusp address :start i) (+ i 16)) i)))
	    (when (> x null-length)
	      (let ((y (truncate x 2)))
		(setf null-position j
		      null-length y
		      i (+ i (* 2 y))
		      j (+ j y)))))))
      (cond
       ((or (not null-position)
	    (<= null-length 2))
	(dotimes (i 7)
	  (format stream "~X:" (addr-elt address start i)))
	(format stream "~X" (addr-elt address start 7)))
       ((= 8 null-length)
	(write-string "::0" stream))
       (t (dotimes (i null-position)
	    (format stream "~X:" (addr-elt address start i)))
	  (when (= start null-position)
	    (write-char #\: stream))
	  (do ((i (+ null-position null-length) (1+ i)))
	      ((>= i 8))
	    (format stream ":~X" (addr-elt address start i))))))))
    
(define-named-integer neighbor-discovery-option-type (:prefix-constants nil)
  (1 source-link-layer-address)
  (2 target-link-layer-address)
  (3 prefix-information)
  (4 redirect-header)
  (5 mtu))

(defun pprint-neighbor-discovery-options (packet start end)
  (loop with offset = start
      when (> offset end)
      do (warn "Dangling bytes while pprinting neighbor-discovery options.")
      while (< offset end)
      do (format t "~&       Option: ~A"
		 (integer-name 'neighbor-discovery-option-type (aref packet offset) nil))
      do (case (integer-name 'neighbor-discovery-option-type (aref packet offset) nil)
	   ((source-link-layer-address target-link-layer-address)
	    (format t ": ~X:~X:~X:~X:~X:~X"
		    (aref packet (+ offset 2)) (aref packet (+ offset 3)) (aref packet (+ offset 4))
		    (aref packet (+ offset 5)) (aref packet (+ offset 6)) (aref packet (+ offset 7))))
	   (mtu
	    (format t "~D" (+ (* #x01000000 (aref packet (+ offset 4)))
			      (* #x00010000 (aref packet (+ offset 5)))
			      (* #x00000100 (aref packet (+ offset 6)))
			      (* #x00000001 (aref packet (+ offset 7)))))))
      do (assert (plusp (aref packet (1+ offset))))
      do (incf offset (* 8 (aref packet (1+ offset))))))

(defun link-local-address-by-mac (mac &key (packet (make-array 16 :element-type 'muerte::u8))
					   (packet-start 0) (start 0))
  "RFC 2464, sec. 5: Link-Local Addresses."
  (replace packet #(#xfe #x80 0 0 0 0 0 0) :start1 packet-start)
  (setf (aref packet (+ 8 packet-start)) (logxor 2 (aref mac (+ 0 start)))
	(aref packet (+ 9 packet-start)) (aref mac (+ 1 start))
	(aref packet (+ 10 packet-start)) (aref mac (+ 2 start))
	(aref packet (+ 11 packet-start)) #xff
	(aref packet (+ 12 packet-start)) #xfe
	(aref packet (+ 13 packet-start)) (aref mac (+ 3 start))
	(aref packet (+ 14 packet-start)) (aref mac (+ 4 start))
	(aref packet (+ 15 packet-start)) (aref mac (+ 5 start)))
  packet)

(defun packet-push (packet &rest values)
  (declare (dynamic-extent values))
  (dolist (value values)
    (vector-push value packet)))

(define-compiler-macro packet-push (packet-form &rest value-forms)
  (let ((packet-var (gensym "packet-push-packet")))
    `(let ((,packet-var ,packet-form))
       ,@(loop for value-form in value-forms
	     collecting `(vector-push ,value-form ,packet-var)))))

(defun push-sequence (packet sequence &optional (length (length sequence)) (sequence-start 0))
  (let ((i (fill-pointer packet)))
    (prog1
	(setf (fill-pointer packet) (+ i length))
      (replace packet sequence :start1 i :start2 sequence-start))))

(defun solicited-node-address (address &key (packet (make-array 16 :element-type 'muerte::u8))
					    (start 0) (packet-start 0))
  "RFC 2373, sec 2.7.1: Pre-Defined Multicast Addresses."
  (replace packet address :start1 packet-start :start2 start :end1 (+ packet-start 16))
  (replace packet #(#xff 2  0 0  0 0  0 0  0 0  0 1 #xff) :start1 packet-start)
  packet)

(defun mac-by-multicast-address (address &key (start 0) (packet (make-array 6)) (packet-start 0))
  "RFC 2464, sec. 7: Address Mapping -- Multicast."
  (assert (eq :multicast (address-prefix-type address :start start)) ()
    "Not a multicast address: ~S" (subseq address start (+ start 16)))
  (setf (aref packet (+ packet-start 0)) #x33
	(aref packet (+ packet-start 1)) #x33
	(aref packet (+ packet-start 2)) (aref address (+ start 12))
	(aref packet (+ packet-start 3)) (aref address (+ start 13))
	(aref packet (+ packet-start 4)) (aref address (+ start 14))
	(aref packet (+ packet-start 5)) (aref address (+ start 15)))
  packet)

(defun push-packet-header (packet &key ether-source ether-destination
				       ip-source ip-destination
				       (payload-length 0) (next-header 0)
				       (hop-limit 64) (traffic-class 0) (flow-label 0)
				       (ip-source-start 0)
				       (ip-destination-start 0))

  (push-sequence packet ether-destination 6)
  (push-sequence packet ether-source 6)
  (packet-push packet
	       (ldb (byte 8 8) +ether-type-ip6+)
	       (ldb (byte 8 0) +ether-type-ip6+)
	       (logior #x60 (ldb (byte 4 4) traffic-class))
	       (logior (ash (ldb (byte 4 0) traffic-class) 4)
		       (ldb (byte 4 16) flow-label))
	       (ldb (byte 8 8) flow-label)
	       (ldb (byte 8 0) flow-label)
	       (ldb (byte 8 8) payload-length)
	       (ldb (byte 8 0) payload-length)
	       next-header
	       hop-limit)
  (push-sequence packet ip-source 16 ip-source-start)
  (push-sequence packet ip-destination 16 ip-destination-start))

(defun push-icmp-header (packet type &optional (code 0) checksum)
  (vector-push type packet)
  (vector-push code packet)
  (cond
   (checksum
    (vector-push (ldb (byte 8 8) checksum) packet)
    (vector-push (ldb (byte 8 0) checksum) packet))
   (t (incf (fill-pointer packet) 2)))
  nil)

(defun push-icmp-neighbor-advertisment (packet target-address mac-address 
					router-p solicited-p override-p
					&key (target-address-start 0)
					     (mac-address-start 0))
  (push-icmp-header packet +icmp-header-type-neighbor-advertisment+)
  (vector-push (logior (if router-p #x80 0)
		       (if solicited-p #x40 0)
		       (if override-p #x20 0))
	       packet)
  (push-sequence packet #(0 0 0))
  (push-sequence packet target-address 16 target-address-start)
  (cond
   ((not mac-address)
    (fill-pointer packet))
   (t (vector-push +target-link-layer-address+ packet)
      (vector-push 1 packet)
      (push-sequence packet mac-address 6 mac-address-start))))

(defun find-icmp-nd-option (packet option start &optional end errorp)
  "RFC 2461, sec. 4.6: Option Formats.
Search for an option of type OPTION (an integer value), and return its offset if
found, or otherwise NIL.
The secondary return value is true if an error was discovered and the packet should be
discarded."
  (setf end (or end (length packet)))
  (loop with offset = start
      while (< offset end)
      do (let ((length (* 8 (aref packet (1+ offset)))))
	   (when (= 0 length)
	     (if errorp
		 (error "Neighbor discovery option with length zero.")
	       (return (values nil t))))
	   (when (= option (aref packet offset))
	     (return (values offset nil))))))
	     

(defun parse-icmp-neighbor-advertisment (packet &key (start 54)
						     (payload-length (packet-length packet)))
  "RFC 2461, sec. 4.4: Neighbor Advertisment Message Format.
Return the Router, Solicited, and Override flags,
and the offset of any target link-layer address."
  (let ((x (aref packet 4)))
    (values (logbitp 7 x)
	    (logbitp 6 x)
	    (logbitp 5 x)
	    (loop with offset = (+ start 24) and target-link-address-offset = nil
		while (< offset (+ start payload-length))
		do (let ((size (* 8 (aref packet (1+ offset)))))
		     (when (= 0 size)
		       (warn "Neighbor advertisment with zero length option.")
		       (return target-link-address-offset))
		     (named-integer-case neighbor-discovery-option-type (aref packet offset)
		       (target-link-layer-address
			(setf target-link-address-offset (+ 2 offset))))
		     (incf offset size))
		finally (return target-link-address-offset)))))

(defun parse-icmp-neighbor-solicitation (packet payload-length &key (start 54))
  "RFC 2461, sec. 4.3: Neighbor Solicitation Message Format.
Parse an ICMP neighbor solicitation packet.
Return as primary value the offset of the optional source link-layer address, if any."
  (loop with offset = (+ start 24) and source-link-address-offset = nil
      while (< offset (+ start payload-length))
      do (let ((size (* 8 (aref packet (1+ offset)))))
	   (when (= 0 size)
	     (warn "Neighbor solicitation with zero length option.")
	     (return source-link-address-offset))
	   (named-integer-case neighbor-discovery-option-type (aref packet offset)
	     (source-link-layer-address
	      (setf source-link-address-offset (+ 2 offset))))
	   (incf offset size))
      finally (return source-link-address-offset)))

(defun push-icmp-neighbor-solicitation (packet target-address
					&key (target-address-start 0)
					     source-mac-address (source-mac-address-start 0))
  "RFC 2461, sec. 4.3: Neighbor Solicitation Message Format."
  (push-icmp-header packet +icmp-header-type-neighbor-solicitation+)
  (push-sequence packet #(0 0 0 0))	; Reserved
  (push-sequence packet target-address 16 target-address-start)
  (cond
   ((not source-mac-address)
    (fill-pointer packet))
   (t (packet-push packet +source-link-layer-address+ 1)
      (push-sequence packet source-mac-address 6 source-mac-address-start))))


(defun transmit-neighbor-solicitation (ne2000 link-local-address packet address start)
  (let ((ip-dest (solicited-node-address address :start start)))
    (push-packet-header packet
			:ether-source (mac-address ne2000)
			:ether-destination (mac-by-multicast-address ip-dest)
			:ip-source link-local-address
			:ip-destination ip-dest
			:next-header +ip-header-type-icmp+
			:hop-limit 255)
    (push-icmp-neighbor-solicitation packet address
				     :target-address-start start
				     :source-mac-address (mac-address ne2000))
    (setf (packet-length packet) (- (length packet) 54)
	  (icmp-header-checksum packet) (icmp-checksum packet))
    (transmit ne2000 packet)))
  
(defvar *ne2000* nil)

(defun ip6-test (&optional (ne2000 
			    (or *ne2000*
				(setf *ne2000*
				  (some #'muerte.x86-pc.ne2k:ne2k-probe
					muerte.x86-pc.ne2k:*ne2k-probe-addresses*))
				(error "No ethernet device."))))
  (let* ((link-local-address (link-local-address-by-mac (mac-address ne2000)))
	 (solicited-node-address (solicited-node-address link-local-address))
	 (neighbor-cache (make-neighbor-cache)))
    (pushnew (mac-by-multicast-address solicited-node-address)
	     (accept-multicast-addresses ne2000)
	     :test #'equal)
    (format t "~&Link-local address: ~/ip6:pprint-ip6/~%" link-local-address)
    (format t "~&Solicited-node address: ~/ip6:pprint-ip6/~%" solicited-node-address)
    (setf (look-up-neighbor neighbor-cache link-local-address :start 0)
      (mac-address ne2000))
;     (format t "~&Local neighbor lookup: ~S.~%" (look-up-neighbor neighbor-cache link-local-address)) ;;comment this out
    (let ((packet-pool (make-array 16 :fill-pointer 0)))
      (flet ((get-packet (packet-pool)
	       (cond
		((plusp (length packet-pool))
		 (vector-pop packet-pool))
		(t (warn "Packet-pool was empty.")
		   (make-array +max-ethernet-frame-size+ :element-type 'muerte::u8 :fill-pointer 0))))
	     (free-packet (packet-pool p)
	       (setf (fill-pointer p) 0)
	       (vector-push p packet-pool)))
	(loop with timings = (make-array 20 :fill-pointer t)
	    with eval-buffer = (make-array 4096 :element-type 'character :fill-pointer 0)
	    with eval-prev-seqno = 0
	    with request-queue = nil
	    with offset = 54
	    finally (return (values))
	    until (muerte.x86-pc.keyboard:poll-char)
	    do (setf (fill-pointer timings) 0
		     (pit8253-timer-mode 0) +pit8253-mode-single-timeout+
		     (pit8253-timer-count 0) 0)
	    do (block process-request
		 (let ((request (or (pop request-queue)
				    (and (packet-available-p ne2000)
					 (receive ne2000 (get-packet packet-pool))))))
		   ;; (warn "request: ~Z" request)
		   (unless request
		     (return-from process-request))
		   (macrolet ((profile-point ()
				#+ignore `(vector-push (pit8253-timer-count 0) timings)))
		     (profile-point)
		     (when (and (= +ether-type-ip6+ (ether-type request))
				(= 6 (packet-version request))
				(or (not (mismatch request link-local-address
						   :start1 38 :end1 (+ 38 16)))
				    (not (mismatch request solicited-node-address
						   :start1 38 :end1 (+ 38 16)))))
		       #+ignore
		       (format t "~&IPv6: ~D bytes from ~22/ip6:pprint-ip6/ ~A~%"
			       (length request) request
			       (integer-name 'ip-header-type (packet-next-header request)))
		       (macrolet ((resolve-neighbor (address &optional (start 38))
				    `(or (look-up-neighbor neighbor-cache ,address :start ,start)
					 (progn
					   (transmit-neighbor-solicitation ne2000 link-local-address
									   (get-packet packet-pool)
									   ,address ,start)
					   (push request request-queue)
					   (return-from process-request)))))
			 (profile-point)
			 (named-integer-case ip-header-type
			     (packet-next-header request)
			   (icmp
			    (profile-point)
			    (when (= (icmp-header-checksum request offset)
				     (icmp-checksum request :icmp-header-start offset))
			      (named-integer-case icmp-header-type
				  (icmp-header-type request offset)
				(echo-request
				 (profile-point)
				 (replace request request :start2 22
					  :start1 38 :end1 (+ 38 16)) ; dest IP
				 (setf (ether-destination request) ; src MAC
				   (resolve-neighbor request))
				 (setf (subseq request 6) (mac-address ne2000))
				 (setf (subseq request 22) link-local-address)
				 (setf (icmp-header-type request) +icmp-header-type-echo-reply+)
				 (let ((old-checksum (icmp-header-checksum request)))
				   (setf (icmp-header-checksum request)
				     (if (< old-checksum #x100)
					 (+ old-checksum #xfeff)
				       (- old-checksum #x100))))
				 (profile-point)
				 (transmit ne2000 request))
				(neighbor-advertisment
				 (when (= 255 (packet-hop-limit request))
				   (multiple-value-bind (router-p solicited-p override-p)
				       (parse-icmp-neighbor-advertisment request :start offset)
				     (declare (ignore router-p solicited-p))
				     (when override-p
				       (let ((mac-offset (find-icmp-nd-option request
									      +target-link-layer-address+
									      (+ offset 24))))
					 (when mac-offset
					   (setf (look-up-neighbor neighbor-cache request
								   :start (+ offset 8)
								   :mac-start mac-offset)
					     request)))))))
				(neighbor-solicitation
				 (when (= 255 (packet-hop-limit request))
				   (let ((source-mac-offset
					  (+ 2 (find-icmp-nd-option request
								    +source-link-layer-address+
								    (+ offset 24)))))
				     (when source-mac-offset
				       (setf (look-up-neighbor neighbor-cache request :start 22
							       :mac-start source-mac-offset)
					 request)))
				   (let ((response (get-packet packet-pool)))
				     (push-packet-header
				      response
				      :ether-source (mac-address ne2000)
				      :ether-destination (resolve-neighbor request 22)
				      :ip-destination request
				      :ip-destination-start 22
				      :ip-source link-local-address
				      :next-header +ip-header-type-icmp+
				      :hop-limit 255)
				     (push-icmp-neighbor-advertisment
				      response link-local-address
				      (mac-address ne2000)
				      nil t t)
				     (setf (packet-length response) (- (length response) 54))
				     (setf (icmp-header-checksum response) (icmp-checksum response))
				     (transmit ne2000 response)
				     (free-packet packet-pool response)))))))
			   (udp
			    (when (= (udp-header-checksum request)
				     (udp-checksum request))
			      (when (= 1 (udp-header-destination request))
				(setf (muerte::vector-element-type request)
				  #.(bt:enum-value 'movitz::movitz-vector-element-type :character))
				(let (seqno last-seqno (poff (+ 8 offset)))
				  (multiple-value-setq (seqno poff)
				    (parse-integer request :start poff :junk-allowed t))
				  (multiple-value-setq (last-seqno poff)
				    (parse-integer request :start poff :junk-allowed t))
				  (incf poff) ; skip space
				  (when (= 0 seqno)
				    (setf eval-prev-seqno 0))
				  (cond
				   ((= seqno (incf eval-prev-seqno))
				    (let ((x (fill-pointer eval-buffer)))
				      (incf (fill-pointer eval-buffer) (- (length request) poff))
				      (replace eval-buffer request :start1 x :start2 poff))
				    (when (= seqno last-seqno)
				      (eval (let ((*read-base* 16))
					      (muerte:simple-read-from-string eval-buffer)))
				      (setf (fill-pointer eval-buffer) 0
					    eval-prev-seqno 0)))
				   (t (warn "Eval-UDP lost packet ~D." eval-prev-seqno)
				      (setf (fill-pointer eval-buffer) 0
					    eval-prev-seqno 0)))
				  (setf (muerte::vector-element-type request)
				    #.(bt:enum-value 'movitz::movitz-vector-element-type :u8))))
			      #+ignore
			      (warn "UDP src ~D, dst ~D, len ~D"
				    (udp-header-source request)
				    (udp-header-destination request)
				    (udp-header-length request)
				    (udp-header-checksum request)
				    (udp-checksum request))))
			   (t (warn "Unknown IPv6 header type: #x~X"
				    (packet-next-header request))))
			 (profile-point)
			 #+ignore
			 (dotimes (i (length timings))
			   (format t "~D: ~:D~%" i
				   (* 838 (- #x10000 (aref timings i)))))
			 (unless (zerop (length timings)) (terpri)))))
		   (free-packet packet-pool request))))))))

(defun ip6-free ()
  (when *ne2000*
    (free-io-space *ne2000*)
    (setf *ne2000* nil))
  (values))
