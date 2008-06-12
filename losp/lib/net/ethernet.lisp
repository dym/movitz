;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      ethernet.lisp
;;;; Description:   IEEE 802.3 Ethernet definitions and abstract device.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 17 15:25:31 2002
;;;;                
;;;; $Id: ethernet.lisp,v 1.12 2008-06-12 12:54:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/named-integers)

(provide :lib/net/ethernet :load-priority 0)

(defpackage muerte.ethernet 
  (:use muerte.cl muerte muerte.lib)
  (:export #:make-ethernet-packet
	   #:ether-destination
	   #:ether-source
	   #:ether-type
	   #:ethernet-device
	   #:transmit
	   #:receive
	   #:packet-error
	   #:packet
	   #:packet-available-p
	   #:mac-address
	   #:accept-broadcasts-p
	   #:accept-multicast-addresses
	   #:promiscuous-p
	   #:pprint-mac
	   #:ether-mac-vendor
	   #:format-ethernet-packet
	   #:ether-802.3-p
	   #:ether-802.3-llc-type
	   #:ether-802.3-llc-dsap
	   #:ether-802.3-llc-ssap
	   #:ether-802.3-snap-p
	   #:ether-802.3-snap-type
	   #:+source-mac+
	   #:+destination-mac+
	   #:+max-ethernet-frame-size+
	   #:+min-ethernet-frame-size+
	   #:+broadcast-address+

	   #:+ether-type-ip4+
	   #:+ether-type-chaosnet+
	   #:+ether-type-arp+
	   #:+ether-type-symbolics+
	   #:+ether-type-rarp+
	   #:+ether-type-snmp+
	   #:+ether-type-ip6+
	   #:+ether-type-ppp+
	   #:+ether-type-mswin-heartbeat+
	   #:+ether-type-loopback+

	   #:with-ether-header
	   ))
	   
(in-package muerte.ethernet)

(defconstant +max-ethernet-frame-size+ 1514) ;  sans preamble and postable.
(defconstant +min-ethernet-frame-size+ 60) ; except crc.
(defconstant +broadcast-address+ #(#xff #xff #xff #xff #xff #xff))

(defconstant +source-mac+ 6)
(defconstant +destination-mac+ 0)

(define-named-integer ether-header (:only-constants t :export-constants t)
  (0 destination)
  (6 source)
  (12 type))

;;; Packet accessors

(defmacro with-ether-header ((ether packet &key (start 0)) &body body)
  (let* ((packet-var (gensym "ether-packet-"))
	 (offset-var (gensym "ether-packet-offset-"))
	 (start-var (gensym "ether-packet-start-")))
    `(let* ((,start-var ,start)
	    (,packet-var (ensure-data-vector ,packet ,start-var 14))
	    (,offset-var (+ ,start-var (movitz-type-slot-offset 'movitz-basic-vector 'data))))
       (declare (ignorable ,start-var ,packet-var ,offset-var))
       (macrolet ((,ether (slot)
		    (ecase slot
		      (:source
		       `(memrange ,',packet-var ,',offset-var 6 6 :unsigned-byte8))
		      (:destination
		       `(memrange ,',packet-var ,',offset-var 0 6 :unsigned-byte8))
		      (:type
		       `(memref ,',packet-var (+ ,',offset-var 12) :type :unsigned-byte16 :endian :big))
		      (:end `(+ ,',start-var 14)))))
	 ,@body))))
       

(defmacro packet-ref (packet start offset type)
  `(memref ,packet (+ (muerte:movitz-type-slot-offset 'movitz-basic-vector 'data)
		      ,start ,offset)
	   :endian :big
	   :type ,type))

(defun ether-destination (packet &optional (start 0))
  (subseq packet start (+ start 6)))

(defun (setf ether-destination) (destination packet &optional (start 0) &key (destination-start 0))
  (replace packet destination :start1 start :end1 (+ start 6) :start2 destination-start)
  destination)

(defun ether-source (packet &optional (start 0))
  (subseq packet (+ start 6) (+ start 12)))

(defun (setf ether-source) (source packet &optional (start 0) &key (source-start 0))
  (replace packet source :start1 (+ start 6) :end1 (+ start 12) :start2 source-start)
  source)

(defun ether-type (packet &optional (start 0))
  (packet-ref packet start 12 :unsigned-byte16))

(defun (setf ether-type) (type packet &optional (start 0))
  (setf (packet-ref packet start 12 :unsigned-byte16)
    type))

(defun ether-802.3-p (packet &optional (start 0))
  "Is the packet a 802.3 type packet?"
  (<= (ether-type packet start) #x5dc))

(defun ether-802.3-llc-type (packet &optional (start 0))
  (packet-ref packet start 16 :unsigned-byte8))

(defun ether-802.3-llc-dsap (packet &optional (start 0))
  (packet-ref packet start 14 :unsigned-byte8))

(defun ether-802.3-llc-ssap (packet &optional (start 0))
  (packet-ref packet start 15 :unsigned-byte8))

(defun ether-802.3-snap-p (packet &optional (start 0))
  (and (ether-802.3-p packet)
       (= #xAA (ether-802.3-llc-ssap packet start))))

(defun ether-802.3-snap-type (packet &optional (start 0))
  (packet-ref packet start 20 :unsigned-byte16))

;;;

(defconstant +ether-type-ip4+ #x0800)
(defconstant +ether-type-chaosnet+ #x0804)
(defconstant +ether-type-arp+ #x0806)
(defconstant +ether-type-symbolics+ #x081c)
(defconstant +ether-type-rarp+ #x0835)
(defconstant +ether-type-snmp+ #x814c)
(defconstant +ether-type-ip6+ #x86dd)
(defconstant +ether-type-ppp+ #x880b)
;; http://www.microsoft.com/technet/treeview/default.asp?
;;        url=/TechNet/prodtechnol/windows2000serv/deploy/confeat/nlbovw.asp
(defconstant +ether-type-mswin-heartbeat+ #x886f)
(defconstant +ether-type-loopback+ #x9000)

;;;


(defun format-ethernet-packet (packet source destination type &key (start 0) (source-start 0)
								   (destination-start 0))
  (setf (ether-source packet start :source-start source-start) source
	(ether-destination packet start :destination-start destination-start) destination
	(ether-type packet start) type)
  packet)

(deftype mac-address ()
  '(vector (unsigned-byte 8) 6))

(defclass ethernet-device ()
  ((mac-address
    :initarg :mac-address
    :accessor mac-address)
   (accept-broadcasts-p
    :documentation "Should this device accept incoming broadcast packets?"
    :initarg :accept-broadcasts-p
    :initform t
    :accessor accept-broadcasts-p)
   (accept-multicast-addresses
    :documentation "A list of incoming multicast addresses that should be accepted, or t for all addresses."
    :initarg :accept-multicast-addresses
    :initform nil
    :accessor accept-multicast-addresses)
   (promiscuous-p
    :initarg :promiscuous-p
    :initform nil
    :accessor promiscuous-p)))

(defmethod print-object ((x ethernet-device) s)
  (print-unreadable-object (x s :type t :identity t)
    (when (slot-boundp x 'mac-address)
      (pprint-mac s (mac-address x)))))


(defgeneric transmit (device packet &optional start end))
(defgeneric receive (device &optional packet start))
(defgeneric packet-available-p (device))

(define-condition packet-error (error)
  ((packet
    :initarg :packet
    :reader packet)))

;;;

(defparameter *ether-vendors*
    '((Cisco
       #x000C #x0142 #x0143 #x0163 #x0164 #x0196 #x0197 #x01C7 #x01C9 #x0216
       #x0217 #x024A #x024B #x027D #x027E #x02B9 #x02BA #x02FC #x02FD #x0331
       #x0332 #x036B #x036C #x039F #x03A0 #x03E3 #x03E4 #x03FD #x03FE #x0427
       #x0428 #x044D #x044E #x046D #x046E #x049A #x049B #x04C0 #x04C1 #x04DD
       #x04DE #x0500 #x0501 #x0531 #x0532 #x055E #x055F #x0573 #x0574 #x059A
       #x059B #x05DC #x05DD #x0628 #x062A #x0652 #x0653 #x067C #x06C1 #x06D6
       #x06D7 #x070D #x070E #x074F #x0750 #x0784 #x0785 #x07B3 #x07B4 #x07EB
       #x07EC #x0820 #x0821 #x087C #x087D #x08A3 #x08A4 #x08C2 #x08E2 #x08E3
       #x0911 #x0912 #x0943 #x0944 #x097B #x097C #x09B6 #x09B7 #x09E8 #x09E9
       #x0A41 #x0A42 #x0A8A #x0A8B #x0AB7 #x0AB8 #x0AF3 #x0AF4 #x0B45 #x0B46
       #x0B5F #x0B60 #x0BBE #x0BBF #x0BFC #x0BFD #x0C30 #x0C31 #x0C85 #x0C86
       #x0CCE #x0CCF #x0D28 #x0D29 #x1007 #x100B #x100D #x1011 #x1014 #x101F
       #x1029 #x102F #x1054 #x1079 #x107B #x10A6 #x10F6 #x10FF #x3019 #x3024
       #x3040 #x3071 #x3078 #x307B #x3080 #x3085 #x3094 #x3096 #x30A3 #x30B6
       #x30F2 #x400B #x500B #x500F #x5014 #x502A #x503E #x5050 #x5053 #x5054
       #x5073 #x5080 #x50A2 #x50A7 #x50BD #x50D1 #x50E2 #x50F0 #x6009 #x602F
       #x603E #x6047 #x605C #x6070 #x6083 #x900C #x9021 #x902B #x905F #x906D
       #x906F #x9086 #x9092 #x90A6 #x90AB #x90B1 #x90BF #x90D9 #x90F2 #xB04A
       #xB064 #xB08E #xB0C2 #xD006 #xD058 #xD063 #xD079 #xD090 #xD097 #xD0BA
       #xD0BB #xD0BC #xD0C0 #xD0D3 #xD0E4 #xD0FF #xE014 #xE01E #xE034 #xE04F
       #xE08F #xE0A3 #xE0B0 #xE0F7 #xE0F9 #xE0FE)
      (3com
       #x0102 #x0103 #x029C #x0A5E #x104B #x105A #x20AF #x301E #x5004 #x5099
       #x50DA #x6008 #x608C #x6097 #x9004 #xA024 #xD096 #x2608C #x2C08C #x8004E)
      (Hewlett-Packard
       #x1e6 #x1e7 #x4ea #x883 #xa57 #x1083 #x306e #x30c1 #x60b0 #x80a0 #x80009)
      (Xerox #x0 #x1 #x2 #x3 #x4 #x5 #x6 #x7 #x8 #x9 #xAA #x80037 #x80072)
      (Agere #x22d #x53d)
      (Aironet #x4096)
      (Ani #x4005)
      (Apple #x393 #x502 #xa27 #xa95 #x3065 #x50e4 #xa040 #x80007)
      (Cameo #x40f4)
      (Dell #x65b #x874 #xb0d0 #xc04f)
      (Delta-networks #x30ab)
      (D-Link #x55d #x50ba #x80c8)
      (Intel
       #x2B3 #x347 #x423 #x7E9 #xCF1 #x207B #x9027 #xA0C9 #xAA00 #xAA01 #xAA02 #xD0B7)
      (Linksys #x45a #x625 #xc41)
      (Lucent #x586 #x306d #x601d #x60d2 #xd077)
      (Xircom #x53c #x10a4 #x80c7))
  "http://standards.ieee.org/regauth/oui/oui.txt")

(defun ether-mac-vendor (address &optional (start 0))
  (let ((vendor-code (logior (ash (aref address (+ start 0)) 16)
			     (ash (aref address (+ start 1)) 8)
			     (aref address (+ start 2)))))
    (loop for v in *ether-vendors*
	when (member vendor-code (cdr v))
	do (return (car v)))))

(defun pprint-mac (stream address &optional colon at (start (if at 6 0)))
  "Pretty-print an ethernet mac-address, like 00:40:05:18:66:d8.
The at modifier offsets the packet 6 bytes. The colon modifier
attempts to decode the vendor part of the address using *ether-vendors*."
  (when colon
    (let ((vendor (ether-mac-vendor address start)))
      (when vendor
	(format stream "~A:" vendor))))
  (loop for i from (1+ start) below (+ start 6)
      initially (format stream "~2,'0X" (aref address start))
      do (format stream ":~2,'0X" (aref address i)))
  (values))

						    
(defun make-ethernet-packet (&optional (size +max-ethernet-frame-size+))
  (make-array size
	      :element-type '(unsigned-byte 8)
	      :fill-pointer t))
