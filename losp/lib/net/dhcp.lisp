;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003, 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      dhcp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri May 13 23:24:01 2005
;;;;                
;;;; $Id: dhcp.lisp,v 1.4 2005/08/31 22:35:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/net/ip4)
(provide :lib/net/dhcp)

(in-package muerte.ip4)

#|

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
     +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
  0  |     op (1)    |   htype (1)   |   hlen (1)    |   hops (1)    |
     +---------------+---------------+---------------+---------------+
  1  |                            xid (4)                            |
     +-------------------------------+-------------------------------+
  2  |           secs (2)            |           flags (2)           |
     +-------------------------------+-------------------------------+
  3  |                          ciaddr  (4)                          |
     +---------------------------------------------------------------+
  4  |                          yiaddr  (4)                          |
     +---------------------------------------------------------------+
  5  |                          siaddr  (4)                          |
     +---------------------------------------------------------------+
  6  |                          giaddr  (4)                          |
     +---------------------------------------------------------------+
  7  |                                                               |
  8  |                          chaddr  (16)                         |
  9  |                                                               |
 10  |                                                               |
     +---------------------------------------------------------------+
 11  |                                                               |
     |                          sname   (64)                         |
     +---------------------------------------------------------------+
 26  |                                                               |
     |                          file    (128)                        |
     +---------------------------------------------------------------+
 58  |                          magic   (4)                          |
     +---------------------------------------------------------------+
 59  |                                                               |
     |                          options (variable)                   |
     +---------------------------------------------------------------+
|#

(defmacro with-dhcp-header ((dhcp packet &key start) &body body)
  (let* ((dhcp-ref (gensym "dhcp-ref-"))
	 (start-var (gensym "dhcp-start-"))
	 (packet-var (gensym "dhcp-packet-"))
	 (offset-var (gensym "dhcp-packet-start-")))
    `(let* ((,packet-var ,packet)
	    (,start-var ,(or start `(fill-pointer ,packet-var)))
	    (,offset-var (+ ,start-var (movitz-type-slot-offset 'movitz-basic-vector 'data))))
       (ensure-data-vector ,packet ,start-var 232)
       (macrolet ((,dhcp-ref (offset type)
		    `(memref ,',packet-var (+ ,',offset-var ,offset) :type ,type :endian :big))
		  (,dhcp (slot)
		    (ecase slot
		      ((:op :htype :hlen :hops)
		       `(,',dhcp-ref ,(position slot '(:op :htype :hlen :hops)) :unsigned-byte8))
		      (:xid
		       `(,',dhcp-ref 4 :unsigned-byte32))
		      (:secs
		       `(,',dhcp-ref 8 :unsigned-byte16))
		      (:flags
		       `(,',dhcp-ref 10 :unsigned-byte16))
		      ((:ciaddr :yiaddr :siaddr :giaddr)
		       `(,',dhcp-ref ,(+ 12 (* 4 (position slot '(:ciaddr :yiaddr :siaddr :giaddr))))
				     :unsigned-byte32))
		      (:chaddr
		       `(memrange ,',packet-var 0 (+ ,',offset-var 28) 16 :unsigned-byte8))
		      (:sname
		       `(memrange ,',packet-var 0 (+ ,',offset-var 44) 64 :character))
		      (:file
		       `(memrange ,',packet-var 0 (+ ,',offset-var 104) 128 :character))
		      (:magic
		       `(,',dhcp-ref 236 :unsigned-byte32))
		      (:end
		       `(+ 240 ,',start-var)))))
	 ,@body))))

(defconstant +bootrequest+ 1)
(defconstant +bootreply+ 2)
(defconstant +dhcp-magic+ #x63825363)

(defun vector-push-vector (vector packet)
  (loop for x across vector do (vector-push x packet))
  (fill-pointer packet))

(defun dhcp-push-options (packet &rest options)
  (declare (dynamic-extent options))
  (loop while options
      do (case (pop options)
	   (:lease-time
	    (vector-push 51 packet)
	    (vector-push 4 packet)
	    (let ((time (pop options)))
	      (check-type time (unsigned-byte 32))
	      (loop for b from 24 downto 0 by 8
		  do (vector-push (ldb (byte 8 b) time) packet))))
	   (:message-type
	    (vector-push 53 packet)
	    (vector-push 1 packet)
	    (vector-push (1+ (position (pop options)
				       '(:dhcpdiscover :dhcpoffer :dhcprequest :dhcpdecline
					 :dhcpack :dhcpnak :dhcprelease :dhcpinform)))
			 packet))
	   (:client-identifier
	    (vector-push 61 packet)
	    (let ((ci (pop options)))
	      (vector-push (length ci) packet)
	      (vector-push-vector ci packet)))
	   (:end
	    (vector-push 255 packet))
	   ))
  packet)

(defun parse-dhcp-options (packet)
  (loop for option = (vector-read packet)
      until (= option 255)
      unless (= 0 option)
      collect
	(case option
	  (1 (assert (= 4 (vector-read packet)) () "Wrong length for subnet-mask.")
	     (cons :subnet-mask
		   (subseq packet
			   (fill-pointer packet)
			   (incf (fill-pointer packet) 4))))
	  (3 (let ((length (vector-read packet)))
	       (cons :routers
		     (loop repeat (truncate length 4)
			 collect (subseq packet
					 (fill-pointer packet)
					 (incf (fill-pointer packet) 4))))))
	  (6 (let ((length (vector-read packet)))
	       (cons :dns-servers
		     (subseq packet
			     (fill-pointer packet)
			     (incf (fill-pointer packet) length)))))
	  (12 (let ((length (vector-read packet)))
		(cons :host-name
		      (map 'string #'code-char
			   (subseq packet
				   (fill-pointer packet)
				   (incf (fill-pointer packet) length))))))
	  (15 (let ((length (vector-read packet)))
		(cons :domain-name
		      (map 'string #'code-char
			   (subseq packet
				   (fill-pointer packet)
				   (incf (fill-pointer packet) length))))))
	  (28 (assert (= 4 (vector-read packet)) () "Wrong length for broadcast.")
	      (cons :broadcast
		    (subseq packet
			    (fill-pointer packet)
			    (incf (fill-pointer packet) 4))))
	  (42 (let ((length (vector-read packet)))
		(cons :ntp-servers
		      (subseq packet
			      (fill-pointer packet)
			      (incf (fill-pointer packet) length)))))
	  (44 (let ((length (vector-read packet)))
		(cons :wins-servers
		      (subseq packet
			      (fill-pointer packet)
			      (incf (fill-pointer packet) length)))))
	  (51 (assert (= 4 (vector-read packet)) () "Wrong length for lease-time.")
	      (cons :lease-time
		    (loop with time = 0 repeat 4
			do (setf time (+ (* 256 time) (vector-read packet)))
			finally (return time))))
	  (53 (assert (= 1 (vector-read packet)))
	      (cons :message-type
		    (let ((message-type (vector-read packet)))
		      (or (nth message-type
			       '(nil :dhcpdiscover :dhcpoffer :dhcprequest :dhcpdecline
				 :dhcpack :dhcpnak :dhcprelease :dhcpinform))
			  (error "Unknown DHCP message-type ~S." message-type)))))
	  (56 (let ((length (vector-read packet)))
		(cons :message
		      (map 'string #'code-char
			   (subseq packet
				   (fill-pointer packet)
				   (incf (fill-pointer packet) length))))))
	  (61 (let ((length (vector-read packet)))
		(cons :client-identifier
		      (subseq packet
			      (fill-pointer packet)
			      (incf (fill-pointer packet) length)))))
	  (t (let ((length (vector-read packet)))
	       (cons option
		     (when (> length 0)
		       (subseq packet
			       (fill-pointer packet)
			       (incf (fill-pointer packet) length)))))))))

(defun format-dhcp-request (nic &rest dhcp-options &key (xid 0)
							#+ignore (message-type :dhcpdiscover))
  (let ((packet (make-ethernet-packet)))
    (with-ether-header (ether packet)
      (setf (ether :source) (mac-address nic)
	    (ether :destination) +broadcast-address+
	    (ether :type) +ether-type-ip4+)
      (with-ip4-header (ip packet :start (ether :end))
	(with-udp-header (udp packet)
	  (with-dhcp-header (dhcp packet :start (udp :end))
	    (setf (ip :version) 4
		  (ip :protocol) 17
		  (ip :ihl) 5
		  (ip :destination) #xffffffff
		  (ip :source) 0
		  (udp :source-port) 0
		  (udp :destination-port) 67
		  (dhcp :op) +bootrequest+
		  (dhcp :htype) 1
		  (dhcp :hlen ) 6
		  (dhcp :hops) 0
		  (dhcp :secs) 0
		  (dhcp :xid) xid
		  (dhcp :chaddr) (mac-address nic)
		  (dhcp :magic) +dhcp-magic+)
	    (setf (fill-pointer packet) (dhcp :end))
	    (apply #'dhcp-push-options packet dhcp-options)
	    (dhcp-push-options packet
			       :client-identifier (mac-address nic)
			       :end)
	    (setf (ip :length) (- (fill-pointer packet) (ether :end))
		  (udp :length) (- (fill-pointer packet) (ip :end)))
	    (setf (ip :checksum) 0
		  (ip :checksum) (ip :compute-checksum))
	    (setf (udp :checksum) 0
		  (udp :checksum) (udp :compute-checksum ip))
	    packet))))))

(defun dhcp-request (&optional (nic (or *ip4-nic* (ip4-init))) &rest dhcp-options)
  (declare (dynamic-extent dhcp-options))
  (loop with packet = (make-ethernet-packet)
      with xid = (random 10000)
      repeat 5
      do (transmit nic (apply #'format-dhcp-request nic :xid xid dhcp-options))
	 (sleep 1/2)
      when (loop while (receive nic packet)
	       thereis (with-ether-header (ether packet)
			 (with-ip4-header (ip packet :start (ether :end))
			   (when (and (= 4 (ip :version))
				      (= 17 (ip :protocol)))
			     (warn "Seeing UDP ~/ip4:pprint-ip4/ from ~/ip4:pprint-ip4/."
				   (ip4-address (ip :destination))
				   (ip4-address (ip :source)))
			     (with-udp-header (udp packet)
			       (when (= 68 (udp :destination-port))
				 (setf (fill-pointer packet)
				   (udp :end))
				 (with-dhcp-header (dhcp packet)
				   (and (= xid (dhcp :xid))
					(= +dhcp-magic+ (dhcp :magic))))))))))
      return packet))

(defun dhcp-init ()
  (let ((packet (dhcp-request)))
    (if (not packet)
	(warn "DHCP lookup failed.")
      (with-dhcp-header (dhcp packet)
	(setf (fill-pointer packet) (dhcp :end))
	(let ((options (parse-dhcp-options packet)))
	  (setf *ip4-ip* (ip4-address (dhcp :yiaddr))
		*ip4-router* (first (cdr (assoc :routers options))))
	  (format *terminal-io* "Setting IP ~/ip4:pprint-ip4/ ~@[~A~]~@[.~A~] router ~/ip4:pprint-ip4/."
		  *ip4-ip*
		  (cdr (assoc :host-name options))
		  (cdr (assoc :domain-name options))
		  *ip4-router*)))))
  (values))
