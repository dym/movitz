;; note, this file is in a very "incomplete" state

(require :lib/net/ethernet)
(provide :lib/net/tftp)

(in-package muerte.ip4)

(defpackage muerte.ip4
  (:export #:format-tftp-request))

;;;taken from tftp.lisp, I think I'll use this function as-is
;; maybe format-tftp-header/packet is better
(defun format-tftp-request (packet start opcode &rest strings) ;; start is the start of the data
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

(defun net-loop-breaker ()
  "When to break a networking loop"
  (eql #\space (muerte.x86-pc.keyboard:poll-char)))

(defun tftp-send-ack (block-number ip &optional (port 69))
  (let ((ip (ip4-address ip))
	(start (+ 14 20 8))
	(packet (make-ethernet-packet)))
    (format-tftp-request packet start 4 block-number)
    (format-udp-header packet :destination ip :destination-port port)
    (format-ethernet-packet packet (mac-address *ip4-nic*) (polling-arp ip) +ether-type-ip4+)
    ;;s/polling-arp/mac???
    (loop
     (when (net-loop-breaker) ;; why is this not working? in receive it is
       (break "TFTP/ETHERNET"))
     (sleep 3)
     (format t "sending ~%") ;; never gets printed
     (transmit *ip4-nic* packet)))) ;; should put a timeout-loop

#+ignore
(defun tftp-send-ack-test ()
  (tftp-send-ack 0 :69.31.43.106))


(defun tftp-receive-ack () ;; have to add a timeout, or finish if we get data or error back. The same for the previous function
  "returns the block-number if ack got sent false oterwise"
  (ip4-init) ;; to get removed later, as to get an ack we need to have made a rq before,
  ;;and thus initialized ip
  ;;--- also i need to extract the source port, and maybe also return it or set a variable ---;;
  (loop with ip-start = 14 ;; perhaps i need just a tftp-start variable in the fun-definition
	with udp-start = (+ ip-start 20)
	with tftp-start = (+ udp-start 8)
	for ack = nil then (receive *ip4-nic* ack)
	until
	(with-simple-restart (continue "Continue")
			     (when (net-loop-breaker) ;; here it DOES work
			       (break "TFTP/ETHERNET"))
			     (when (and ack
					(eq +ether-type-ip4+ (ether-type ack))
					(not (mismatch *ip4-ip* (ip-header-destination ack)))
					(= +ip-protocol-udp+ (ip-protocol ack))
					(= (ip4-ref ack tftp-start 0 :unsigned-byte16) 4))
			       (return (ip4-ref ack tftp-start 1 :unsigned-byte16))))))

(defun tftp-send-data (ip source-port destination-port 
			  data-vector &key (data-length (length data-vector)))
  "splitting the data into packets and transmitting them until all the data is sent"
  ;; this function needs more testing, it causes errors
  (ip4-init) ;;to be removed
  (let ((start 42)
	(ip (ip4-address ip)) ;maybe remove this
	(packet (make-ethernet-packet)))
    (loop for block-number upfrom 1
	  for i from 0 to data-length by 512
	  do (format-tftp-request packet start 3 block-number)
	  (loop for j upfrom (fill-pointer packet)
		as k upfrom i below (min data-length (+ i 512))
		do (setf (ip4-ref packet 0 j :unsigned-byte8)
			 (ip4-ref data-vector 0 k :unsigned-byte8))
		finally
		(setf (fill-pointer packet) j))
	  (format-udp-header packet :source ip :source-port port)
	  (format-ethernet-packet packet (mac-address *ip4-nic*) (polling-arp ip) 
				  +ether-type-ip4+) ;;s/polling-arp/mac ??
	  ;;here i should also check if i get the ack's using tftp-receive-ack
	  ;;and increasing block-numbers - also add the breaking function again
	  (transmit *ip4-nic* packet))))

(defun tftp-receive-data ()
)

(defun tftp-send-error ()
)

(defun tftp-send-wrq ()
)

(defun tftp-send-rrq ()
)

;; the "main" functions
(defun tftp-put ()
)

(defun tftp-get ()
)