;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      scavenge.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Mar 29 14:54:08 2004
;;;;                
;;;; $Id: scavenge.lisp,v 1.11 2004/06/16 07:42:55 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package #:muerte)

(provide :muerte/scavenge)

;; In this file and others, a "location" is a fixnum word used as a
;; memory pointer with 32-bit resolution. The location 0 is address
;; #x0, the location 1 is address #x4, 2 is #x8, 100 is #x190, 262144
;; is the 1MB address, and so on.
;;
;; Such "locations" can of course only be used in certain
;; circumstances, i.e. when you know there is no outside GC
;; etc. involved.


(defun map-heap-words (function start-location end-location)
  "Map function over each potential pointer word between
start-location and end-location."
  (macrolet ((scavenge-typep (x primary)
	       (let ((code (movitz:tag primary)))
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,x)
		    (:cmpb ,code :al))))
	     (scavenge-wide-typep (x primary secondary)
	       (let ((code (dpb secondary
				(byte 8 8)
				(movitz:tag primary))))
		 `(with-inline-assembly (:returns :boolean-zf=1)
		    (:compile-form (:result-mode :eax) ,x)
		    (:cmpw ,code :ax))))
	     (word-upper16 (x)
	       "Consider x as a 32-bit integer, and return the upper 16 bits (as a fixnum)."
	       `(with-inline-assembly (:returns :eax)
		  (:compile-form (:result-mode :eax) ,x)
		  (:andl #xffff0000 :eax)
		  (:shrl ,(- 16 movitz:+movitz-fixnum-shift+) :eax))))
    (do ((scan start-location (1+ scan)))
	((>= scan end-location))
      (let (;; (*i* i)
	    (x (memref scan 0 0 :lisp)))
	;; (declare (special *i*))
	(cond
	 ((typep x '(or null fixnum character)))
	 ((scavenge-typep x :illegal)
	  (error "Illegal word ~Z at ~S." x scan))
	 ((scavenge-typep x :bignum)
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  ;; Just skip the bigits
	  (let* ((bigits (word-upper16 x))
		 (delta (1+ (logand bigits -2))))
	    (incf scan delta)))
	 ((scavenge-typep x :funobj)
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  ;; Process code-vector pointer specially..
	  (let* ((funobj (%word-offset scan #.(movitz:tag :other)))
		 (code-vector (funobj-code-vector funobj))
		 (num-jumpers (funobj-num-jumpers funobj)))
	    (check-type code-vector vector-u8)
	    (map-heap-words function (+ scan 5) (+ scan 7)) ; scan funobj's lambda-list and name
	    (let ((new-code-vector (funcall function code-vector scan)))
	      (check-type new-code-vector vector-u8)
	      (unless (eq code-vector new-code-vector)
		(error "Code-vector migration is not implemented.")
		(setf (memref scan 0 -1 :lisp) (%word-offset new-code-vector 2))
		;; Do more stuff here to update code-vectors and jumpers
		))
	    (incf scan (+ 7 num-jumpers)))) ; Don't scan the jumpers.
	 ((scavenge-typep x :infant-object)
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  (error "Scanning an infant object ~Z at ~S (end ~S)." x scan end-location))
	 ((or (scavenge-wide-typep x :vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :u8))
	      (scavenge-wide-typep x :vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :character)))
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  (let ((len (memref scan (word-upper16 x) 0 :unsigned-byte16)))
	    (incf scan (1+ (* 2 (truncate (+ 7 len) 8))))))
	 ((scavenge-wide-typep x :vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u16))
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  (let ((len (memref scan (word-upper16 x) 0 :unsigned-byte16)))
	    (incf scan (1+ (* 2 (truncate (+ 3 len) 4))))))
	 ((scavenge-wide-typep x :vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u32))
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd address #x~X." x scan)
	  (let ((len (memref scan (word-upper16 x) 0 :unsigned-byte16)))
	    (incf scan (1+ (logand (1+ len) -2)))))
	 ((eq x (fixnum-word 3))
	  (incf scan)
	  (incf scan (memref scan 0 0 :lisp)))
	 ((typep x 'pointer)
	  (let ((new (funcall function x scan)))
	    (unless (eq new x)
	      (setf (memref scan 0 0 :lisp) new))))))))
  (values))

(defun map-stack-words (function start-stack-frame)
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (loop for nether-frame = start-stack-frame then frame
      and frame = (stack-frame-uplink start-stack-frame) then (stack-frame-uplink frame)
      while (plusp frame)
      do (let ((funobj (stack-frame-funobj frame t)))
	   #+ignore
	   (format t "~&fill ~S frame for ~S"
		   (aref (%run-time-context-slot 'nursery-space) 0)
		   funobj)
	   (typecase funobj
	     (function
	      (assert (= 0 (funobj-frame-num-unboxed funobj)))
	      (map-heap-words function (+ nether-frame 2) frame))
	     ((eql 0)
	      ;; 1. Scavenge the interrupt-frame
	      (map-heap-words function
			      (+ nether-frame 2)
			      (+ frame (interrupt-frame-index :ecx)))
	      (let* ((interrupt-frame frame)
		     (interrupted-eip-loc
		      (interrupt-frame-ref :eip :signed-byte30+2 0 interrupt-frame)))
		;; 2. Pop to interrupted frame
		(setf nether-frame frame
		      frame (stack-frame-uplink frame))
		(let ((interrupted-funobj (stack-frame-funobj frame))
		      (interrupted-esp (+ interrupt-frame 6)))
		  (assert (typep interrupted-funobj 'function) ()
		    "Interrupted frame was not a normal function: ~S"
		    interrupted-funobj)
		  ;; 3. Scavenge the interrupted frame, skipping EFLAGS etc.
		  (if (location-in-object-p (funobj-code-vector interrupted-funobj)
					    interrupted-eip-loc)
		      ;; The simple case: The interruptee matches interrupted EIP
		      (map-heap-words function interrupted-esp frame)
		    (let ((primitive-function-vector
			   (stack-frame-primitive-funcall interrupted-funobj
							  interrupted-esp
							  interrupted-eip-loc)))
		      (if primitive-function-vector
			  ;; Next simplest case: The interruptee was in a primitive-function,
			  ;; with the return-address at top of stack.
			  (map-heap-words function (1+ interrupted-esp) frame)
			(error "Don't know how to scavenge across interrupt frame at ~S."
			       interrupt-frame)))))))
	     (t (error "Don't know how to scavenge across a frame of kind ~S." funobj)))))
  (values))

(defparameter *primitive-funcall-patterns*
    '((:or
       (#xff #x57 (:function-offset :signed8)) ; 
       (#xff #x97 (:function-offset :signed32))))) ;

(defun stack-frame-primitive-funcall (funobj stack-location eip-location)
  "Is stack-frame in a primitive-function?
If so, return the primitive-function's code-vector."
  (let ((return-address (memref stack-location 0 0 :unsigned-byte32))
	(code-vector (funobj-code-vector funobj)))
    (multiple-value-bind (return-location return-delta)
	(truncate return-address #.movitz:+movitz-fixnum-factor+)
      (if (not (location-in-object-p code-vector return-location))
	  nil				; A PF must have return-address on top of stack.
	(dotimes (offset 5 (warn "mismatch in ~S at ~D from #x~X in ~Z."
				 funobj
				 (+ (* (- return-location
					  (object-location code-vector))
				       #.movitz:+movitz-fixnum-factor+)
				    return-delta
				    -3 -8)
				 return-address code-vector))
	  (multiple-value-bind (success-p type code ip)
	      (match-code-pattern *primitive-funcall-patterns*
				  code-vector (+ (* (- return-location
						       (object-location code-vector))
						    #.movitz:+movitz-fixnum-factor+)
						 return-delta
						 -3 -8 (- offset))
				  :function-offset)
	    (when success-p
	      (return
		(let* ((offset (case type
				 (:signed8
				  (if (not (logbitp 7 code)) code (- code 256)))
				 (:signed32
				  ;; We must read the unsigned-byte32 that starts at ip
				  (let ((x (logior (aref code-vector (- ip 1))
						       (* (aref code-vector (+ 0 ip)) #x100)
						       (* (aref code-vector (+ 1 ip)) #x10000)
						       (* (aref code-vector (+ 2 ip)) #x1000000))))
				    (if (not (logbitp 7 (aref code-vector (+ ip 2))))
					x
				      (break "Negative 32-bit offset."))))
				 (t (break "Match fail: vec: ~Z, ip: ~D"
					   code-vector (+ (* (- return-location
								(object-location code-vector))
							     #.movitz:+movitz-fixnum-factor+)
							  return-delta
							  -3 -8)))))
		       (primitive-function (%word-offset (%run-time-context-ref offset) -2)))
		  (check-type primitive-function vector-u8)
		  (if (not (location-in-object-p primitive-function eip-location))
		      nil
		    primitive-function))))))))))
