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
;;;; $Id: scavenge.lisp,v 1.25 2004/07/23 15:27:43 ffjeld Exp $
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

(defvar *scan*)
(defvar *map-heap-words-verbose* nil)

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
	     (word-bigits (x)
	       "If x is a bignum header word, return the number of bigits."
	       `(with-inline-assembly (:returns :eax)
		  (:compile-form (:result-mode :eax) ,x)
		  (:shrl 16 :eax)
		  (:testb ,movitz:+movitz-fixnum-zmask+ :al)
		  (:jnz '(:sub-program () (:int 63))))))
    (do ((verbose *map-heap-words-verbose*)
	 (*scan-last* nil)		; Last scanned object, for debugging.
	 (scan start-location (1+ scan)))
	((>= scan end-location))
      (declare (special *scan-last*))
      (let ((*scan* scan)
	    (x (memref scan 0 0 :lisp)))
	(declare (special *scan*))
	(when verbose
	  (format *terminal-io* "~&MHW scanning at ~S: ~Z" scan x))
	(cond
	 ((typep x '(or null fixnum character)))
	 ((scavenge-typep x :illegal)
	  (error "Illegal word ~Z at ~S." x scan))
	 ((scavenge-typep x :bignum)
	  (assert (evenp scan) ()
	    "Scanned ~Z at odd location #x~X." x scan)
	  ;; Just skip the bigits
	  (let* ((bigits (word-bigits x))
		 (delta (logior bigits 1)))
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	    (incf scan delta)))
	 ((scavenge-typep x :funobj)
	  (assert (evenp scan) ()
	    "Scanned ~Z at odd location #x~X." x scan)
	  (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	  ;; Process code-vector pointers specially..
	  (let* ((funobj (%word-offset scan #.(movitz:tag :other)))
		 (code-vector (funobj-code-vector funobj))
		 (num-jumpers (funobj-num-jumpers funobj)))
	    (check-type code-vector code-vector)
	    (map-heap-words function (+ scan 5) (+ scan 7)) ; scan funobj's lambda-list and name
	    (let ((new-code-vector (funcall function code-vector scan)))
	      (check-type new-code-vector code-vector)
	      (unless (eq code-vector new-code-vector)
		(error "Code-vector migration is not implemented.")
		(setf (memref scan 0 -1 :lisp) (%word-offset new-code-vector 2))
		;; Do more stuff here to update code-vectors and jumpers
		))
	    (incf scan (+ 7 num-jumpers)))) ; Don't scan the jumpers.
	 ((scavenge-typep x :infant-object)
	  (assert (evenp scan) ()
	    "Scanned #x~Z at odd location #x~X." x scan)
	  (error "Scanning an infant object ~Z at ~S (end ~S)." x scan end-location))
	 ((or (scavenge-wide-typep x :basic-vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :u8))
	      (scavenge-wide-typep x :basic-vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :character))
	      (scavenge-wide-typep x :basic-vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :code)))
	  (assert (evenp scan) ()
	    "Scanned ~Z at odd location #x~X." x scan)
	  (let ((len (memref scan 0 1 :lisp)))
	    (check-type len positive-fixnum)
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	    (incf scan (1+ (* 2 (truncate (+ 7 len) 8))))))
	 ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u16))
	  (assert (evenp scan) ()
	    "Scanned ~Z at odd location #x~X." x scan)
	  (let ((len (memref scan 0 1 :lisp)))
	    (check-type len positive-fixnum)
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	    (incf scan (1+ (* 2 (truncate (+ 3 len) 4))))))
	 ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u32))
	  (assert (evenp scan) ()
	    "Scanned ~Z at odd location #x~X." x scan)
	  (let ((len (memref scan 0 1 :lisp)))
	    (check-type len positive-fixnum)
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	    (incf scan (1+ (logand (1+ len) -2)))))
	 ((and (scavenge-typep x :basic-vector)
	       (not (scavenge-wide-typep x :basic-vector
					 #.(bt:enum-value 'movitz:movitz-vector-element-type :any-t))))
	  (error "Scanned unknown basic-vector #x~Z at address #x~X." x scan))
	 ((scavenge-typep x :old-vector)
	  (error "Scanned old-vector #x~Z at address #x~X." x scan))
	 ((eq x (%lispval-object 3))
	  (incf scan)
	  (let ((delta (memref scan 0 0 :lisp)))
	    (check-type delta positive-fixnum)
	    ;; (warn "at ~S skipping ~S to ~S." scan delta (+ scan delta))
	    (incf scan delta)))
	 ((typep x 'pointer)
	  (let ((new (funcall function x scan)))
	    (when verbose
	      (format *terminal-io* " [~Z => ~Z]" x new))
	    (unless (eq new x)
	      (setf (memref scan 0 0 :lisp) new))))))))
  (values))

(defun map-stack-words (function start-stack-frame)
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (loop for nether-frame = start-stack-frame then frame
      and frame = (stack-frame-uplink start-stack-frame) then (stack-frame-uplink frame)
      while (plusp frame)
      do (let ((funobj (funcall function (stack-frame-funobj frame t) nil)))
	   (typecase funobj
	     (function
	      (assert (= 0 (funobj-frame-num-unboxed funobj)))
	      (map-heap-words function (+ nether-frame 2) frame))
	     ((eql 0)			; An interrupt-frame?
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
		(let ((interrupted-funobj (funcall function (stack-frame-funobj frame t) nil))
		      (interrupted-esp (+ interrupt-frame 6)))
		  (assert (typep interrupted-funobj 'function) ()
		    "Interrupted frame was not a normal function: ~S"
		    interrupted-funobj)
		  ;; 3. Scavenge the interrupted frame, skipping EFLAGS etc.
		  (if (location-in-object-p (funobj-code-vector interrupted-funobj)
					    interrupted-eip-loc)
		      ;; The simple case: The interruptee matches interrupted EIP
		      (map-heap-words function interrupted-esp frame)
		    (let ((primitive-function
			   (stack-frame-primitive-funcall interrupted-funobj
							  interrupted-esp
							  interrupted-eip-loc)))
		      (if (not primitive-function)
			  (error "Don't know how to scavenge across PF interrupt frame at ~S."
				 interrupt-frame)
			(let ((forwarded-pf (funcall function primitive-function nil)))
			  ;; Next simplest case: The interruptee was in a primitive-function,
			  ;; with the return-address at top of stack.
			  (unless (eq primitive-function forwarded-pf)
			    ;; The PF's vector has migrated.
			    (let* ((interrupted-eip
				    (interrupt-frame-ref :eip :unsigned-byte32 0 :unsigned-byte32))
				   (offset (- interrupted-eip (%object-lispval primitive-function))))
			      (break "Active PF moved. PF: ~Z, fwPF: ~Z, offset: ~D, PFlen ~D."
				     primitive-function
				     forwarded-pf
				     offset
				     (+ 8 (length forwarded-pf)))
			      (setf (memref interrupted-esp 0 0 :unsigned-byte32)
				(+ offset (%object-lispval forwarded-pf)))))
			  (map-heap-words function (1+ interrupted-esp) frame))))))))
	     (t (error "Don't know how to scavenge across frame ~S of kind ~S." frame funobj)))))
  (values))

(defparameter *primitive-funcall-patterns*
    '((:or
       (#xff #x57 (:function-offset :signed8)) ; 
       (#xff #x97 (:function-offset :signed32))))) ;

(defun stack-frame-primitive-funcall (funobj stack-location eip-location)
  "Is stack-frame in a primitive-function?
If so, return the primitive-function's code-vector."
  (declare (ignore eip-location))
  ;; XXXX Really we should make comparisons against :call-local-pf
  ;;      such that we find the active set of local-pf's from the stack-location!
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
		  (if (not (typep primitive-function 'code-vector))
		      nil
		    primitive-function))))))))))
;;;		  (check-type primitive-function code-vector)
;;;		  (if (not (location-in-object-p primitive-function eip-location))
;;;		      nil
;;;		    primitive-function))))))))))
