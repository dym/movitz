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
;;;; $Id: scavenge.lisp,v 1.27 2004/08/23 13:58:34 ffjeld Exp $
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
		 `(= ,code (ldb (byte 8 0) ,x))))
	     (scavenge-wide-typep (x primary secondary)
	       (let ((code (dpb secondary
				(byte 8 8)
				(movitz:tag primary))))
		 `(= ,code ,x))))
    (do ((verbose *map-heap-words-verbose*)
	 (*scan-last* nil)		; Last scanned object, for debugging.
	 (scan start-location (1+ scan)))
	((>= scan end-location))
      (declare (special *scan-last*))
      (let ((*scan* scan)
	    (x (memref scan 0 0 :unsigned-byte16)))
	(declare (special *scan*))
	(when verbose
	  (format *terminal-io* " [at ~S: ~S]" scan x))
	(cond
	 ((let ((tag (ldb (byte 3 0) x)))
	    (or (= tag #.(movitz:tag :null))
		(= tag #.(movitz:tag :fixnum))
		(scavenge-typep x :character))))
	 ((scavenge-typep x :illegal)
	  (error "Illegal word ~S at ~S." x scan))
	 ((scavenge-typep x :bignum)
	  (assert (evenp scan) ()
	    "Scanned ~S at odd location #x~X." x scan)
	  ;; Just skip the bigits
	  (let* ((bigits (memref scan 0 1 :unsigned-byte14))
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
	  (error "Scanned old-vector ~Z at address #x~X." x scan))
	 ((eq x 3)
	  (incf scan)
	  (let ((delta (memref scan 0 0 :lisp)))
	    (check-type delta positive-fixnum)
	    ;; (warn "at ~S skipping ~S to ~S." scan delta (+ scan delta))
	    (incf scan delta)))
	 (t ;; (typep x 'pointer)
	  (let* ((old (memref scan 0 0 :lisp))
		 (new (funcall function old scan)))
	    (when verbose
	      (format *terminal-io* " [~Z => ~Z]" old new))
	    (unless (eq old new)
	      (setf (memref scan 0 0 :lisp) new))))))))
  (values))

(defun map-stack-words (function stack start-frame)
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (loop for nether-frame = start-frame then frame
      and frame = (stack-frame-uplink stack start-frame) then (stack-frame-uplink stack frame)
      while (plusp frame)
      do (let ((funobj (funcall function (stack-frame-funobj stack frame) nil)))
	   (typecase funobj
	     (function
	      (assert (= 0 (funobj-frame-num-unboxed funobj)))
	      (map-heap-words function (+ nether-frame 2) frame))
	     ((eql 0)			; An dit interrupt-frame?
	      (let* ((dit-frame frame)
		     (casf-frame (dit-frame-casf dit-frame)))
		;; 1. Scavenge the dit-frame
		(cond
		 ((logbitp 10 (dit-frame-ref :eflags :unsigned-byte32 0 dit-frame))
		  ;; DF flag was 1, so EAX and EDX are not GC roots.
		  #+ignore
		  (warn "Interrupt in uncommon mode at ~S"
			(dit-frame-ref :eip :unsigned-byte32 0 dit-frame))
		  (map-heap-words function ; Assume nothing in the dit-frame above the location ..
				  (+ nether-frame 2) ; ..of EBX holds pointers.
				  (+ frame (dit-frame-index :ebx))))
		 (t #+ignore
		    (warn "Interrupt in COMMON mode!")
		    (map-heap-words function ; Assume nothing in the dit-frame above the location ..
				    (+ nether-frame 2) ; ..of ECX holds pointers.
				    (+ frame (dit-frame-index :ecx)))))
		;; 2. Pop to (dit-)frame's CASF
		(setf nether-frame frame
		      frame (dit-frame-casf frame))
		(let ((casf-funobj (funcall function (stack-frame-funobj stack frame) nil))
		      (interrupted-esp (dit-frame-esp dit-frame)))
		  (cond
		   ((eq 0 casf-funobj)
		    (warn "Interrupt (presumably)   in interrupt trampoline."))
		   (t (assert (typep casf-funobj 'function) ()
			"Interrupted CASF frame was not a normal function: ~S"
			casf-funobj)
		      (let ((casf-code-vector (funobj-code-vector casf-funobj)))
			;; 3. Scavenge the interrupted frame, according to one of i. ii. or iii.
			(cond
			 ((location-in-object-p casf-code-vector
						(dit-frame-ref :eip :location 0 dit-frame))
			  ;; Situation i. Nothing special on stack, scavenge frame normally.
			  (map-heap-words function interrupted-esp frame))
			 ((eq casf-frame (memref interrupted-esp 0 0 :location))
			  ;; Situation ii. esp(0)=CASF, esp(1)=code-vector
			  (assert (location-in-object-p casf-code-vector
							(memref interrupted-esp 0 1 :location))
			      () "Stack discipline situation ii. invariant broken. CASF=#x~X"
			      casf-frame)
			  (map-heap-words function (+ interrupted-esp 2) frame))
			 (t ;; Situation iii. esp(0)=code-vector.
			  (assert (location-in-object-p casf-code-vector
							(memref interrupted-esp 0 0 :location))
			      () "Stack discipline situation iii. invariant broken. CASF=#x~X"
			      casf-frame)
			  (map-heap-words function (+ interrupted-esp 1) frame)))))))))
	     (t (error "Don't know how to scavenge across frame ~S of kind ~S." frame funobj)))))
  (values))

;;;(defparameter *primitive-funcall-patterns*
;;;    '((:or
;;;       (#xff #x57 (:function-offset :signed8)) ; 
;;;       (#xff #x97 (:function-offset :signed32))))) ;
;;;
;;;(defun stack-frame-primitive-funcall (funobj stack-location eip-location)
;;;  "Is stack-frame in a primitive-function?
;;;If so, return the primitive-function's code-vector."
;;;  (declare (ignore eip-location))
;;;  ;; XXXX Really we should make comparisons against :call-local-pf
;;;  ;;      such that we find the active set of local-pf's from the stack-location!
;;;  (let ((return-address (memref stack-location 0 0 :unsigned-byte32))
;;;	(code-vector (funobj-code-vector funobj)))
;;;    (multiple-value-bind (return-location return-delta)
;;;	(truncate return-address #.movitz:+movitz-fixnum-factor+)
;;;      (if (not (location-in-object-p code-vector return-location))
;;;	  nil				; A PF must have return-address on top of stack.
;;;	(dotimes (offset 5 (warn "mismatch in ~S at ~D from #x~X in ~Z."
;;;				 funobj
;;;				 (+ (* (- return-location
;;;					  (object-location code-vector))
;;;				       #.movitz:+movitz-fixnum-factor+)
;;;				    return-delta
;;;				    -3 -8)
;;;				 return-address code-vector))
;;;	  (multiple-value-bind (success-p type code ip)
;;;	      (match-code-pattern *primitive-funcall-patterns*
;;;				  code-vector (+ (* (- return-location
;;;						       (object-location code-vector))
;;;						    #.movitz:+movitz-fixnum-factor+)
;;;						 return-delta
;;;						 -3 -8 (- offset))
;;;				  :function-offset)
;;;	    (when success-p
;;;	      (return
;;;		(let* ((offset (case type
;;;				 (:signed8
;;;				  (if (not (logbitp 7 code)) code (- code 256)))
;;;				 (:signed32
;;;				  ;; We must read the unsigned-byte32 that starts at ip
;;;				  (let ((x (logior (aref code-vector (- ip 1))
;;;						   (* (aref code-vector (+ 0 ip)) #x100)
;;;						   (* (aref code-vector (+ 1 ip)) #x10000)
;;;						   (* (aref code-vector (+ 2 ip)) #x1000000))))
;;;				    (if (not (logbitp 7 (aref code-vector (+ ip 2))))
;;;					x
;;;				      (break "Negative 32-bit offset."))))
;;;				 (t (break "Match fail: vec: ~Z, ip: ~D"
;;;					   code-vector (+ (* (- return-location
;;;								(object-location code-vector))
;;;							     #.movitz:+movitz-fixnum-factor+)
;;;							  return-delta
;;;							  -3 -8)))))
;;;		       (primitive-function (%word-offset (%run-time-context-ref offset) -2)))
;;;		  (if (not (typep primitive-function 'code-vector))
;;;		      nil
;;;		    primitive-function))))))))))
;;;		  (check-type primitive-function code-vector)
;;;		  (if (not (location-in-object-p primitive-function eip-location))
;;;		      nil
;;;		    primitive-function))))))))))
