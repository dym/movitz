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
;;;; $Id: scavenge.lisp,v 1.36 2004/11/26 14:59:31 ffjeld Exp $
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

(defvar *scan*)				; debugging
(defvar *scan-last*)			; debugging
(defvar *map-header-vals-verbose* nil)

(defun map-lisp-vals (function start-location end-location)
  (with-funcallable (do-map function)
    (loop for location from start-location below end-location
	as object = (memref location 0)
	do (when (typep object 'pointer)
	     (let ((new-object (do-map object)))
	       (unless (eq object new-object)
		 (setf (memref location 0) new-object)))))))

(defun map-header-vals (function start-location end-location)
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
    (do ((verbose *map-header-vals-verbose*)
	 (*scan-last* nil)		; Last scanned object, for debugging.
	 (scan start-location (1+ scan)))
	((>= scan end-location))
      (with-simple-restart (continue-map-header-vals
			    "Continue map-header-vals at location ~S." (1+ scan))
	(let ((x (memref scan 0 :type :unsigned-byte16))
	      (x2 (memref scan 1 :type :unsigned-byte16)))
	  (when verbose
	    (format *terminal-io* " [at ~S: ~S]" scan x))
	  (cond
	   ((let ((tag (ldb (byte 3 0) x)))
	      (or (= tag #.(movitz:tag :null))
		  (= tag #.(movitz:tag :even-fixnum))
		  (= tag #.(movitz:tag :odd-fixnum))
		  (scavenge-typep x :character))))
	   ((or (and (= 0 x2) (= 2 x))
		(and (= #xffff x2) (= #xfffe x))
		(and (= #x7fff x2) (= #xffff x))))
	   ((scavenge-typep x :illegal)
	    (error "Illegal word ~S at ~S." x scan))
	   ((scavenge-typep x :bignum)
	    (assert (evenp scan) ()
	      "Scanned bignum-header ~S at odd location #x~X." x scan)
	    ;; Just skip the bigits
	    (let* ((bigits (memref scan 0 :index 1 :type :unsigned-byte14))
		   (delta (logior bigits 1)))
	      (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	      (incf scan delta)))
	   ((scavenge-typep x :defstruct)
	    (assert (evenp scan) ()
	      "Scanned struct-header ~S at odd location #x~X." x scan)
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other))))
	   ((scavenge-typep x :funobj)
	    (assert (evenp scan) ()
	      "Scanned funobj-header ~S at odd location #x~X." 
	      (memref scan 0 :type :unsigned-byte32) scan)
	    (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	    ;; Process code-vector pointers specially..
	    (let* ((funobj (%word-offset scan #.(movitz:tag :other)))
		   (code-vector (funobj-code-vector funobj))
		   (num-jumpers (funobj-num-jumpers funobj)))
	      (check-type code-vector code-vector)
	      (map-header-vals function (+ scan 5) (+ scan 7)) ; scan funobj's lambda-list and name
	      (let ((new-code-vector (funcall function code-vector scan)))
		(check-type new-code-vector code-vector)
		(unless (eq code-vector new-code-vector)
		  (error "Code-vector migration is not implemented.")
		  (setf (memref scan 0 :index -1) (%word-offset new-code-vector 2))
		  ;; Do more stuff here to update code-vectors and jumpers
		  ))
	      (incf scan (+ 7 num-jumpers)))) ; Don't scan the jumpers.
	   ((scavenge-typep x :infant-object)
	    (assert (evenp scan) ()
	      "Scanned infant ~S at odd location #x~X." x scan)
	    (error "Scanning an infant object ~Z at ~S (end ~S)." x scan end-location))
	   ((or (scavenge-wide-typep x :basic-vector
				     #.(bt:enum-value 'movitz:movitz-vector-element-type :u8))
		(scavenge-wide-typep x :basic-vector
				     #.(bt:enum-value 'movitz:movitz-vector-element-type :character))
		(scavenge-wide-typep x :basic-vector
				     #.(bt:enum-value 'movitz:movitz-vector-element-type :code)))
	    (assert (evenp scan) ()
	      "Scanned u8-vector-header ~S at odd location #x~X." x scan)
	    (let ((len (memref scan 0 :index 1 :type :lisp)))
	      (check-type len positive-fixnum)
	      (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	      (incf scan (1+ (* 2 (truncate (+ 7 len) 8))))))
	   ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u16))
	    (assert (evenp scan) ()
	      "Scanned u16-vector-header ~S at odd location #x~X." x scan)
	    (let ((len (memref scan 0 :index 1)))
	      (check-type len positive-fixnum)
	      (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	      (incf scan (1+ (* 2 (truncate (+ 3 len) 4))))))
	   ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u32))
	    (assert (evenp scan) ()
	      "Scanned u32-vector-header ~S at odd location #x~X." x scan)
	    (let ((len (memref scan 4)))
	      (assert (typep len 'positive-fixnum) ()
		"Scanned basic-vector at ~S with illegal length ~S." scan len)
	      (setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	      (incf scan (1+ (logand (1+ len) -2)))))
	   ((scavenge-typep x :basic-vector)
	    (if (scavenge-wide-typep x :basic-vector
				     #.(bt:enum-value 'movitz:movitz-vector-element-type :any-t))
		(setf *scan-last* (%word-offset scan #.(movitz:tag :other)))
	      (error "Scanned unknown basic-vector-header ~S at location #x~X." x scan)))
	   ((scavenge-typep x :old-vector)
	    (error "Scanned old-vector ~Z at address #x~X." x scan))
	   ((eq x 3)
	    (setf *scan-last* scan)
	    (incf scan)
	    (let ((delta (memref scan 0)))
	      (check-type delta positive-fixnum)
	      ;; (warn "at ~S skipping ~S to ~S." scan delta (+ scan delta))
	      (incf scan delta)))
	   (t ;; (typep x 'pointer)
	    (let* ((old (memref scan 0))
		   (new (funcall function old scan)))
	      (when verbose
		(format *terminal-io* " [~Z => ~Z]" old new))
	      (unless (eq old new)
		(setf (memref scan 0) new)))))))))
  (values))

(defun map-stack-vector (function stack start-frame &optional (map-region #'map-header-vals))
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (with-funcallable (map-region)
    (loop with next-frame with next-nether-frame
	for nether-frame = start-frame then (or next-nether-frame frame)
	and frame = (stack-frame-uplink stack start-frame) then (or next-frame
								    (stack-frame-uplink stack frame))
	while (plusp frame)
	do (setf next-frame nil next-nether-frame nil)
	do (flet ((scavenge-funobj-code-vector (funobj)
		    "Funobj 0 is assumed to be the DIT code-vector."
		    (if (eq 0 funobj)
			(symbol-value 'default-interrupt-trampoline)
		      (funobj-code-vector funobj))))
	     (let ((funobj (funcall function (stack-frame-funobj stack frame) frame)))
	       ;; If nether-frame is a DIT-frame, there are 4 more words to be skipped.
	       (when (eq 0 (stack-frame-ref stack nether-frame -1))
		 (incf nether-frame 4))
	       (typecase funobj
		 ((or function null)
		  (assert (= 0 (funobj-frame-num-unboxed funobj)))
		  (map-region function (+ nether-frame 2) frame))
		 ((eql 0)		; A dit interrupt-frame?
		  (let* ((dit-frame frame)
			 (casf-frame (dit-frame-casf stack dit-frame)))
		    ;; 1. Scavenge the dit-frame
		    (cond
		     ((let ((atomically (dit-frame-ref stack dit-frame :atomically-continuation
						       :unsigned-byte32)))
			(and (not (= 0 atomically))
			     (= 0 (ldb (byte 2 0) atomically))))
		      ;; Interrupt occurred inside an (non-pf) atomically, so none of the
		      ;; registers are active.
		      (map-region function (+ nether-frame 2)
				  (+ dit-frame 1 (dit-frame-index :tail-marker))))
		     ((logbitp 10 (dit-frame-ref stack dit-frame :eflags :unsigned-byte32))
		      ;; DF flag was 1, so EAX and EDX are not GC roots.
		      #+ignore (warn "Interrupt in uncommon mode at ~S"
				     (dit-frame-ref stack dit-frame :eip :unsigned-byte32))
		      (map-region function ; Assume nothing in the dit-frame above the location ..
				  (+ nether-frame 2) ; ..of EDX holds pointers.
				  (+ dit-frame (dit-frame-index :edx))))
		     (t #+ignore (warn "Interrupt in COMMON mode!")
			(map-region function ; Assume nothing in the dit-frame above the location ..
				    (+ nether-frame 2) ; ..of ECX holds pointers.
				    (+ dit-frame (dit-frame-index :ecx)))))
		    ;; 2. Pop to (dit-)frame's CASF
		    (setf nether-frame dit-frame
			  frame (dit-frame-casf stack frame))
		    (let ((casf-funobj (funcall function (stack-frame-funobj stack frame) frame))
			  (interrupted-ebp (dit-frame-ref stack dit-frame :ebp))
			  (interrupted-esp (dit-frame-esp stack dit-frame)))
		      (cond
		       #+ignore
		       ((eq nil casf-funobj)
			(warn "Scanning interrupt in PF: ~S"
			      (dit-frame-ref stack dit-frame :eip :unsigned-byte32)))
		       ((or (eq 0 casf-funobj)
			    (typep casf-funobj 'function))
			(let ((casf-code-vector (scavenge-funobj-code-vector casf-funobj)))
			  ;; 3. Scavenge the interrupted frame, according to one of i. ii. or iii.
			  (cond
			   ((< interrupted-ebp interrupted-esp)
			    (cond
			     ((location-in-object-p casf-code-vector
						    (dit-frame-ref stack dit-frame :eip :location))
			      (warn "DIT at throw situation, in target EIP=~S"
				    (dit-frame-ref stack dit-frame :eip :unsigned-byte32))
			      (map-region function interrupted-esp frame))
			     ((location-in-object-p (scavenge-funobj-code-vector (dit-frame-ref stack
												dit-frame
												:scratch1))
						    (dit-frame-ref stack dit-frame :eip :location))
			      (warn "DIT at throw situation, in thrower EIP=~S"
				    (dit-frame-ref stack dit-frame :eip :unsigned-byte32))
			      (map-region function interrupted-esp frame))
			     (t (error "DIT with EBP<ESP, EBP=~S, ESP=~S"
				       interrupted-ebp
				       interrupted-esp))))
			   ((location-in-object-p casf-code-vector
						  (dit-frame-ref stack dit-frame :eip :location))
			    (cond
			     ((let ((x0-tag (ldb (byte 3 0)
						 (memref interrupted-esp 0 :type :unsigned-byte8))))
				(and (member x0-tag '(1 5 6 7))
				     (location-in-object-p casf-code-vector
							   (memref interrupted-esp 0 :type :location))))
			      ;; When code-vector migration is implemented...
			      (warn "Scanning at ~S X0 call ~S in ~S."
				    (dit-frame-ref stack dit-frame :eip :unsigned-byte32)
				    (memref interrupted-esp 0 :type :unsigned-byte32)
				    (funobj-name casf-funobj))
			      (map-region function (+ interrupted-esp 1) frame)
			      (when (eq 0 (stack-frame-ref stack frame -1))
				(break "X1 call in DIT-frame."))
			      (setf next-frame frame
				    next-nether-frame (+ interrupted-esp 1 -2)))
			     ((let ((x1-tag (ldb (byte 3 0)
						 (memref interrupted-esp 4 :type :unsigned-byte8))))
				(and (member x1-tag '(1 5 6 7))
				     (location-in-object-p casf-code-vector
							   (memref interrupted-esp 4 :type :location))))
			      ;; When code-vector migration is implemented...
			      (warn "Scanning at ~S X1 call ~S in ~S."
				    (dit-frame-ref stack dit-frame :eip :unsigned-byte32)
				    (memref interrupted-esp 4 :type :unsigned-byte32)
				    (funobj-name casf-funobj))
			      (when (eq 0 (stack-frame-ref stack frame -1))
				(break "X1 call in DIT-frame."))
			      (map-region function (+ interrupted-esp 2) frame)
			      (setf next-frame frame
				    next-nether-frame (+ interrupted-esp 2 -2)))
			     (t ;; Situation i. Nothing special on stack, scavenge frame normally.
			      ;; (map-region function interrupted-esp frame)
			      (setf next-frame frame
				    next-nether-frame (- interrupted-esp 2))
			      )))
			   ((eq casf-frame (memref interrupted-esp 0 :type :location))
			    ;; Situation ii. esp(0)=CASF, esp(1)=code-vector
			    (assert (location-in-object-p casf-code-vector
							  (memref interrupted-esp 4 :type :location))

				() "Stack discipline situation ii. invariant broken. CASF=#x~X, ESP=~S, EBP=~S"
				casf-frame interrupted-esp interrupted-ebp)
			    (map-region function (+ interrupted-esp 2) frame)
			    (setf next-frame frame
				  next-nether-frame (+ interrupted-esp 2 -2)))
			   (t ;; Situation iii. esp(0)=code-vector.
			    (assert (location-in-object-p casf-code-vector
							  (memref interrupted-esp 0 :type :location))
				() "Stack discipline situation iii. invariant broken. CASF=#x~X"
				casf-frame)
			    (map-region function (+ interrupted-esp 1) frame)
			    (setf next-frame frame
				  next-nether-frame (+ interrupted-esp 1 -2))))))
		       (t (error "DIT-frame interrupted unknown CASF funobj: ~S" casf-funobj))))))
		 (t (error "Don't know how to scavenge across frame ~S of kind ~S." frame funobj)))))))
  (values))

