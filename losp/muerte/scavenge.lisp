;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      scavenge.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Mar 29 14:54:08 2004
;;;;                
;;;; $Id: scavenge.lisp,v 1.40 2005/01/25 13:56:18 ffjeld Exp $
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
	     (let ((new-object (do-map object location)))
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
	   ((and (eq x 3) (eq x2 0))
	    (setf *scan-last* scan)
	    (incf scan)
	    (let ((delta (memref scan 0)))
	      (check-type delta positive-fixnum)
	      ;; (warn "at ~S skipping ~S to ~S." scan delta (+ scan delta))
	      (incf scan delta)))
	   (t ;; (typep x 'pointer)
	    (let ((old (memref scan 0)))
	      (unless (eq old (load-global-constant new-unbound-value))
		(let ((new (funcall function old scan)))
		  (when verbose
		    (format *terminal-io* " [~Z => ~Z]" old new))
		  (unless (eq old new)
		    (setf (memref scan 0) new)))))))))))
  (values))

(defun map-stack-vector (function stack start-frame &optional (map-region #'map-header-vals))
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (assert (typep (stack-frame-funobj stack start-frame) 'function) (start-frame)
    "Cannot start map-stack-vector at a non-normal frame.")
  (assert (eq nil stack))
  (map-stack function
	     (stack-frame-uplink stack start-frame)
	     (+ start-frame 2)
	     (+ start-frame 1)
	     map-region))

;;;(defun map-code-vector-slot (function stack slot casf-funobj)
;;;  (let ((casf-code-vector (if (eq 0 casf-funobj)
;;;			      (symbol-value 'default-interrupt-trampoline)
;;;			    (funobj-code-vector casf-funobj)))
;;;	(eip-location (stack-frame-ref stack slot 0 :location)))
;;;    (cond
;;;     ((location-in-object-p casf-code-vector eip-location)
;;;      (let ((new (funcall function casf-code-vector nil)))
;;;	(when (not (eq new casf-code-vector))
;;;	  ;; Perform some pointer arithmetics..
;;;	  (let ((offset (- (stack-frame-ref stack slot 0 :unsigned-byte32)
;;;			   (%object-lispval casf-code-vector))))
;;;	    (break "Code-vector for ~S moved, offset is ~D." casf-code-vector offset))))))))

(defun scavenge-find-code-vector (location casf-funobj esi &optional searchp)
  (flet ((match-funobj (funobj location)
	   (cond
	    ((let ((x (funobj-code-vector casf-funobj)))
	       (and (location-in-object-p x location) x)))
	    ((let ((x (funobj-code-vector%1op casf-funobj)))
	       (and (typep x 'vector)
		    (location-in-object-p x location)
		    x)))
	    ((let ((x (funobj-code-vector%2op casf-funobj)))
	       (and (typep x 'vector)
		    (location-in-object-p x location)
		    x)))
	    ((let ((x (funobj-code-vector%3op casf-funobj)))
	       (and (typep x 'vector)
		    (location-in-object-p x location)
		    x))))))
    (cond
     ((eq 0 casf-funobj)
      (let ((dit-code-vector (symbol-value 'default-interrupt-trampoline)))
	(if (location-in-object-p dit-code-vector location)
	    dit-code-vector
	  (break "DIT returns outside DIT??"))))
     ((and (typep esi 'function)
	   (match-funobj esi location)))
     ((match-funobj casf-funobj location))
     ((not (typep casf-funobj 'function))
      (break "Unknown funobj/frame-type: ~S" casf-funobj))
     ((when searchp
	(%find-code-vector location)))
     (t (error "Unable to decode EIP #x~X funobj ~S." location casf-funobj)))))

(defun map-stack-value (function value frame)
  (if (not (typep value 'pointer))
      value
    (funcall function value frame)))

(defun map-stack (function frame frame-bottom eip-index map-region)
  (with-funcallable (map-region)
    (loop
      ;; for frame = frame then (stack-frame-uplink frame)
      ;; as frame-end = frame-end then frame
	while (not (eq 0 frame))
	do (map-lisp-vals function (1- frame) frame)
	   (let ((frame-funobj (map-stack-value function (stack-frame-funobj nil frame) frame)))
	     (cond
	      ((eq 0 frame-funobj)
	       (return (map-stack-dit function frame frame-bottom eip-index map-region)))
	      ((not (typep frame-funobj 'function))
	       (error "Unknown stack-frame funobj ~S at ~S" frame-funobj frame))
	      (t (let* ((old-code-vector
			 (scavenge-find-code-vector (stack-frame-ref nil eip-index 0 :location)
						    frame-funobj nil nil)))
		   (map-stack-instruction-pointer function eip-index old-code-vector))
		 (let ((raw-locals (funobj-frame-raw-locals frame-funobj)))
		   (if (= 0 raw-locals)
		       (map-region function frame-bottom frame)
		     (progn
		      (break "~D raw-locals for ~S?" raw-locals frame-funobj)
		      (map-region function (1- frame) frame)
		      (map-region function frame-bottom (- frame 1 raw-locals))))
		   (setf eip-index (+ frame 1)
			 frame-bottom (+ frame 2)
			 frame (stack-frame-uplink nil frame)))))))))

(defun test-stack ()
  (let ((z (current-stack-frame)))
    (map-stack (lambda (x y)
		 (format t "~&[~S]: ~S" y x)
		 x)
	       (stack-frame-uplink nil z) (+ z 2) (+ z 1)
	       #'map-header-vals)))

(defun map-stack-dit (function dit-frame frame-bottom eip-index map-region)
  (with-funcallable (map-region)
    (let* ((atomically
	    (dit-frame-ref nil dit-frame :atomically-continuation :unsigned-byte32))
	   (secondary-register-mode-p
	    (logbitp 10 (dit-frame-ref nil dit-frame :eflags :unsigned-byte32)))
	   (casf-frame
	    (dit-frame-casf nil dit-frame))
	   (casf-funobj (map-stack-value function (stack-frame-funobj nil casf-frame) casf-frame))
	   (casf-code-vector (map-stack-value function
					      (case casf-funobj
						(0 (symbol-value 'default-interrupt-trampoline))
						(t (funobj-code-vector casf-funobj)))
					      casf-frame)))
      ;; 1. Scavenge the dit-frame
      (cond
       ((and (not (= 0 atomically))
	     (= 0 (ldb (byte 2 0) atomically)))
	;; Interrupt occurred inside an (non-pf) atomically, so none of the
	;; GC-root registers are active.
	(setf (dit-frame-ref nil dit-frame :eax) nil
	      (dit-frame-ref nil dit-frame :ebx) nil
	      (dit-frame-ref nil dit-frame :edx) nil
	      (dit-frame-ref nil dit-frame :esi) nil)
	(map-region function frame-bottom (+ dit-frame 1 (dit-frame-index :scratch1))))
       (secondary-register-mode-p
	;; EBX is also active
	(map-region function frame-bottom (+ dit-frame 1 (dit-frame-index :ebx))))
       (t ;; EDX and EAX too.
	(map-region function frame-bottom (+ dit-frame 1 (dit-frame-index :eax)))))
      ;; The DIT's return-address
      (let* ((interrupted-esi (dit-frame-ref nil dit-frame :esi))
	     (next-frame-bottom (+ dit-frame 1 (dit-frame-index :eflags)))
	     (next-eip-index (+ dit-frame (dit-frame-index :eip)))
	     (old-code-vector
	      (scavenge-find-code-vector (stack-frame-ref nil eip-index 0 :location)
					 0 interrupted-esi
					 nil))
	     (new-code-vector (map-stack-instruction-pointer function eip-index old-code-vector)))
	;;
	(multiple-value-bind (x0-location x0-tag)
	    (stack-frame-ref nil next-frame-bottom 0 :signed-byte30+2)
	  ;; (warn "X0: ~S ~S" x0-location x0-tag)
	  (cond
	   ((and (or (eq x0-tag 1)	; 1 or 5?
		     (eq x0-tag 3)	; 3 or 7?
		     (and (oddp x0-location) (eq x0-tag 2))) ; 6?
		 (location-in-object-p casf-code-vector x0-location))
	    (let* ((old-x0-code-vector
		    (scavenge-find-code-vector (stack-frame-ref nil next-eip-index 0 :location)
					       casf-funobj interrupted-esi t)))
	      (map-stack-instruction-pointer function next-eip-index old-x0-code-vector))
	    (setf next-eip-index next-frame-bottom
		  next-frame-bottom (1+ next-frame-bottom)))
	   (t (multiple-value-bind (x1-location x1-tag)
		  (stack-frame-ref nil next-frame-bottom 1 :signed-byte30+2)
		(when (and (or (eq x1-tag 1) ; 1 or 5?
			       (eq x1-tag 3) ; 3 or 7?
			       (and (oddp x1-location) (eq x1-tag 2))) ; 6?
			   (location-in-object-p casf-code-vector x1-location))
		  (warn "X1: ~S ~S" x1-location x1-tag)
		  (let* ((old-x1-code-vector
			  (scavenge-find-code-vector (stack-frame-ref nil next-eip-index 0 :location)
						     casf-funobj interrupted-esi t)))
		    (map-stack-instruction-pointer function next-eip-index old-x1-code-vector))
		  (setf next-eip-index (+ 1 next-frame-bottom)
			next-frame-bottom (+ 2 next-frame-bottom)))))))
	;; proceed
	(map-stack function casf-frame next-frame-bottom next-eip-index map-region)))))

(defun map-stack-instruction-pointer (function index old-code-vector)
  "Update the (raw) instruction-pointer in stack at index,
assuming the pointer refers to old-code-vector."
  (assert (location-in-object-p old-code-vector (stack-frame-ref nil index 0 :location)))
  (let ((new-code-vector (funcall function old-code-vector nil)))
    (when (not (eq old-code-vector new-code-vector))
      (break "Code-vector for stack instruction-pointer moved. [index: ~S]" index))
    new-code-vector))

(defun map-stack-flaccid-pointer (function index)
  "If the pointed-to object is moved, reset pointer to NIL."
  (let ((old (stack-frame-ref nil index 0)))
    (cond
     ((not (typep old 'pointer))
      old)
     ((eq old (funcall function old index))
      old)
     (t (setf (stack-frame-ref nil index 0) nil)))))


#+ignore
(defun old-map-stack-vector (function stack start-frame &optional (map-region #'map-header-vals))
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
		  (assert (= 0 (funobj-frame-raw-locals funobj)))
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
			  frame casf-frame #+ignore (dit-frame-casf stack frame))
		    (let ((eip-location (dit-frame-ref stack dit-frame :eip :location))
			  (interrupted-esp (dit-frame-esp stack dit-frame))
			  (interrupted-ebp (dit-frame-ref stack dit-frame :ebp))
			  (casf-funobj (funcall function (stack-frame-funobj stack frame) frame)))
		      (cond
		       ((or (eq 0 casf-funobj)
			    (typep casf-funobj 'function))
			(let ((casf-code-vector (scavenge-funobj-code-vector casf-funobj)))
			  ;; 3. Scavenge the interrupted frame, according to one of i. ii. or iii.
			  (cond
			   ((eq nil interrupted-ebp)
			    (cond
			     ((location-in-object-p casf-code-vector eip-location)
			      (warn "DIT at throw situation, in target ~S at ~S"
				    casf-funobj
				    (dit-frame-ref stack dit-frame :eip :unsigned-byte32))
			      (map-region function interrupted-esp frame))
			     ((location-in-object-p (%run-time-context-slot 'dynamic-jump-next)
						    eip-location)
			      (warn "DIT at throw situation, in dynamic-jump-next.")
			      (let ((dynamic-env (dit-frame-ref stack dit-frame :dynamic-env)))
				(assert (< dynamic-env frame))
				(map-region function dynamic-env frame)))
			     (t (error "Unknown throw situation with EBP=~S, ESP=~S"
				       interrupted-ebp interrupted-esp))))
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
			      (when (eq 0 (stack-frame-ref stack frame -1))
				(break "X1 call in DIT-frame."))
			      (map-region function (+ interrupted-esp 1) frame)
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
			    (when (eq 0 (stack-frame-ref stack frame -1))
			      (break "X1 ii call in DIT-frame."))
			    (map-region function (+ interrupted-esp 2) frame)
			    (setf next-frame frame
				  next-nether-frame (+ interrupted-esp 2 -2)))
			   (t ;; Situation iii. esp(0)=code-vector.
			    (assert (location-in-object-p casf-code-vector
							  (memref interrupted-esp 0 :type :location))
				() "Stack discipline situation iii. invariant broken. CASF=#x~X"
				casf-frame)
			    (when (eq 0 (stack-frame-ref stack frame -1))
			      (break "X1 iii call in DIT-frame."))
			    (map-region function (+ interrupted-esp 1) frame)
			    (setf next-frame frame
				  next-nether-frame (+ interrupted-esp 1 -2))))))
		       (t (error "DIT-frame interrupted unknown CASF funobj: ~Z, CASF ~S"
				 casf-funobj casf-frame))))))
		 (t (error "Don't know how to scavenge across frame ~S of kind ~S." frame funobj)))))))
  (values))

