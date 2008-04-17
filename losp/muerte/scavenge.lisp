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
;;;; $Id: scavenge.lisp,v 1.62 2008-04-17 19:35:49 ffjeld Exp $
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

(defun map-header-vals* (function &optional (vector (%run-time-context-slot nil 'nursery-space)))
  (check-type vector (vector (unsigned-byte 32)))
  (let ((location (+ 2 (object-location vector))))
    (map-header-vals function location (+ location (length vector)))))

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
		 `(= ,code ,x)))
	     (record-scan (&optional (tag :other))
	       (declare (ignorable x))
	       `(let ((x (%word-offset scan ,(movitz:tag tag))))
		  #+ignore (when (and (los0::object-in-space-p (%run-time-context-slot nil 'nursery-space) x)
			     (not (typep x 'vector))
			     (not (typep x 'function)))
			     (format t "~&Scan: ~S: ~Z ~A~%" scan x (type-of x)))
		  ;; `(format t "~&Scan: ~S: ~Z" scan x)
		  (setf *scan-last* x))))
    (do ((verbose *map-header-vals-verbose*)
	 #+ignore (*scan-last* nil) ; Last scanned object, for debugging.
	 (scan start-location (1+ scan)))
	((>= scan end-location))
      (declare (fixnum scan))
      (let ((x (memref scan 0 :type :unsigned-byte16))
            (x2 (memref scan 2 :type :unsigned-byte16)))
        (when verbose
          (format *terminal-io* " [at #x~X: #x~X]" scan x))
        (cond
          ((let ((tag (ldb (byte 3 0) x)))
             (or (= tag #.(movitz:tag :null))
                 (= tag #.(movitz:tag :even-fixnum))
                 (= tag #.(movitz:tag :odd-fixnum))
                 (scavenge-typep x :character))))
          ((or (and (= 0 x2)
		    (= 2 x))
               (and (= #xffff x2)
		    (= #xfffe x))
               (and (= #x7fff x2)
		    (= #xffff x))))
          ((scavenge-typep x :illegal)
           (error "Illegal word #x~4,'0X at #x~X." x scan))
          ((scavenge-typep x :bignum)
           (assert (evenp scan) ()
                   "Scanned bignum-header #x~4,'0X at odd location #x~X." x scan)
           ;; Just skip the bigits
	   (record-scan :other)
           (let* ((bigits (memref scan 0 :index 1 :type :unsigned-byte14))
                  (delta (logior bigits 1)))
             (incf scan delta)))
          ((scavenge-typep x :defstruct)
           (assert (evenp scan) ()
                   "Scanned struct-header #x~4,'0X at odd location #x~X." x scan)
           (record-scan :other))
          ((scavenge-typep x :run-time-context)
           (assert (evenp scan) ()
                   "Scanned run-time-context-header #x~4,'0X at odd location #x~X." 
                   (memref scan 0 :type :unsigned-byte32) scan)
	   (record-scan :other)
	   (let ((rtc (%word-offset scan #.(movitz:tag :other))))
	     (incf scan)
	     (let ((non-lispvals #.(cl:truncate (cl:+ -4 (bt:slot-offset 'movitz::movitz-run-time-context
									 'movitz::pointer-start)
						      (movitz::image-nil-word movitz:*image*))
						4))
		   (end (+ scan #.(movitz::movitz-type-word-size 'movitz::movitz-run-time-context))))
	       (incf scan non-lispvals)
	       (check-type rtc run-time-context)
	       (let ((old-stack (%run-time-context-slot rtc 'stack-vector)))
		 ;; (warn "old-stack: ~Z" old-stack)
		 (map-lisp-vals function scan (1+ end))
		 (let ((new-stack (%run-time-context-slot rtc 'stack-vector)))
		   ;; (warn "new-stack: ~Z" new-stack)
		   (when (not (eq old-stack new-stack))
		     (error "Stack-vector for ~S moved from ~Z to ~Z." rtc old-stack new-stack))))
	       (setf scan end))))
          ((scavenge-typep x :funobj)
           (assert (evenp scan) ()
                   "Scanned funobj-header #x~4,'0X at odd location #x~X." 
                   (memref scan 0 :type :unsigned-byte32) scan)
           (record-scan :other)
           ;; Process code-vector pointers specially..
           (let* ((old-code-vector (memref (incf scan) 0 :type :code-vector))
                  (new-code-vector (if (eq 0 old-code-vector)
                                       0 ; i.e. a non-initialized funobj.
                                       (map-instruction-pointer function scan old-code-vector))))
             (cond
	       ((not (eq new-code-vector old-code-vector))
		;; Code-vector%1op
		(if (location-in-code-vector-p%unsafe old-code-vector
						      (memref (incf scan) 0 :type :location))
		    (map-instruction-pointer function scan old-code-vector)
                    (map-instruction-pointer function scan))
		;; Code-vector%2op
		(if (location-in-code-vector-p%unsafe old-code-vector
						      (memref (incf scan) 0 :type :location))
		    (map-instruction-pointer function scan old-code-vector)
                    (map-instruction-pointer function scan))
		;; Code-vector%3op
		(if (location-in-code-vector-p%unsafe old-code-vector
						      (memref (incf scan) 0 :type :location))
		    (map-instruction-pointer function scan old-code-vector)
                    (map-instruction-pointer function scan))
		;; lambda-list and name
		(map-header-vals function (incf scan) (incf scan 2))
		;; Jumpers
		(let ((num-jumpers (memref scan 0 :type :unsigned-byte14)))
		  (dotimes (i num-jumpers)
		    (map-instruction-pointer function (incf scan) old-code-vector))))
	       ((eq new-code-vector old-code-vector)
		;; Code-vector%1op
		(unless (location-in-code-vector-p%unsafe old-code-vector
							  (memref (incf scan) 0 :type :location))
		  (map-instruction-pointer function scan))
		;; Code-vector%2op
		(unless (location-in-code-vector-p%unsafe old-code-vector
							  (memref (incf scan) 0 :type :location))
		  (map-instruction-pointer function scan))
		;; Code-vector%3op
		(unless (location-in-code-vector-p%unsafe old-code-vector
							  (memref (incf scan) 0 :type :location))
		  (map-instruction-pointer function scan))
		;; lambda-list and name
		(map-header-vals function (incf scan) (incf scan 2))
		;; Jumpers
		(let ((num-jumpers (memref scan 0 :type :unsigned-byte14)))
		  (incf scan num-jumpers))))))
          ((scavenge-typep x :infant-object)
           (assert (evenp scan) ()
                   "Scanned infant #x~4,'0X at odd location #x~X." x scan)
           (error "Scanning an infant object #x~4,'0X at #x~X (end #x~X)." x scan end-location))
          ((scavenge-typep x :basic-vector)
           (assert (evenp scan) ()
                   "Scanned basic-vector-header #x~4,'0X at odd location #x~X." x scan)
           (cond
             ((or (scavenge-wide-typep x :basic-vector
                                       #.(bt:enum-value 'movitz:movitz-vector-element-type :u8))
                  (scavenge-wide-typep x :basic-vector
                                       #.(bt:enum-value 'movitz:movitz-vector-element-type :character))
                  (scavenge-wide-typep x :basic-vector
                                       #.(bt:enum-value 'movitz:movitz-vector-element-type :code)))
              (let ((len (memref scan 4)))
                (record-scan :other)
                (incf scan (1+ (* 2 (truncate (+ 7 len) 8))))))
             ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u16))
              (let ((len (memref scan 0 :index 1)))
                (record-scan :other)
                (incf scan (1+ (* 2 (truncate (+ 3 len) 4))))))
             ((or (scavenge-wide-typep x :basic-vector
				       #.(bt:enum-value 'movitz:movitz-vector-element-type :u32))
		  (scavenge-wide-typep x :basic-vector
				       #.(bt:enum-value 'movitz:movitz-vector-element-type :stack)))
              (let ((len (memref scan 4)))
                (record-scan :other)
                (incf scan (1+ (logand (1+ len) -2)))))
             ((scavenge-wide-typep x :basic-vector #.(bt:enum-value 'movitz:movitz-vector-element-type :bit))
              (let ((len (memref scan 4)))
                (record-scan :other)
                (incf scan (1+ (* 2 (truncate (+ 63 len) 64))))))
             ((or (scavenge-wide-typep x :basic-vector
                                       #.(bt:enum-value 'movitz:movitz-vector-element-type
							:any-t))
                  (scavenge-wide-typep x :basic-vector
                                       #.(bt:enum-value 'movitz:movitz-vector-element-type
							:indirects)))
              (record-scan :other))
             (t (error "Scanned unknown basic-vector-header #x~4,'0X at location #x~X." x scan))))
          ((and (eq x 3) (eq x2 0))
           ;; (record-scan scan)
           (incf scan)
           (let ((delta (memref scan 0)))
             (check-type delta positive-fixnum)
	     (format t "at ~S skipping ~S to ~S." scan delta (+ scan delta))
             (incf scan delta)))
          (t ;; (typep x 'pointer)
           (let* ((old (memref scan 0))
                  (new (funcall function old scan)))
             (unless (eq old new)
               (when verbose
                 (format *terminal-io* " [~Z => ~Z]" old new))
               (setf (memref scan 0) new))))))))
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

(defun scavenge-match-code-vector (function code-vector location)
  "Is location inside code-vector, under evacuator function?
If so, return the actual code-vector pointer that matches."
  (if (location-in-code-vector-p%unsafe code-vector location)
      code-vector
    (let ((fwd (funcall function code-vector nil)))
      (check-type fwd code-vector)
      (when (location-in-code-vector-p%unsafe fwd location)
	fwd))))

(defun scavenge-find-pf (function location)
  (loop for (slot-name type) in (slot-value (class-of (current-run-time-context)) 'slot-map)
      do (when (eq type 'code-vector-word)
	   (let ((it (scavenge-match-code-vector function
						 (%run-time-context-slot nil slot-name)
						 location)))
	     (when it (return it))))))

(defun scavenge-find-code-vector (function location casf-funobj esi &optional primitive-function-p edx)
  (flet ((match-funobj (function funobj location)
	   (cond
	    ((not (typep funobj 'function))
	     nil)
	    ((let ((x (funobj-code-vector funobj)))
	       (scavenge-match-code-vector function x location)))
	    ((let ((x (funobj-code-vector%1op funobj)))
	       (and (typep x '(not fixnum))
		    (scavenge-match-code-vector function x location))))
	    ((let ((x (funobj-code-vector%2op funobj)))
	       (and (typep x '(not fixnum))
		    (scavenge-match-code-vector function x location))))
	    ((let ((x (funobj-code-vector%3op funobj)))
	       (and (typep x '(not fixnum))
		    (scavenge-match-code-vector function x location)))))))
    (cond
     ((scavenge-match-code-vector function (symbol-value 'ret-trampoline) location))
     ((scavenge-match-code-vector function
				  (%run-time-context-slot nil 'dynamic-jump-next)
				  location))
     ((eq 0 casf-funobj)
      (let ((dit-code-vector (symbol-value 'default-interrupt-trampoline)))
	(cond
	 ((scavenge-match-code-vector function dit-code-vector location))
	 ((match-funobj function esi location))
	 (t (break "DIT returns outside DIT??")))))
     ((match-funobj function casf-funobj location))
     ((match-funobj function esi location))      
     ((match-funobj function edx location))
     ((not (typep casf-funobj 'function))
      (break "Unknown funobj/frame-type: ~S" casf-funobj))
     ((when primitive-function-p
	(scavenge-find-pf function location)
	#+ignore
	(%find-code-vector location)))
     (t (with-simple-restart (continue "Try to perform a code-vector-search.")
	  (error "Unable to decode EIP #x~X funobj ~S, ESI ~S."
		 (* 4 location) casf-funobj esi))
	(or (%find-code-vector location)
	    (error "Code-vector-search for EIP #x~X also failed."
		   (* 4 location)))))))

(defun map-stack-value (function value frame)
  (if (not (typep value 'pointer))
      value
    (funcall function value frame)))

(defun map-stack (function frame frame-bottom eip-index map-region)
  "Scavenge the stack starting at location <frame> which ends at <frame-bottom>
and whose return instruction-pointer is at location eip-index."
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
			 (scavenge-find-code-vector function
						    (stack-frame-ref nil eip-index 0 :location)
						    frame-funobj nil nil)))
		   (map-instruction-pointer function eip-index old-code-vector))
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
  "Scavenge the stack, starting at a DIT stack-frame." 
  (with-funcallable (map-region)
    (let* ((atomically
	    (dit-frame-ref nil dit-frame :atomically-continuation :unsigned-byte32))
	   (secondary-register-mode-p
	    (logbitp 10 (dit-frame-ref nil dit-frame :eflags :unsigned-byte32)))
	   (casf-frame
	    (dit-frame-casf nil dit-frame))
	   (casf-funobj (map-stack-value function (stack-frame-funobj nil casf-frame) casf-frame))
	   (casf-code-vector (case casf-funobj
			       (0 (symbol-value 'default-interrupt-trampoline))
			       (t (funobj-code-vector casf-funobj)))))
      ;; 1. Scavenge the dit-frame
      (cond
       ((and (not (= 0 atomically))
	     (= 0 (ldb (byte 2 0) atomically)))
	;; Interrupt occurred inside an (non-pf) atomically, so none of the
	;; GC-root registers are active.
	#+ignore (setf (dit-frame-ref nil dit-frame :eax) nil
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
	      (scavenge-find-code-vector function
					 (stack-frame-ref nil eip-index 0 :location)
					 0 interrupted-esi
					 nil)))
	;; (when atomically (we should be more clever about the stack..))
	(multiple-value-bind (x0-location x0-tag)
	    (stack-frame-ref nil next-frame-bottom 0 :signed-byte30+2)
	  (cond
	   ((and (or (eq x0-tag 1)	; 1 or 5?
		     (eq x0-tag 3)	; 3 or 7?
		     (and (oddp x0-location) (eq x0-tag 2))) ; 6?
		 (scavenge-match-code-vector function casf-code-vector x0-location))
	    (when (= #xc3 (memref-int (stack-frame-ref nil next-eip-index 0 :unsigned-byte32)
				      :physicalp nil :type :unsigned-byte8))
	      (setf (stack-frame-ref nil next-eip-index 0 :code-vector)
		(symbol-value 'ret-trampoline)))
	    (let* ((old-x0-code-vector
		    (scavenge-find-code-vector function
					       (stack-frame-ref nil next-eip-index 0 :location)
					       casf-funobj interrupted-esi t
					       (unless secondary-register-mode-p
						 (dit-frame-ref nil dit-frame :edx)))))
	      (map-instruction-pointer function next-eip-index old-x0-code-vector dit-frame))
	    (setf next-eip-index next-frame-bottom
		  next-frame-bottom (1+ next-frame-bottom)))
	   (t (multiple-value-bind (x1-location x1-tag)
		  (stack-frame-ref nil next-frame-bottom 1 :signed-byte30+2)
		(when (and (or (eq x1-tag 1) ; 1 or 5?
			       (eq x1-tag 3) ; 3 or 7?
			       (and (oddp x1-location) (eq x1-tag 2))) ; 6?
			   (scavenge-match-code-vector function casf-code-vector x1-location))
		  (let* ((old-x1-code-vector
			  (scavenge-find-code-vector function
						     (stack-frame-ref nil next-eip-index 0 :location)
						     casf-funobj
						     (unless secondary-register-mode-p
						       interrupted-esi)
						     t)))
		    (map-instruction-pointer function next-eip-index old-x1-code-vector dit-frame))
		  (setf next-eip-index (+ 1 next-frame-bottom)
			next-frame-bottom (+ 2 next-frame-bottom)))))))
	;; proceed
	(map-stack function casf-frame next-frame-bottom next-eip-index map-region)))))

(defun map-instruction-pointer (function location
				&optional (old-code-vector (memref location 0 :type :code-vector))
					  debug-context)
  "Update the (raw) instruction-pointer at location,
assuming the pointer refers to old-code-vector."
  (declare (ignorable debug-context))
  ;; (check-type old-code-vector code-vector) ; Can't de-reference old objects..
  (let ((old-ip-location (memref location 0 :type :location)))
    (assert (location-in-code-vector-p%unsafe old-code-vector old-ip-location))
    (let ((new-code-vector (funcall function old-code-vector nil)))
      (when (not (eq old-code-vector new-code-vector))
	(check-type new-code-vector code-vector)
	(let ((location-offset (- old-ip-location (object-location old-code-vector)))
	      (lowbits (ldb (byte 2 0) (memref location 0 :type :unsigned-byte8))))
	  (let ((oeip (memref location 0 :type :unsigned-byte32))
		(neip (+ (* 4 (object-location new-code-vector))
			 (* location-offset 4)
			 lowbits)))
	    #+ignore
	    (warn "Instruction-pointer moved at location ~S, old=~S [~S ~S ~S], new=~Z ~S [~S ~S ~S] context ~S"
		  location
		  oeip
		  (memref-int oeip :physicalp nil :type :unsigned-byte8 :offset 0)
		  (memref-int oeip :physicalp nil :type :unsigned-byte8 :offset 1)
		  (memref-int oeip :physicalp nil :type :unsigned-byte8 :offset 2)
		  new-code-vector
		  neip
		  (memref-int neip :physicalp nil :type :unsigned-byte8 :offset 0)
		  (memref-int neip :physicalp nil :type :unsigned-byte8 :offset 1)
		  (memref-int neip :physicalp nil :type :unsigned-byte8 :offset 2)
		  debug-context))
	  (setf (memref location 0 :type :unsigned-byte32)
	    (+ (* 4 (object-location new-code-vector))
	       (* location-offset 4)
	       lowbits))))
      new-code-vector)))
