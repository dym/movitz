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
;;;; $Id: scavenge.lisp,v 1.1 2004/03/29 14:30:22 ffjeld Exp $
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
  (check-type start-location fixnum)
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
		    (:cmpw ,code :ax)))))
    (do ((i start-location (1+ i)))
	((>= i end-location))
      (let ((*i* i)
	    (x (memref i 0 0 :lisp)))
	(declare (special *i*))
	(cond
	 ((typep x '(or null fixnum character)))
	 ((scavenge-typep x :illegal)
	  (error "Illegal word ~Z at ~S." x i))
	 ((scavenge-typep x :funobj)
	  ;; Process code-vector pointer specially..
	  (let ((code-vector (%word-offset (memref i 0 -1 :lisp) -2))
		(num-jumpers (ldb (byte 14 0) (memref i 0 6 :lisp))))
	    (check-type code-vector vector-u8)
	    (map-heap-words function (+ i 4) (+ i 6)) ; scan funobj's lambda-list and name fields
	    (let ((new-code-vector (funcall function code-vector)))
	      (check-type new-code-vector vector-u8)
	      (unless (eq code-vector new-code-vector)
		(error "Code-vector migration is not implemented.")
		(setf (memref i 0 -1 :lisp) (%word-offset new-code-vector 2))
		;; Do more stuff here to update code-vectors and jumpers
		))
	    (incf i (+ 6 num-jumpers)))) ; Don't scan the jumpers.
	 ((scavenge-typep x :infant-object)
	  (error "Scanning an infant object ~Z at ~S." x i))
	 ((or (scavenge-wide-typep x :vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :u8))
	      (scavenge-wide-typep x :vector
				   #.(bt:enum-value 'movitz:movitz-vector-element-type :character)))
	  (let ((len (memref i -2 0 :unsigned-byte16)))
	    (incf i (* 2 (truncate (+ 7 len) 8)))))
	 ((scavenge-wide-typep x :vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u16))
	  (let ((len (memref i -2 0 :unsigned-byte16)))
	    (incf i (* 2 (truncate (+ 3 len) 4)))))
	 ((scavenge-wide-typep x :vector #.(bt:enum-value 'movitz:movitz-vector-element-type :u32))
	  (let ((len (memref i -2 0 :unsigned-byte16)))
	    (incf i (* 2 (truncate (+ 1 len) 2)))))
	 ((eq x (fixnum-word 3))
	  (incf i)
	  (incf i (memref i 0 0 :lisp)))
	 ((typep x 'pointer)
	  (let ((new (funcall function x)))
	    (check-type new pointer)
	    (setf (memref i 0 0 :lisp) new)))))))
  (values))

(defun map-stack-words (function start-stack-frame)
  "Map function over the potential pointer words of a stack, starting
at the start-stack-frame location."
  (loop for nether-frame = start-stack-frame then frame
      and frame = (stack-frame-uplink start-stack-frame) then (stack-frame-uplink frame)
      while (plusp frame)
      do (let ((funobj (stack-frame-funobj frame)))
	   (typecase funobj
	     (integer
	      (error "Don't know how to scavenge across an interrupt frame."))
	     (function
	      (assert (= 0 (funobj-frame-num-unboxed funobj)))
	      (map-heap-words function (+ nether-frame 2) frame)))))
  (values))

