;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      los0-gc.lisp
;;;; Description:   A simple GC architecture for los0.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Feb 21 17:48:32 2004
;;;;                
;;;; $Id: los0-gc.lisp,v 1.8 2004/04/15 13:21:42 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :los0-gc)

(in-package muerte.init)

(defun make-space (location)
  "Make a space vector at a fixed location."
  (assert (evenp location))
  (macrolet ((x (index)
	       `(memref location 0 ,index :unsigned-byte16)))
    (setf (x 0) #x0
	  (x 1) #xfffd
	  (x 2) #.(cl:dpb (bt:enum-value 'movitz:movitz-vector-element-type :u32)
			  (cl:byte 8 8)
			  (bt:enum-value 'movitz:other-type-byte :vector))
	  (x 3) #xfffd))
  (%word-offset location #.(movitz:tag :other)))

(defmacro space-other (space)
  `(memref ,space -6 3 :lisp))

(defmacro space-fresh-pointer (space)
  `(memref ,space -6 2 :lisp))

(defun allocate-space (&optional other-space)
  (let ((space (make-array #xfffd :element-type '(unsigned-byte 32))))
    (setf (space-fresh-pointer space) 2
	  (space-other space) other-space)
    space))

(defun initialize-space (space)
  (setf (space-fresh-pointer space) 2))

(defun allocate-duo-space ()
  (let* ((space1 (allocate-space))
	 (space2 (allocate-space space1)))
    (setf (space-other space1) space2)))

(defun space-cons-pointer ()
  (aref (%run-time-context-slot 'nursery-space) 0))

(define-primitive-function new-fast-cons ()
  "Allocate a cons cell from nursery-space."
  (with-inline-assembly (:returns :eax)
   retry-cons
    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
    (:movl (:edx 2) :ecx)
    (:cmpl #x3fff4 :ecx)
    (:jge '(:sub-program ()
	    (:int 113)
	    ;; This interrupt can be retried.
	    (:jmp 'retry-cons)))
    (:movl :eax (:edx :ecx 2))
    (:movl :ebx (:edx :ecx 6))
    (:leal (:edx :ecx 3) :eax)
    (:addl 8 :ecx)
    (:movl :ecx (:edx 2))
    (:ret)))

(defun new-malloc-clumps (clumps)
  (check-type clumps (integer 0 1000))
  (with-inline-assembly (:returns :ebx)
   retry
    (:compile-form (:result-mode :eax) clumps)
    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
    (:movl (:edx 2) :ecx)
    (:leal (:edx :ecx 8) :ebx)
    (:leal ((:eax 2) :ecx) :ecx)
    (:cmpl #x3fff4 :ecx)
    (:jge '(:sub-program ()
	    (:compile-form (:result-mode :ignore)
	     (stop-and-copy))
	    (:jmp 'retry)))
    (:movl :ecx (:edx 2))
    (:xorl :ecx :ecx)
   init-loop				; Now init eax number of clumps.
    (:movl :edi (:ebx (:ecx 2) -6))
    (:movl :edi (:ebx (:ecx 2) -2))
    (:addl 4 :ecx)
    (:cmpl :eax :ecx)
    (:jb 'init-loop)
    (:movl #.(movitz:tag :infant-object) (:ebx -2))))

(defun los0-handle-out-of-memory (exception interrupt-frame)
  (declare (ignore exception interrupt-frame))
  (format t "~&;; Handling out-of-memory exception..")
  (stop-and-copy))

(defun install-los0-consing ()
  (setf (%run-time-context-slot 'nursery-space)
    (allocate-duo-space))
  (let ((conser (symbol-value 'new-fast-cons)))
    (check-type conser vector)
    (setf (%run-time-context-slot 'muerte::fast-cons)
      conser))
  (let ((old-malloc (symbol-function 'muerte:malloc-clumps)))
    (setf (symbol-function 'muerte:malloc-clumps)
      (symbol-function 'new-malloc-clumps))
    (setf (symbol-function 'new-malloc-clumps)
      old-malloc))
  (setf (interrupt-handler 113)
    (lambda (exception interrupt-frame)
      (declare (ignore exception interrupt-frame))
      (format t "~&;; Handling out-of-memory exception..")
      (stop-and-copy)))
  (values))

(defun install-old-consing ()
  (let ((conser (symbol-value 'muerte::fast-cons)))
    (check-type conser vector)
    (setf (%run-time-context-slot 'muerte::fast-cons)
      conser))
  (let ((old-malloc (symbol-function 'muerte:malloc-clumps)))
    (setf (symbol-function 'muerte:malloc-clumps)
      (symbol-function 'new-malloc-clumps))
    (setf (symbol-function 'new-malloc-clumps)
      old-malloc))
  (values))

(defun object-in-space-p (space object)
  (check-type space vector-u32)
  (and (typep object 'pointer)
       (< (object-location space)
	  (object-location object)
	  (+ (object-location space)
	     (array-dimension space 0)))))

(defun report-nursery (x location)
  "Write a message if x is inside newspace."
  (when (object-in-space-p (%run-time-context-slot 'nursery-space) x)
    (format t "~&~Z: ~S: ~S from ~S" x (type-of x) x location))
  x)

(defun report-inactive-space (x location)
  "Check that x is not pointing into (what is presumably) oldspace."
  (when (object-in-space-p (space-other (%run-time-context-slot 'nursery-space)) x)
    (break "~Z: ~S: ~S from ~S" x (type-of x) x location))
  x)

(defun location-finder (find-location)
  (lambda (x location)
    (when (location-in-object-p x find-location)
      (break "The location ~S is in the object at ~Z referenced from location ~S."
	     find-location x location))
    x))

(defun stop-and-copy ()
  (let* ((space0 (%run-time-context-slot 'nursery-space))
	 (space1 (space-other space0)))
    (check-type space0 vector-u32)
    (check-type space1 vector-u32)
    (assert (eq space0 (space-other space1)))
    (multiple-value-bind (newspace oldspace)
	(if (< (space-fresh-pointer space0) ; Chose the emptiest space as newspace.
	       (space-fresh-pointer space1))
	    (values space0 space1)
	  (values space1 space0))
      ;; Ensure newspace is activated.
      (setf (%run-time-context-slot 'nursery-space) newspace)
      ;; (assert (< #x200 (- (length newspace) (space-fresh-pointer newspace))))
      ;; Evacuate-oldspace is to be mapped over every potential pointer.
      (flet ((evacuate-oldspace (x location)
	       "If x is in oldspace, migrate it to newspace."
	       (declare (ignore location))
	       (if (not (object-in-space-p oldspace x))
		   x
		 (let ((forwarded-x (memref (object-location x) 0 1 :lisp)))
		   (if (object-in-space-p newspace forwarded-x)
		       forwarded-x
		     (let ((forward-x (shallow-copy x)))
		       (setf (memref (object-location x) 0 1 :lisp) forward-x)
		       forward-x))))))
	;; Scavenge roots
	(map-heap-words #'evacuate-oldspace 0 (+ (malloc-buffer-start)
						 (* 2 (malloc-cons-pointer))))
	(map-stack-words #'evacuate-oldspace (current-stack-frame))
	;; Scan newspace, Cheney style.
	(loop with newspace-location = (+ 2 (object-location newspace))
	    with scan-pointer = 2
	    as fresh-pointer = (space-fresh-pointer newspace)
	    while (< scan-pointer fresh-pointer)
	    do (map-heap-words #'evacuate-oldspace
			       (+ newspace-location scan-pointer)
			       (+ newspace-location (space-fresh-pointer newspace)))
	       (setf scan-pointer fresh-pointer))
	;; GC completed, oldspace is evacuated.
	(let ((old-size (truncate (- (space-fresh-pointer oldspace) 2) 2))
	      (new-size (truncate (- (space-fresh-pointer newspace) 2) 2)))
	  (format t "~&;; Old space: ~/muerte:pprint-clumps/, new space: ~
~/muerte:pprint-clumps/, freed: ~/muerte:pprint-clumps/.~%"
		  old-size new-size (- old-size new-size)))
	(initialize-space oldspace))))
  (values))
