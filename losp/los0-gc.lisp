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
;;;; $Id: los0-gc.lisp,v 1.28 2004/07/15 21:06:33 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :los0-gc)

(in-package muerte.init)

(defvar *gc-quiet* nil)
    
(defun make-space (location size)
  "Make a space vector at a fixed location."
  (assert (evenp location))
  (macrolet ((x (index)
	       `(memref location 0 ,index :unsigned-byte32)))
    (setf (x 1) (* #.movitz:+movitz-fixnum-factor+ size)
	  (x 0) #.(cl:dpb (bt:enum-value 'movitz:movitz-vector-element-type :u32)
			  (cl:byte 8 8)
			  (bt:enum-value 'movitz:other-type-byte :basic-vector))))
  (%word-offset location #.(movitz:tag :other)))


(defmacro space-fresh-pointer (space)
  `(memref ,space -6 2 :lisp))

(defmacro space-other (space)
  `(memref ,space -6 3 :lisp))

(defun allocate-space (size &optional other-space)
  (let ((space (make-array size :element-type '(unsigned-byte 32))))
    (initialize-space space)
    (setf (space-other space) other-space)
    space))

(defun initialize-space (space)
  (setf (space-fresh-pointer space) 2)
  space)

(defun allocate-duo-space (size)
  (let* ((space1 (allocate-space size))
	 (space2 (allocate-space size space1)))
    (setf (space-other space1) space2)
    space1))

;;;(defun space-cons-pointer ()
;;;  (aref (%run-time-context-slot 'nursery-space) 0))

(defun test ()
  (warn "install..")
  (install-los0-consing 4)
  (warn "nursery: ~Z, other: ~Z" 
	(%run-time-context-slot 'muerte::nursery-space)
	(space-other (%run-time-context-slot 'muerte::nursery-space)))
  (warn "first cons: ~Z" (funcall 'truncate #x100000000 3))
  (warn "second cons: ~Z" (funcall 'truncate #x100000000 3))
  (halt-cpu)
  (values))

(define-primitive-function los0-fast-cons ()
  "Allocate a cons cell from nursery-space."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	   retry-cons
	    ;; Set up thread-atomical execution
	    (:locally (:movl ,(movitz::atomically-status-simple-pf 'fast-cons t)
			     (:edi (:edi-offset atomically-status))))
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ecx)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :ecx)
	    (:jae '(:sub-program (allocation-failed)
		    ;; Exit thread-atomical
		    (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
			       (:edi (:edi-offset atomically-status))))
		    (:int 113)
		    ;; This interrupt can be retried.
		    (:jmp 'retry-cons)))
	    (:movl :eax (:edx :ecx 2))
	    (:movl :ebx (:edx :ecx 6))
	    (:addl 8 :ecx)
	    (:movl :ecx (:edx 2))	; Commit allocation
	    ;; Exit thread-atomical
	    (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
			     (:edi (:edi-offset atomically-status))))
	    (:leal (:edx :ecx -5) :eax)
	    (:ret))))
    (do-it)))

(define-primitive-function los0-get-cons-pointer ()
  "Return in EAX the next object location with space for EAX words, with tag 6.
Preserve ECX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	   retry
	    (:locally (:cmpl 0 (:edi (:edi-offset atomically-status)))) ; Atomically?
	    (:je '(:sub-program ()
		   (:int 50)))		; This must be called inside atomically.
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ebx)
	    (:leal (:ebx :eax 4) :eax)
	    (:andl -8 :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:ja '(:sub-program (probe-failed)
		   (:int 113)
		   (:jmp 'retry)))
	    (:movl :edi (:edx :ebx 8 ,movitz:+other-type-offset+))
	    (:leal (:edx :ebx 8) :eax)
	    (:ret))))
    (do-it)))

(define-primitive-function los0-cons-commit ()
  "Commit allocation of ECX/fixnum words.
Preserve EAX and EBX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	   retry
	    (:locally (:cmpl 0 (:edi (:edi-offset atomically-status)))) ; Atomically?
	    (:je '(:sub-program ()
		   (:int 50)))		; This must be called inside atomically.
	    (:addl ,movitz:+movitz-fixnum-factor+ :ecx)
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:andl -8 :ecx)
	    (:addl (:edx 2) :ecx)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :ecx)
	    (:ja '(:sub-program (commit-failed)
		   (:int 113)
		   (:jmp 'retry)))
	    (:movl :ecx (:edx 2))
	    (:leal (:edx :ecx) :ecx)
	    (:ret))))
    (do-it)))
    
(define-primitive-function los0-box-u32-ecx ()
  "Make u32 in ECX into a fixnum or bignum."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:cmpl ,movitz:+movitz-most-positive-fixnum+ :ecx)
	    (:ja 'not-fixnum)
	    (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
	    (:ret)
	   not-fixnum
	   retry-cons
	    (:locally (:movl ,(movitz::atomically-status-simple-pf 'box-u32-ecx t)
			     (:edi (:edi-offset atomically-status))))
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:jae '(:sub-program ()
		    (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
			       (:edi (:edi-offset atomically-status))))
		    (:int 113)		; This interrupt can be retried.
		    (:jmp 'retry-cons)))
	    (:movl ,(dpb movitz:+movitz-fixnum-factor+
			 (byte 16 16) (movitz:tag :bignum 0))
		   (:edx :eax 2))
	    (:movl :ecx (:edx :eax 6))
	    (:addl 8 :eax)
	    (:movl :eax (:edx 2))	; Commit allocation
	    ;; Exit thread-atomical
	    (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
			     (:edi (:edi-offset atomically-status))))
	    (:leal (:edx :eax) :eax)
	    (:ret))))
    (do-it)))

(define-primitive-function los0-malloc-pointer-words (words)
  "Number of words in EAX/fixnum. Result in EAX with tag :other."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:addl 4 :eax)
	    (:andl -8 :eax)
	    (:movl :eax :ebx)		; Save count for later
	   retry
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ecx)
	    (:leal (:ecx :eax) :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:ja '(:sub-program ()
		   (:int 113)
		   (:movl :ebx :eax)	; Restore count in EAX before retry
		   (:jmp 'retry)))
	    (:movl :eax (:edx 2))
	    (:movl ,(movitz:tag :infant-object) (:edx :ecx ,(+ 8 movitz:+other-type-offset+)))
	    (:leal (:edx :ecx 8) :eax)		
	    (:xorl :ecx :ecx)
	   init-loop			; Now init ebx number of words
	    (:movl :edi (:eax :ecx ,(- (movitz:tag :other))))
	    (:addl 4 :ecx)
	    (:cmpl :ebx :ecx)
	    (:jb 'init-loop)
	    (:ret))))
    (do-it)))

(define-primitive-function los0-malloc-non-pointer-words (words)
  "Number of words in EAX/fixnum. Result in EAX with tag :other."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:addl 4 :eax)
	    (:andl -8 :eax)
	    (:movl :eax :ebx)		; Save count for later
	   retry
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ecx)
	    (:leal (:ecx :eax) :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:ja '(:sub-program ()
		   (:int 113)
		   (:movl :ebx :eax)	; Restore count in EAX before retry
		   (:jmp 'retry)))
	    (:movl :eax (:edx 2))
	    (:movl ,(movitz:tag :infant-object) (:edx :ecx ,(+ 8 movitz:+other-type-offset+)))
	    (:leal (:edx :ecx 8) :eax)	; Now EAX is a valid pointer
	    (:ret))))
    (do-it)))


(defun install-los0-consing (&key (context (current-run-time-context))
				  (kb-size 1024)
				  duo-space)
  "Install the 'Los0' GC architecture on run-time-context CONTEXT.
Either use an explicitly provided DUO-SPACE, or allocate a fresh
duo-space where each space is KB-SIZE kilobytes."
  (setf (exception-handler 113)
    (lambda (exception interrupt-frame)
      (declare (ignore exception interrupt-frame))
      (unless *gc-quiet*
	(format t "~&;; GC.. "))
      (stop-and-copy)
      (loop				; This is  a nice opportunity to poll the keyboard..
	(case (muerte.x86-pc.keyboard:poll-char)
	  ((#\esc)
	   (break "Los0 GC keyboard poll."))
	  ((nil)
	   (return))))))
  (let* ((actual-duo-space (or duo-space
			       (allocate-duo-space (* kb-size #x100))))
	 (last-location (object-location (cons 1 2))))
    (macrolet ((install-primitive (name slot)
		 `(let ((code-vector (symbol-value ',name)))
		    (check-type code-vector code-vector)
		    (if (eq context (current-run-time-context))
			;; The point of this is to not trigger CLOS bootstrapping.
			(setf (%run-time-context-slot ',slot) code-vector)
		      (setf (%run-time-context-slot ',slot context) code-vector)))))
      (install-primitive los0-fast-cons muerte::fast-cons)
      (install-primitive los0-box-u32-ecx muerte::box-u32-ecx)
      (install-primitive los0-get-cons-pointer muerte::get-cons-pointer)
      (install-primitive los0-cons-commit muerte::cons-commit)
      (install-primitive los0-malloc-pointer-words muerte::malloc-pointer-words)
      (install-primitive los0-malloc-non-pointer-words muerte::malloc-non-pointer-words))
    (if (eq context (current-run-time-context))
	(setf (%run-time-context-slot 'muerte::nursery-space)
	  actual-duo-space)
      (setf (%run-time-context-slot 'muerte::nursery-space context)
	actual-duo-space))
    ;; Pretend that the heap stops here, so that we don't have to scan
    ;; the entire tail end of memory, which isn't going to be used.
    (setf (cdar muerte::%memory-map-roots%) last-location))
  (values))

(defun object-in-space-p (space object)
  (check-type space vector-u32)
  (and (typep object 'pointer)
       (< (object-location space)
	  (object-location object)
	  (+ (object-location space)
	     (array-dimension space 0)))))

(defun tenure ()
  (install-old-consing)
  (install-los0-consing))

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

(defun kill-the-newborns ()
  (let* ((oldspace (%run-time-context-slot 'nursery-space))
	 (newspace (space-other oldspace)))
    (setf (%run-time-context-slot 'nursery-space) newspace)
    (flet ((zap-oldspace (x location)
	     (declare (ignore location))
	     (if (object-in-space-p oldspace x)
		 nil
	       x)))
      (map-heap-words #'zap-oldspace 0 (malloc-end))
      (map-stack-words #'zap-oldspace (current-stack-frame))
      (initialize-space oldspace)
      (values))))

(defparameter *x* #500())

(defun stop-and-copy (&optional evacuator)
  (setf (fill-pointer *x*) 0)
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
      ;; Evacuate-oldspace is to be mapped over every potential pointer.
      (let ((evacuator
	     (or evacuator
		 (lambda (x location)
		   "If x is in oldspace, migrate it to newspace."
		   (declare (ignore location))
		   (cond
		    ((not (object-in-space-p oldspace x))
		     x)
		    #+ignore
		    ((typep x 'muerte::tag6)
		     (let ((fwi (position (object-location x) *x* :test #'eq)))
		       (if fwi
			   (muerte::%word-offset (aref *x* (1+ fwi)) 6)
			 (let ((fw (shallow-copy x)))
			   (vector-push (object-location x) *x*)
			   (vector-push (object-location fw) *x*)
			   fw))))
		    (t (let ((forwarded-x (memref (object-location x) 0 0 :lisp)))
			 (if (object-in-space-p newspace forwarded-x)
			     (progn
			       (assert (eq (object-tag forwarded-x)
					   (object-tag x)))
			       forwarded-x)
			   (let ((forward-x (shallow-copy x)))
			     (when (typep x 'muerte::bignum)
			       (assert (= x forward-x)))
			     (setf (memref (object-location x) 0 0 :lisp) forward-x)
			     forward-x)))))))))
	;; Scavenge roots
	(dolist (range muerte::%memory-map-roots%)
	  (map-heap-words evacuator (car range) (cdr range)))
	(map-stack-words evacuator (current-stack-frame))
	;; Scan newspace, Cheney style.
	(loop with newspace-location = (+ 2 (object-location newspace))
	    with scan-pointer = 2
	    as fresh-pointer = (space-fresh-pointer newspace)
	    while (< scan-pointer fresh-pointer)
	    do (map-heap-words evacuator
			       (+ newspace-location scan-pointer)
			       (+ newspace-location (space-fresh-pointer newspace)))
	       (setf scan-pointer fresh-pointer))

	#+ignore
	(dotimes (i (truncate (length *x*) 2))
	  (let ((x (muerte::%word-offset (aref *x* (* i 2)) 6))
		(y (muerte::%word-offset (aref *x* (1+ (* i 2))) 6)))
	    (assert (and (object-in-space-p newspace y)
			 (object-in-space-p oldspace x)
			 (or (typep x 'muerte::std-instance)
			     (equalp x y)))
		()
	      "Fail: i=~D, x: ~S/~Z, y: ~S/~Z, o: ~Z, n: ~Z" i x x y y oldspace newspace)))

	;; GC completed, oldspace is evacuated.
	(unless *gc-quiet*
	  (let ((old-size (truncate (- (space-fresh-pointer oldspace) 2) 2))
		(new-size (truncate (- (space-fresh-pointer newspace) 2) 2)))
	    (format t "Old space: ~/muerte:pprint-clumps/, new space: ~
~/muerte:pprint-clumps/, freed: ~/muerte:pprint-clumps/.~%"
		    old-size new-size (- old-size new-size))))
	(initialize-space oldspace))))
  (values))
