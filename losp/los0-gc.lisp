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
;;;; $Id: los0-gc.lisp,v 1.42 2004/10/11 13:51:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :los0-gc)

(in-package muerte.init)

(defvar *gc-quiet* nil)
(defvar *gc-running* nil)
(defvar *gc-break* nil)
(defvar *gc-trigger* nil)
(defvar *gc-consitency-check* t) 

    
(defun make-space (location size)
  "Make a space vector at a fixed location."
  (assert (evenp location))
  (macrolet ((x (index)
	       `(memref location 0 :index ,index :type :unsigned-byte32)))
    (setf (x 1) (* #.movitz:+movitz-fixnum-factor+ size)
	  (x 0) #.(cl:dpb (bt:enum-value 'movitz:movitz-vector-element-type :u32)
			  (cl:byte 8 8)
			  (bt:enum-value 'movitz:other-type-byte :basic-vector))))
  (%word-offset location #.(movitz:tag :other)))


(defmacro space-fresh-pointer (space)
  `(memref ,space -6 :index 2))

(defmacro space-other (space)
  `(memref ,space -6 :index 3))

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
  "Allocate a cons cell of EAX and EBX from nursery-space."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	   retry-cons
	    ;; Set up thread-atomical execution
	    (:locally (:movl ,(movitz::atomically-continuation-simple-pf 'fast-cons)
			     (:edi (:edi-offset atomically-continuation))))
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ecx)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :ecx)
	    (:jae '(:sub-program (allocation-failed)
		    (:int 113)))
	    (:movl :eax (:edx :ecx 2))
	    (:movl :ebx (:edx :ecx 6))
	    (:addl 8 :ecx)
	    (:movl :ecx (:edx 2))	; Commit allocation
	    (:leal (:edx :ecx -5) :edx)
	    ;; Exit thread-atomical
	    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	    (:movl :edx :eax)
	    (:ret))))
    (do-it)))


(defun trigger-full-newspace (free-space)
  "Make it so that there's only free-space words left before newspace is full."
  (let ((trigger (if (consp *gc-trigger*)
		     (pop *gc-trigger*)
		   *gc-trigger*)))
    (when trigger
      (macrolet
	  ((do-it ()
	     `(with-inline-assembly (:returns :nothing)
		(:compile-form (:result-mode :eax) (+ free-space trigger))
		(:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
		(:testl ,(logxor #xffffffff
				 (* #xfff movitz:+movitz-fixnum-factor+))
			:eax)
		(:jnz '(:sub-program () (:int 64)))
		(:addl 4 :eax)
		(:andl -8 :eax)
		(:movl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		       :ecx)
		(:subl :eax :ecx)
		(:movl (:edx 2) :ebx)
		(:movl :ecx (:edx 2))
		(:addl 8 :ebx)
	       fill-loop
		(:movl :edi (:edx :ebx -6))
		(:addl 4 :ebx)
		(:cmpl :ebx :ecx)
		(:ja 'fill-loop)
		)))
	(do-it)))))
  

(define-primitive-function los0-get-cons-pointer ()
  "Return in EAX the next object location with space for EAX words, with tag 6.
Preserve ECX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	   retry
	    (:locally (:cmpl 0 (:edi (:edi-offset atomically-continuation)))) ; Atomically?
	    (:je '(:sub-program ()
		   (:int 63)))		; This must be called inside atomically.
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :ebx)
	    (:leal (:ebx :eax 4) :eax)
	    (:andl -8 :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:ja '(:sub-program (probe-failed)
		   (:int 113)
		   (:int 63)))
	    (:leal (:edx :ebx 8) :eax)
	    (:movl :edi (:edx :ebx 8 ,movitz:+other-type-offset+))
	    (:ret))))
    (do-it)))

(define-primitive-function los0-cons-commit ()
  "Commit allocation of ECX/fixnum words.
Preserve EAX and EBX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	   retry
	    (:locally (:cmpl 0 (:edi (:edi-offset atomically-continuation)))) ; Atomically?
	    (:je '(:sub-program ()
		   (:int 63)))		; This must be called inside atomically.
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
  "Make u32 in ECX into a fixnum or bignum in EAX."
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :multiple-values)
	    (:cmpl ,movitz:+movitz-most-positive-fixnum+ :ecx)
	    (:ja 'not-fixnum)
	    (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
	    (:ret)
	   not-fixnum
	   retry-cons
	    (:locally (:movl ,(movitz::atomically-continuation-simple-pf 'box-u32-ecx)
			     (:edi (:edi-offset atomically-continuation))))
	    (:locally (:movl (:edi (:edi-offset nursery-space)) :edx))
	    (:movl (:edx 2) :eax)
	    (:cmpl (:edx ,(bt:slot-offset 'movitz:movitz-basic-vector 'movitz::num-elements))
		   :eax)
	    (:jae '(:sub-program ()
		    (:int 113)))
	    (:movl ,(dpb movitz:+movitz-fixnum-factor+
			 (byte 16 16) (movitz:tag :bignum 0))
		   (:edx :eax 2))
	    (:movl :ecx (:edx :eax 6))
	    (:addl 8 :eax)
	    (:movl :eax (:edx 2))	; Commit allocation
	    (:leal (:edx :eax) :eax)
	    ;; Exit thread-atomical
	    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
	    (:ret))))
    (do-it)))

(defvar *gc-stack*)

(defun install-los0-consing (&key (context (current-run-time-context))
				  (kb-size 1024)
				  duo-space)
  "Install the 'Los0' GC architecture on run-time-context CONTEXT.
Either use an explicitly provided DUO-SPACE, or allocate a fresh
duo-space where each space is KB-SIZE kilobytes."
  (setf (exception-handler 113)
    (lambda (exception interrupt-frame)
      (declare (ignore exception interrupt-frame))
      (without-interrupts
	(let ((*standard-output* *terminal-io*))
	  (when *gc-running*
	    (break "Recursive GC triggered."))
	  (let ((*gc-running* t))
	    (unless *gc-quiet*
	      (format t "~&;; GC.. "))
	    (stop-and-copy))
	  (if *gc-break*
	      (break "GC break.")
	    (loop			; This is  a nice opportunity to poll the keyboard..
	      (case (muerte.x86-pc.keyboard:poll-char)
		((#\esc)
		 (break "Los0 GC keyboard poll."))
		((nil)
		 (return)))))))))
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
      (install-primitive los0-cons-commit muerte::cons-commit))
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
  (check-type space (simple-array (unsigned-byte 32) 1))
  (and (typep object 'pointer)
       (<= (+ 2 (object-location space))
	   (object-location object)
	   (+ 1 (object-location space)
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

#+ignore
(defun tenure ()
  (install-old-consing)
  (install-los0-consing))

#+ignore
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
      (map-stack-words #'zap-oldspace nil (current-stack-frame))
      (initialize-space oldspace)
      (values))))


(defparameter *x* #4000())		; Have this in static space.
(defparameter *xx* #4000())		; Have this in static space.


(defun stop-and-copy (&optional evacuator)
  (setf (fill-pointer *x*) 0)
  (multiple-value-bind (newspace oldspace)
      (without-interrupts
	(let* ((space0 (%run-time-context-slot 'nursery-space))
	       (space1 (space-other space0)))
	  (check-type space0 vector-u32)
	  (check-type space1 vector-u32)
	  (assert (eq space0 (space-other space1)))
	  (assert (= 2 (space-fresh-pointer space1)))
	  (setf (%run-time-context-slot 'nursery-space) space1)
	  (values space1 space0)))
    ;; Evacuate-oldspace is to be mapped over every potential pointer.
    (let ((evacuator
	   (or evacuator
	       (lambda (x location)
		 "If x is in oldspace, migrate it to newspace."
		 (declare (ignore location))
		 (cond
		  ((null x)
		   nil)
		  ((not (object-in-space-p oldspace x))
		   x)
		  (t (or (and (eq (object-tag x)
				  (ldb (byte 3 0)
				       (memref (object-location x) 0 :type :unsigned-byte8)))
			      (let ((forwarded-x (memref (object-location x) 0)))
				(and (object-in-space-p newspace forwarded-x)
				     forwarded-x)))
			 (let ((forward-x (shallow-copy x)))
			   (when (and (typep x 'muerte::pointer)
				      *gc-consitency-check*)
			     (let ((a *x*))
			       (vector-push (%object-lispval x) a)
			       (vector-push (memref (object-location x) 0 :type :unsigned-byte32) a)
			       (assert (vector-push (%object-lispval forward-x) a))))
			   (setf (memref (object-location x) 0) forward-x)
			   forward-x))))))))
      ;; Scavenge roots
      (dolist (range muerte::%memory-map-roots%)
	(map-heap-words evacuator (car range) (cdr range)))
      (map-stack-words evacuator nil (current-stack-frame))
      ;; Scan newspace, Cheney style.
      (loop with newspace-location = (+ 2 (object-location newspace))
	  with scan-pointer = 2
	  as fresh-pointer = (space-fresh-pointer newspace)
	  while (< scan-pointer fresh-pointer)
	  do (map-heap-words evacuator
			     (+ newspace-location scan-pointer)
			     (+ newspace-location (space-fresh-pointer newspace)))
	     (setf scan-pointer fresh-pointer))

      ;; Consistency check..
      (when *gc-consitency-check*
	(without-interrupts
	  (let ((a *x*))
	    ;; First, restore the state of old-space
	    (do ((i 0 (+ i 3)))
		((>= i (length a)))
	      (let ((old (%lispval-object (aref a i)))
		    (old-class (aref a (+ i 1))))
		(setf (memref (object-location old) 0 :type :unsigned-byte32) old-class)))
	    ;; Then, check that each migrated object is equalp to its new self.
	    (do ((i 0 (+ i 3)))
		((>= i (length a)))
	      (let ((old (%lispval-object (aref a i)))
		    (new (%lispval-object (aref a (+ i 2)))))
		(unless (and (object-in-space-p newspace new)
			     (object-in-space-p oldspace old)
			     (objects-equalp old new))
		  (let ((*old* old)
			(*new* new)
			(*old-class* (aref a (+ i 1))))
		    (declare (special *old* *new* *old-class*))
		    (with-simple-restart (continue "Ignore failed GC consistency check.")
		      (error "GC consistency check failed:
old object: ~Z: ~S
new object: ~Z: ~S
oldspace: ~Z, newspace: ~Z, i: ~D"
			     old old new new oldspace newspace i))))))
	    (map-heap-words (lambda (x y)
			      (declare (ignore y))
			      (when (location-in-object-p (space-other (%run-time-context-slot 'nursery-space))
							  (object-location x))
				(break "Seeing old object in values-vector: ~Z" x))
			      x)
			    #x38 #xb8)
	    (let* ((stack (%run-time-context-slot 'muerte::nursery-space))
		   (stack-start (- (length stack) (muerte::current-control-stack-depth))))
	      (do ((i 0 (+ i 3)))
		  ((>= i (length a)))
		(when (find (aref a i) stack :start stack-start)
		  (break "Seeing old object ~S in current stack!"
			 (aref a i))))))))

      ;; GC completed, oldspace is evacuated.
      (unless *gc-quiet*
	(let ((old-size (truncate (- (space-fresh-pointer oldspace) 2) 2))
	      (new-size (truncate (- (space-fresh-pointer newspace) 2) 2)))
	  (format t "Old space: ~/muerte:pprint-clumps/, new space: ~
~/muerte:pprint-clumps/, freed: ~/muerte:pprint-clumps/.~%"
		  old-size new-size (- old-size new-size))))
      (initialize-space oldspace)
      (fill oldspace #x13 :start 2)
      (setf *gc-stack* (muerte::copy-current-control-stack))
      (setf (fill-pointer *xx*) (fill-pointer *x*))
      (replace *xx* *x*)))
  (values))


(defun find-object-by-location (location &key (continuep t) (breakp nil))
  "Scan the heap for a (pointer) object that matches location.
This is a debugging tool."
  (let ((results nil))
    (flet ((searcher (x ignore)
	     (declare (ignore ignore))
	     (when (and (typep x '(or muerte::tag1 muerte::tag6 muerte::tag7))
			(not (eq x (%run-time-context-slot 'muerte::nursery-space)))
			(location-in-object-p x location)
			(not (member x results)))
	       (push x results)
	       (funcall (if breakp #'break #'warn)
			"Found pointer ~Z of type ~S at location ~S."
			x (type-of x) (object-location x)))
	     x))
      (handler-bind
	  ((serious-condition (lambda (c)
				(when (and continuep
					   (find-restart 'muerte::continue-map-heap-words))
				  (warn "Automatic continue from scanning error: ~A" c)
				  (invoke-restart 'muerte::continue-map-heap-words)))))
	(dolist (range muerte::%memory-map-roots%)
	  (map-heap-words #'searcher (car range) (cdr range)))
	(let ((nursery (%run-time-context-slot 'muerte::nursery-space)))
	  (map-heap-words #'searcher
			  (+ 4 (object-location nursery))
			  (+ 4 (object-location nursery) (space-fresh-pointer nursery))))
	(map-stack-words #'searcher nil (current-stack-frame))))
    results))
