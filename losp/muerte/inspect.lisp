;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      inspect.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 24 09:50:41 2003
;;;;                
;;;; $Id: inspect.lisp,v 1.20 2004/07/13 22:42:38 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/inspect)

(in-package muerte)

(define-compiler-macro check-stack-limit ()
  `(with-inline-assembly (:returns :nothing)
     (:locally (:bound (:edi (:edi-offset stack-bottom)) :esp))))

(defun check-stack-limit ()
  (declare (without-check-stack-limit))	; we do it explicitly..
  (check-stack-limit))

(defun stack-top ()
  (declare (without-check-stack-limit))
  (load-global-constant stack-top :thread-local t))

(defun stack-bottom ()
  (declare (without-check-stack-limit))
  (load-global-constant stack-bottom :thread-local t))

(defun (setf stack-top) (value)
  (declare (without-check-stack-limit))
  (check-type value fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) value)
    ((:fs-override) :movl :eax (:edi #.(movitz::global-constant-offset 'stack-top)))))


(defun (setf stack-bottom) (value)
  (declare (without-check-stack-limit))
  (check-type value fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) value)
    ((:fs-override) :movl :eax (:edi #.(movitz::global-constant-offset 'stack-bottom)))))


(defun stack-frame-uplink (stack-frame)
  (values (truncate (stack-ref (* 4 stack-frame) 0 0 :unsigned-byte32)
		    4)))

(define-compiler-macro current-stack-frame ()
  `(with-inline-assembly (:returns :eax)
     (:leal ((:ebp ,(truncate movitz::+movitz-fixnum-factor+ 4)))
	    :eax)))

(defun current-stack-frame ()
  (stack-frame-uplink (current-stack-frame)))

(defun stack-frame-funobj (stack-frame &optional accept-non-funobjs)
  (when stack-frame
    (let ((x (stack-frame-ref stack-frame -1)))
      (and (or accept-non-funobjs
	       (typep x 'function))
	   x))))

(defun stack-frame-call-site (stack-frame)
  "Return the code-vector and offset into this vector that is immediately
after the point that called this stack-frame."
  (let ((funobj (stack-frame-funobj (stack-frame-uplink stack-frame))))
    (when funobj
      (let* ((code-vector (funobj-code-vector funobj))
	     (x (stack-ref (* 4 stack-frame) 0 1 :unsigned-byte32))
	     (delta (- x 8 (* #.movitz::+movitz-fixnum-factor+ (object-location code-vector)))))
	(when (below delta (length code-vector))
	  (values delta code-vector funobj))))))

(defun stack-frame-ref (stack-frame index)
  (if (= 0 index)
      (stack-frame-uplink stack-frame)
    (stack-ref (* 4 stack-frame) 0 index :lisp)))

(defun stack-ref-p (pointer)
  (let ((top (load-global-constant-u32 stack-top))
	(bottom (with-inline-assembly (:returns :eax)
		  (:movl :esp :eax)
		  (:shll #.movitz:+movitz-fixnum-shift+ :eax))))
    (<= bottom pointer top)))

(defun stack-ref (pointer offset index type)
  (assert (stack-ref-p pointer) (pointer)
    "Stack pointer not in range: #x~X" pointer)
  (memref-int pointer offset index type))

(defun current-dynamic-context ()
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))))

(defun dynamic-context-uplink (dynamic-context)
  (stack-ref dynamic-context 12 0 :unsigned-byte32))

(defun dynamic-context-tag (dynamic-context)
  (stack-ref dynamic-context 4 0 :lisp))

(defmacro with-each-dynamic-context ((&optional start-context result) &rest clauses)
  "Only use this if you know what you're doing. See run-time.lisp."
  (let ((context (gensym "dynamic-context-"))
	(tag (gensym "dynamic-tag-"))
	(bind-clause (find :binding clauses :key #'caar))
	(catch-clause (find :catch clauses :key #'caar))
	(up-clause (find :unwind-protect clauses :key #'caar))
	(basic-restart-clause (find :basic-restart clauses :key #'caar)))
    `(do ((,context ,(if start-context start-context '(current-dynamic-context))
		    (dynamic-context-uplink ,context)))
	 ((not (stack-ref-p ,context)) ,result)
       (let ((,tag (dynamic-context-tag ,context)))
	 (cond
	  ,@(when bind-clause
	      `(((eq ,tag (load-global-constant unbound-value))
		 (multiple-value-bind ,(cdar bind-clause)
		     (values ,context
			     (stack-ref ,context 0 0 :lisp)
			     (stack-ref ,context 8 0 :lisp))
		   ,@(rest bind-clause)))))
	  ,@(when up-clause
	      `(((eq ,tag (load-global-constant unwind-protect-tag))
		 (multiple-value-bind ,(cdar up-clause)
		     (values ,context)
		   ,@(rest up-clause)))))
	  ,@(when basic-restart-clause
	      `(((eq ,tag (load-global-constant restart-tag))
		 (macrolet ((rc-function (c) `(stack-ref ,c 0 -2 :lisp))
			    (rc-interactive (c) `(stack-ref ,c 0 -3 :lisp))
			    (rc-test (c) `(stack-ref ,c 0 -4 :lisp))
			    (rc-format (c) `(stack-ref ,c 0 -5 :lisp))
			    (rc-args (c) `(stack-ref ,c 0 -6 :lisp)))
		   (multiple-value-bind ,(cdar basic-restart-clause)
		       (values ,@(subseq `(,context
					   (stack-ref ,context 0 -1 :lisp)) ; name
					 0 (length (cdar basic-restart-clause))))
		     ,@(rest basic-restart-clause))))))
	  ,@(when catch-clause
	      `((t (multiple-value-bind ,(cdar catch-clause)
		       (values ,context ,tag)
		     ,@(rest catch-clause))))))))))

#+ignore
(defun pdc (&rest types)
  (declare (dynamic-extent types))
  (let ((types (or types '(:restarts :bindings :catch))))
    (with-each-dynamic-context ()
      ((:basic-restart context name)
       (when (member :restart types)
	 (format t "~&restart: ~S fmt: ~S/~S [#x~X]" name
		 (rc-format context)
		 (rc-args context)
		 context)))
      ((:binding context name value)
       (declare (ignore context))
       (when (member :bindings types)
	 (format t "~&bind:    ~S => ~Z" name value)))
      ((:catch context tag)
       (declare (ignore context))
       (when (member :catch types)
	 (format t "~&catch:   ~Z: ~S" tag tag))))))

(defun shallow-copy (old)
  "Allocate a new object that is similar to the old one."
  (etypecase old
    (cons
     (cons (car old) (cdr old)))
    (bignum
     (copy-bignum old))
    (std-instance
     (allocate-std-instance (std-instance-class old)
			    (std-instance-slots old)))
    (symbol
     (copy-symbol old t))
    (vector
     (make-array (array-dimension old 0)
		 :element-type (array-element-type old)
		 :initial-contents old
		 :fill-pointer (fill-pointer old)))
    (function
     (copy-funobj old))
    (structure-object
     (copy-structure old))))

(defun malloc-clumps (clumps)
  "Allocate general-purpose memory, i.e. including pointers.
The unit clump is 8 bytes, or two words."
  (let ((x (with-inline-assembly (:returns :eax :side-effects t)
	     (:compile-form (:result-mode :ebx) clumps)
	     (:shll 1 :ebx)
	     (:globally (:call (:edi (:edi-offset malloc))))
	     (:addl #.(movitz::tag :other) :eax)
	     (:xorl :ecx :ecx)
	    reset-loop
	     (:movl :edi (:eax :ecx -6))
	     (:addl 4 :ecx)
	     (:cmpl :ecx :ebx)
	     (:jae 'reset-loop))))
    #+ignore
    (dotimes (i (* 2 clumps))
      (setf (memref x -6 i :lisp) nil))
    x))

(defun malloc-data-clumps (clumps)
  "Allocate memory for non-pointer data (i.e. doesn't require initialization)."
  ;; Never mind, this is the stupid default implementation.
  (malloc-clumps clumps))

(defun malloc-words (words)
  "Allocate space for at least (+ 2 words) cells/words."
  (malloc-clumps (1+ (truncate (1+ words) 2))))

(defun malloc-data-words (words)
  (malloc-data-clumps (1+ (truncate (1+ words) 2))))

(defun location-in-object-p (object location)
  "Is location inside object?"
  (let ((object-location (object-location object)))
    (etypecase object
      ((or number null character)
       nil)
      (cons
       (<= object-location
	   location
	   (+ object-location 1)))
      (symbol
       (<= object-location
	   location
	   (+ -1 object-location #.(movitz::movitz-type-word-size :movitz-symbol))))
      (run-time-context
       (<= object-location
	   location
	   (+ -1 object-location #.(movitz::movitz-type-word-size :movitz-constant-block))))
      (std-instance
       (<= object-location
	   location
	   (+ -1 object-location #.(movitz::movitz-type-word-size :movitz-std-instance))))
      (function
       (<= object-location
	   location
	   (+ -1 object-location
	      #.(movitz::movitz-type-word-size :movitz-funobj)
	      (funobj-num-constants object))))
      ((or string code-vector (simple-array (unsigned-byte 8) 1))
       (<= object-location
	   location
	   (+ -1 object-location
	      #.(movitz::movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (array-dimension object 0) 7) 8)))))
      (vector-u16
       (<= object-location
	   location
	   (+ -1 object-location
	      #.(movitz::movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (array-dimension object 0) 3) 4)))))
      ((or vector-u32 simple-vector)
       (<= object-location
	   location
	   (+ -1 object-location
	      #.(movitz::movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (array-dimension object 0) 1) 2)))))
      (structure-object
       (<= object-location
	   location
	   (+ -1 object-location
	      #.(movitz::movitz-type-word-size :movitz-struct)
	      (* 2 (truncate (+ (structure-object-length object) 1) 2))))))))

(defun %bignum-bigits (x)
  (%bignum-bigits x))

(defun %bignum-canonicalize (x)
  "Assuming x is a bignum, return the canonical integer value. That is,
either return a fixnum, or destructively modify the bignum's length so
that the msb isn't zero. DO NOT APPLY TO NON-BIGNUM VALUES!"
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    (:load-lexical (:lexical-binding x) :eax)
	    (:movl (:eax ,movitz:+other-type-offset+) :ecx)
	    (:shrl 16 :ecx)
	   shrink-loop
	    (:cmpl ,movitz:+movitz-fixnum-factor+ :ecx)
	    (:je 'shrink-no-more)
	    (:cmpl 0 (:eax :ecx ,(+ -4 (bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0))))
	    (:jnz 'shrink-done)
	    (:subl ,movitz:+movitz-fixnum-factor+ :ecx)
	    (:jmp 'shrink-loop)
	   shrink-no-more
	    (:cmpl ,(1+ movitz:+movitz-most-positive-fixnum+)
		   (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0)))
	    (:jc '(:sub-program (fixnum-result)
		   (:movl (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::bigit0))
		    :ecx)
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
		   (:jmp 'done)))
	   shrink-done
	    (:testb 3 :cl)
	    (:jnz '(:sub-program () (:int 59)))
	    (:movw :cx (:eax ,(bt:slot-offset 'movitz:movitz-bignum 'movitz::length)))
	   done
	    )))
    (do-it)))

(defun copy-bignum (old)
  (check-type old bignum)
  (let* ((length (%bignum-bigits old))
	 (new (malloc-data-clumps (1+ (truncate length 2)))))
    (with-inline-assembly (:returns :eax)
      (:compile-two-forms (:eax :ebx) new old)
      (:compile-form (:result-mode :edx) length)
     copy-bignum-loop
      (:movl (:ebx :edx #.movitz:+other-type-offset+) :ecx)
      (:movl :ecx (:eax :edx #.movitz:+other-type-offset+))
      (:subl 4 :edx)
      (:jnc 'copy-bignum-loop))))

(defun print-bignum (x)
  (check-type x bignum)
  (dotimes (i (1+ (%bignum-bigits x)))
    (format t "~8,'0X " (memref x -6 i :unsigned-byte32)))
  (terpri)
  (values))
