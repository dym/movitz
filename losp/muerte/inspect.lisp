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
;;;; $Id: inspect.lisp,v 1.40 2004/09/22 17:39:04 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/inspect)

(in-package muerte)

(define-global-variable %memory-map%
    '((0 . #x80000))			; 0-2 MB
  "This is a list of the active memory ranges. Each element is a cons-cell
where the car is the start-location and the cdr the end-location.
A 'location' is a fixnum interpreted as a pointer (i.e. the pointer value
with the lower two bits masked off).
This variable should be initialized during bootup initialization.")

(defvar %memory-map-roots% '((0 . #x80000))
  "The memory-map that is to be scanned for pointer roots.")

(define-compiler-macro check-stack-limit ()
  `(with-inline-assembly (:returns :nothing)
     (:locally (:bound (:edi (:edi-offset stack-bottom)) :esp))))

(defun check-stack-limit ()
  (declare (without-check-stack-limit))	; we do it explicitly..
  (check-stack-limit))

(defun stack-frame-funobj (stack frame)
  (stack-frame-ref stack frame -1))

(defun stack-frame-uplink (stack frame)
  (if (eq 0 (stack-frame-funobj stack frame))
      (dit-frame-casf stack frame)
    (stack-frame-ref stack frame 0)))

(define-compiler-macro current-stack-frame ()
  `(with-inline-assembly (:returns :eax)
     (:leal ((:ebp ,(truncate movitz::+movitz-fixnum-factor+ 4)))
	    :eax)))

(defun current-stack-frame ()
  (stack-frame-uplink nil (current-stack-frame)))

(defun stack-frame-call-site (stack frame)
  "Return the code-vector and offset into this vector that is immediately
after the point that called this stack-frame."
  (let ((uplink (stack-frame-uplink stack frame)))
    (when (and uplink (not (= 0 uplink)))
      (let ((funobj (stack-frame-funobj stack uplink)))
	(when (typep funobj 'function)
	  (let* ((code-vector (funobj-code-vector funobj))
		 (eip (stack-frame-ref stack frame 1 :unsigned-byte32))
		 (delta (- eip 8 (* #.movitz::+movitz-fixnum-factor+ (object-location code-vector)))))
	    (when (below delta (length code-vector))
	      (values delta code-vector funobj))))))))

(defun stack-frame-ref (stack frame index &optional (type ':lisp))
  "If stack is provided, stack-frame is an index into that stack vector.
Otherwise, stack-frame is an absolute location."
  (cond
   ((not (null stack))
    (check-type stack (simple-array (unsigned-byte 32) 1))
    (let ((pos (+ frame index)))
      (assert (< -1 pos (length stack))
	  () "Index ~S, pos ~S, len ~S" index pos (length stack))
      (memref stack 2 pos type)))
   (t (memref frame 0 index type))))

(defun (setf stack-frame-ref) (value stack frame index &optional (type ':lisp))
  (cond
   ((not (eq nil stack))
    (check-type stack (simple-array (unsigned-byte 32) 1))
    (let ((pos (+ frame index)))
      (assert (< -1 pos (length stack))
	  () "Index ~S, pos ~S, len ~S" index pos (length stack))
      (setf (memref stack 2 pos type) value)))
   (t (setf (memref frame 0 index type) value))))

(defun current-dynamic-context ()
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :eax))))

(defun dynamic-context-uplink (dynamic-context)
  (stack-frame-ref nil dynamic-context 3 :lisp))

(defun dynamic-context-tag (dynamic-context)
  (stack-frame-ref nil dynamic-context 1 :lisp))

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
	 ((not (plusp ,context)) ,result)
       (let ((,tag (dynamic-context-tag ,context)))
	 (cond
	  ,@(when bind-clause
	      `(((eq ,tag (load-global-constant unbound-value))
		 (multiple-value-bind ,(cdar bind-clause)
		     (values ,context
			     (stack-frame-ref nil ,context 0 :lisp)
			     (stack-frame-ref nil ,context 2 :lisp))
		   ,@(rest bind-clause)))))
	  ,@(when up-clause
	      `(((eq ,tag (load-global-constant unwind-protect-tag))
		 (multiple-value-bind ,(cdar up-clause)
		     (values ,context)
		   ,@(rest up-clause)))))
	  ,@(when basic-restart-clause
	      `(((eq ,tag (load-global-constant restart-tag))
		 (macrolet ((rc-function (c) `(stack-frame-ref nil ,c -2 :lisp))
			    (rc-interactive (c) `(stack-frame-ref nil ,c -3 :lisp))
			    (rc-test (c) `(stack-frame-ref nil ,c -4 :lisp))
			    (rc-format (c) `(stack-frame-ref nil ,c -5 :lisp))
			    (rc-args (c) `(stack-frame-ref nil ,c -6 :lisp)))
		   (multiple-value-bind ,(cdar basic-restart-clause)
		       (values ,@(subseq `(,context
					   (stack-frame-ref nil ,context -1 :lisp)) ; name
					 0 (length (cdar basic-restart-clause))))
		     ,@(rest basic-restart-clause))))))
	  ,@(when catch-clause
	      `((t (multiple-value-bind ,(cdar catch-clause)
		       (values ,context ,tag)
		     ,@(rest catch-clause))))))))))

(defun pdc (&rest types)
  (declare (dynamic-extent types))
  (let ((types (or types '(:restarts :bindings :catch))))
    (with-each-dynamic-context ()
      ((:basic-restart context name)
       (when (member :restarts types)
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


(defun malloc-pointer-words (words)
  (check-type words (integer 2 *))
  (with-allocation-assembly (words :fixed-size-p t
				   :object-register :eax
				   :size-register :ecx)
    (:load-lexical (:lexical-binding words) :ecx)
;;;    (:leal (:eax :ecx #.movitz:+other-type-offset+) :edx)
;;;    (:testb 3 :dl)
;;;    (:jnz '(:sub-program () (:int 63)))
    (:movl :edi (:eax :ecx #.movitz:+other-type-offset+))))

(defun %shallow-copy-object (object word-count)
  "Copy any object with size word-count."
  (check-type word-count (integer 2 *))
  (with-allocation-assembly (word-count
			     :object-register :eax
			     :size-register :ecx)
    (:load-lexical (:lexical-binding object) :ebx)
    (:load-lexical (:lexical-binding word-count) :edx)
    (:xorl :esi :esi)			; counter
    (:addl 4 :edx)
    (:andl -8 :edx)
    copy-loop
    (:movl (:ebx :esi #.movitz:+other-type-offset+) :ecx)
    (:movl :ecx (:eax :esi #.movitz:+other-type-offset+))
    (:addl 4 :esi)
    (:cmpl :esi :edx)
    (:jne 'copy-loop)
    (:movl (:ebp -4) :esi)
;;;    ;; Copy tag from EBX onto EAX
;;;    (:movl :ebx :ecx)
;;;    (:andl 7 :ecx)
;;;    (:andl -8 :eax)
;;;    (:orl :ecx :eax)
    ;; Load word-count into ECX
    (:movl :edx :ecx)))

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
     (let ((new (make-array (array-dimension old 0)
			    :element-type (array-element-type old)
			    :initial-contents old)))
       (when (array-has-fill-pointer-p old)
	 (setf (fill-pointer new) (fill-pointer old)))
       new))
    (function
     (copy-funobj old))
    (structure-object
     (copy-structure old))))

(defun objects-equalp (x y)
  "Basically, this verifies whether x is a shallow-copy of y, or vice versa."
  (assert (not (with-inline-assembly (:returns :boolean-zf=1)
		 (:load-lexical (:lexical-binding x) :eax)
		 (:cmpl #x13 :eax)))
      (x) "Checking illegal ~S for object-equalp." x)
  (or (eql x y)
      (cond
       ((not (objects-equalp (class-of x) (class-of y)))
	nil)
       ((not (and (typep x 'pointer)
		  (typep y 'pointer)))
	nil)
       (t (macrolet ((test (accessor &rest args)
		       `(objects-equalp (,accessor x ,@args)
					(,accessor y ,@args))))
	    (typecase x
	      (bignum
	       (= x y))
	      (function
	       (and (test funobj-code-vector)
		    (test funobj-code-vector%1op)
		    (test funobj-code-vector%2op)
		    (test funobj-code-vector%3op)
		    (test funobj-lambda-list)
		    (test funobj-name)
		    (test funobj-num-constants)
		    (test funobj-num-jumpers)
		    (dotimes (i (funobj-num-constants x) t)
		      (unless (test funobj-constant-ref i)))))
	      (symbol
	       (and (test memref #.(bt:slot-offset 'movitz:movitz-symbol 'movitz::function-value)
			  0 :lisp)
		    (test memref #.(bt:slot-offset 'movitz:movitz-symbol 'movitz::name)
			  0 :lisp)
		    (test memref #.(bt:slot-offset 'movitz:movitz-symbol 'movitz::flags)
			  0 :lisp)))
	      (vector
	       (and (typep y 'vector)
		    (test array-element-type)
		    (every #'objects-equalp x y)))
	      (cons
	       (and (typep y 'cons)
		    (test car)
		    (test cdr)))
	      (structure-object
	       (and (typep y 'structure-object)
		    (test structure-object-class)
		    (test structure-object-length)
		    (dotimes (i (structure-object-length x) t)
		      (unless (test structure-ref i)
			(return nil)))))
	      (std-instance
	       (and (typep y 'std-instance)
		    (test std-instance-class)
		    (test std-instance-slots)))))))))

(define-compiler-macro %lispval-object (integer &environment env)
  "Return the object that is wrapped in the 32-bit integer lispval."
  (if (movitz:movitz-constantp integer env)
      (let ((word (movitz:movitz-eval integer env)))
	(check-type word (unsigned-byte 32))
	`(with-inline-assembly (:returns :register)
	   (:movl ,word (:result-register))))
    `(with-inline-assembly (:returns :register)
       (:compile-form (:result-mode :eax) ,integer)
       (:call-global-pf unbox-u32)
       (:movl :ecx (:result-register)))))

(defun %lispval-object (integer)
  "Return the object that is wrapped in the 32-bit integer lispval."
  (compiler-macro-call %lispval-object integer))

(define-compiler-macro %object-lispval (object &environment env)
  "Return the integer lispval that corresponds to object.
Obviously, this correspondence is not guaranteed to hold e.g. across GC."
  (if (movitz:movitz-constantp object env)
      (movitz:movitz-intern (movitz:movitz-read (movitz:movitz-eval object env)) 'word)
    `(with-inline-assembly (:returns :eax)
       (:compile-form (:result-mode :eax) ,object)
       (:movl :eax :ecx)
       (:call-local-pf box-u32-ecx))))

(defun %object-lispval (object)
  "Return the integer lispval that corresponds to object.
Obviously, this correspondence is not guaranteed to hold e.g. across GC."
  (compiler-macro-call %object-lispval object))

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
	   (+ -1 object-location #.(movitz::movitz-type-word-size :movitz-run-time-context))))
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

(defun current-control-stack-depth (&optional (start-frame (current-stack-frame)))
  "How deep is the stack currently?"
  (do ((frame start-frame (stack-frame-uplink nil frame)))
      ((eq 0 (stack-frame-uplink nil frame))
       (1+ (- frame start-frame)))))

(defun copy-current-control-stack (&optional (start-frame (current-stack-frame)))
  (let ((copy (make-array (current-control-stack-depth start-frame)
			  :element-type '(unsigned-byte 32))))
    (dotimes (i (length copy))
      (setf (stack-frame-ref copy i 0 :unsigned-byte32)
	(stack-frame-ref nil start-frame i :unsigned-byte32)))
    (do ((frame start-frame))
	((eq 0 frame))
      (let ((uplink (stack-frame-uplink nil frame)))
	(setf (stack-frame-ref copy 0 (- frame start-frame) :lisp)
	  (if (eql 0 uplink)
	      0
	    (- uplink start-frame)))
	(setf frame uplink)))
    copy))
