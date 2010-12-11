;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      inspect.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 24 09:50:41 2003
;;;;                
;;;; $Id: inspect.lisp,v 1.61 2008-04-02 20:49:44 ffjeld Exp $
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

(defun protect-unbound (x)
  (if (not (eq x (%run-time-context-slot nil 'new-unbound-value)))
      x
      (format nil "#<unbound #x~X>" (%object-lispval x))))

(defun stack-frame-funobj (stack frame)
  (stack-frame-ref stack frame -1))

(defun stack-location (stack index)
  (if (eq nil stack)
      index
    (+ (object-location stack) 2 index)))

(defun stack-frame-uplink (stack frame)
  (cond
   ((eq 0 frame) 0)
   ((eq 0 (stack-frame-funobj stack frame))
    (dit-frame-casf stack frame))
   (t (stack-frame-ref stack frame 0))))

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
	(cond
	 ((typep funobj 'function)
	  (let* ((code-vector (funobj-code-vector funobj))
		 (eip (stack-frame-ref stack frame 1 :unsigned-byte32))
		 (delta (- eip 8 (* #.movitz::+movitz-fixnum-factor+ (object-location code-vector)))))
	    (when (below delta (length code-vector))
	      (values delta code-vector funobj))))
	 ((eq 0 funobj)
	  (let* ((code-vector (symbol-value 'default-interrupt-trampoline))
		 (eip (stack-frame-ref stack frame 1 :unsigned-byte32))
		 (delta (- eip 8 (* #.movitz::+movitz-fixnum-factor+ (object-location code-vector)))))
	    (when (below delta (length code-vector))
	      (values delta code-vector funobj)))))))))

(defun stack-frame-ref (stack frame index &optional (type ':lisp))
  "If stack is provided, stack-frame is an index into that stack vector.
Otherwise, stack-frame is an absolute location."
  (cond
   ((not (null stack))
    (check-type stack stack-vector)
    (let ((pos (+ frame index)))
      (assert (< -1 pos (length stack))
	  () "Index ~S, pos ~S, len ~S" index pos (length stack))
      (memref stack (+ 2 (* 4 pos)) :type type)))
   (t (memref frame (* 4 index) :type type))))

(defun (setf stack-frame-ref) (value stack frame index &optional (type ':lisp))
  (cond
   ((not (eq nil stack))
    (check-type stack stack-vector)
    (let ((pos (+ frame index)))
      (assert (< -1 pos (length stack))
	  () "Index ~S, pos ~S, len ~S" index pos (length stack))
      (setf (memref stack 2 :index pos :type type) value)))
   (t (setf (memref frame 0 :index index :type type) value))))

(defun current-dynamic-context ()
  (with-inline-assembly (:returns :eax)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :eax))))

(defun dynamic-context-uplink (dynamic-context)
  (stack-frame-ref nil dynamic-context 3 :lisp))

(defun dynamic-context-tag (dynamic-context)
  (stack-frame-ref nil dynamic-context 1 :lisp))

(defun stack-index-frame (stack index start-frame)
  "Find the frame in which index is included."
  (do ((frame start-frame (stack-frame-uplink stack frame)))
      ((eq 0 frame) nil)
    (when (< index frame)
      (return frame))))

(defmacro with-each-dynamic-context ((&optional start-context result) &rest clauses)
  "Only use this if you know what you're doing. See run-time.lisp."
  (let ((context (gensym "dynamic-context-"))
	(tag (gensym "dynamic-tag-"))
	(name (gensym "dynamic-name-"))
	(bind-clause (find :binding clauses :key #'caar))
	(catch-clause (find :catch clauses :key #'caar))
        (lcatch-clause (find :lexical-catch clauses :key #'caar))
	(up-clause (find :unwind-protect clauses :key #'caar))
	(basic-restart-clause (find :basic-restart clauses :key #'caar)))
    `(do ((,context ,(if start-context start-context '(current-dynamic-context))
		    (dynamic-context-uplink ,context)))
	 ((not (plusp ,context)) ,result)
       (let ((,tag (dynamic-context-tag ,context))
	     (,name (stack-frame-ref nil ,context 0 :lisp)))
	 (declare (ignorable ,name))
	 (cond
	  ,@(when bind-clause
	      `(((symbolp ,name)
		 (multiple-value-bind ,(cdar bind-clause)
		     (values ,context
			     (stack-frame-ref nil ,context 0 :lisp)
			     (stack-frame-ref nil ,context 2 :lisp)
                             (stack-frame-ref nil ,context 1 :lisp))
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
          ,@(when lcatch-clause
                  `(((eq ,tag (load-global-constant unbound-function))
                     (multiple-value-bind ,(cdar lcatch-clause)
                         (values ,context)
                       ,@(rest lcatch-clause)))))
	  ,@(when catch-clause
	      `((t (multiple-value-bind ,(cdar catch-clause)
		       (values ,context ,tag)
		     ,@(rest catch-clause))))))))))


(defun print-dynamic-context (&key
                              (types '(:restart :binding :catch :unwind-protect :lexical-catch) types-p)
                              variables (spartan t) (show-functions t))
  (when (and variables (not types-p))
    (setf types '(:binding)))
  (let ((format-values (if spartan "~Z" "~S"))
        (last-frame nil))
    (flet ((info (context type format &rest args)
             (when (member type types)
               (let ((frame (stack-index-frame nil context (current-stack-frame))))
                 (when (and show-functions frame (not (eq frame last-frame)))
                   (setf last-frame frame)
                   (format t "~&  [[[in ~A]]]~%" (stack-frame-funobj nil frame))))
               (format t "~&[~8,'0X] " context)
               (apply #'format t format args))))
      (with-each-dynamic-context ()
        ((:basic-restart context name)
         (info context :basic-restart
               "restart: ~S fmt: ~S/~S [#x~X]"
               name (rc-format context) (rc-args context) context))
        ((:binding context name value scratch)
         (when (or (null variables)
                   (member name variables))
           (info context :binding "bind: ~S => ~@? [scratch: ~@?]"
                 name format-values value format-values scratch)))
        ((:unwind-protect context)
         (info context :unwind-protect "unwind-protect"))
        ((:lexical-catch context tag)
         (info context :lexical-catch "lexical-catch" tag tag))
        ((:catch context tag)
         (info context :catch "catch: ~Z: ~S" tag tag))))))

(define-compiler-macro %location-object (&environment env location tag)
  (assert (movitz:movitz-constantp tag env))
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,location)
     (:addl ,tag :eax)))

(defun %find-code-vector (location &optional (stop-location (if (< location #x2000)
								0
							      (- location #x2000))))
  "Find the code-vector that holds a location by searching for a code-vector object header."
  (do ((l (logand location -2) (- l 2)))
      ((< l stop-location)
       (error "Unable to find code-vector for location ~S." location))
    (when (and (= (memref l 0 :type :unsigned-byte16)
		  #.(movitz:basic-vector-type-tag :code))
	       ;; If the vector has a fill-pointer, it should be equal to the length.
	       (multiple-value-bind (len len-tag)
		   (memref l 4 :type :signed-byte30+2)
		 (and (= 0 len-tag)
		      (typecase len
			((integer 0 #x3fff)
			 (= len (memref l 2 :type :unsigned-byte14)))
			(positive-fixnum t)
			(t nil)))))
      (let ((code-vector (%location-object l 6)))
	(check-type code-vector code-vector)
	(assert (location-in-object-p code-vector location))
	(return code-vector)))))

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
    (:movl :edx :ecx)))

(defun %shallow-copy-non-pointer-object (object word-count)
  "Copy any object with size word-count."
  (check-type word-count (integer 2 *))
  (with-non-pointer-allocation-assembly (word-count
					 :object-register :eax
					 :size-register :ecx)
    (:load-lexical (:lexical-binding object) :ebx)
    (:load-lexical (:lexical-binding word-count) :edx)
    (:xorl :esi :esi)			; counter
    copy-loop
    (:movl (:ebx :esi #.movitz:+other-type-offset+) :ecx)
    (:movl :ecx (:eax :esi #.movitz:+other-type-offset+))
    (:addl 4 :esi)
    (:cmpl :esi :edx)
    (:jne 'copy-loop)
    (:movl (:ebp -4) :esi)
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
     (shallow-copy-vector old))
    (function
     (copy-funobj old))
    (structure-object
     (copy-structure old))
    (ratio
     (%make-ratio (%ratio-numerator old)
                  (%ratio-denominator old)))
    (run-time-context
     (%shallow-copy-object old (movitz-type-word-size 'movitz-run-time-context)))))

(defun objects-equalp (x y &optional (limit 20))
  "Basically, this verifies whether x is a shallow-copy of y, or vice versa."
  (assert (not (with-inline-assembly (:returns :boolean-zf=1)
		 (:load-lexical (:lexical-binding x) :eax)
		 (:cmpl #x13 :eax)))
      (x) "Checking illegal ~S for object-equalp." x)
  (or (= 0 (decf limit))
      (eql x y)
      (cond
       ((not (objects-equalp (class-of x) (class-of y) limit))
	nil)
       ((not (and (typep x 'pointer)
		  (typep y 'pointer)))
	nil)
       (t (macrolet ((test (accessor &rest args)
		       `(objects-equalp (,accessor x ,@args)
					(,accessor y ,@args)
                                        limit)))
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
	       (and (test memref (movitz-type-slot-offset 'movitz-symbol 'function-value))
		    (test memref (movitz-type-slot-offset 'movitz-symbol 'name))
		    (test memref (movitz-type-slot-offset 'movitz-symbol 'flags))))
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
		    (test std-instance-slots)))
	      (run-time-context
	       (and (typep y 'run-time-context)
		    (test %run-time-context-slot 'slots)
		    (test %run-time-context-slot 'class)))))))))

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
	   (+ -1 object-location (movitz-type-word-size :movitz-symbol))))
      (run-time-context
       (<= object-location
	   location
	   (+ -1 object-location (movitz-type-word-size :movitz-run-time-context))))
      (std-instance
       (<= object-location
	   location
	   (+ -1 object-location (movitz-type-word-size :movitz-std-instance))))
      (function
       (<= object-location
	   location
	   (+ -1 object-location
	      (movitz-type-word-size :movitz-funobj)
	      (funobj-num-constants object))))
      ((or string
	   code-vector
	   (simple-array (unsigned-byte 8) 1))
       (<= object-location
	   location
	   (+ -1 object-location
	      (movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (array-dimension object 0) 7) 8)))))
      ((simple-array (unsigned-byte 16) 1)
       (<= object-location
	   location
	   (+ -1 object-location
	      (movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (array-dimension object 0) 3) 4)))))
      ((or simple-vector
	   (simple-array (unsigned-byte 32) 1)
	   stack-vector)
       (<= object-location
	   location
	   (+ -1 object-location
	      (movitz-type-word-size 'movitz-basic-vector)
	      (* 4 (truncate (+ (array-dimension object 0) 3) 4)))))
      (structure-object
       (<= object-location
	   location
	   (+ -1 object-location
	      (movitz-type-word-size :movitz-struct)
	      (* 4 (truncate (+ (array-dimension object 0) 3) 4))))))))

(defun location-in-code-vector-p%unsafe (code-vector location)
  (and (<= (object-location code-vector) location)
       (<= location
	   (+ -1 (object-location code-vector)
	      (movitz-type-word-size 'movitz-basic-vector)
	      (* 2 (truncate (+ (memref code-vector
					(movitz-type-slot-offset 'movitz-basic-vector 'num-elements))
				7)
			     8))))))

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
      (let ((uplink (stack-frame-uplink nil frame))
	    (copy-frame (- frame start-frame)))
	(unless (= 0 uplink)
	  (setf (stack-frame-ref copy copy-frame 0 :lisp)
	    (- uplink start-frame))
	  (unless (= 0 copy-frame)	; first frame has only uplink.
	    ;; Now, make any raw stack-pointers into relative indexes.
	    ;; XXX TODO: The dynamic-env list.
	    (case (stack-frame-funobj copy copy-frame)
	      (0 (let ((ebp (dit-frame-ref nil frame :ebp)))
		   (setf (dit-frame-ref copy copy-frame :ebp)
		     (etypecase ebp
		       (fixnum (- ebp start-frame))
		       (null nil))))
		 (let ((ac (dit-frame-ref copy copy-frame
					  :atomically-continuation
					  :location)))
		   (when (and (/= 0 ac)
			      (= 0 (ldb (byte 2 0)
					(dit-frame-ref copy copy-frame
						       :atomically-continuation
						       :unsigned-byte8))))
		     (setf (dit-frame-ref copy copy-frame :atomically-continuation)
		       (- ac start-frame))))))))
	(setf frame uplink)))
    copy))
