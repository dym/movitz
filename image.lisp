;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001,2000, 2002-2005,
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;; Filename:      image.lisp
;;;; Description:   Construction of Movitz images.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Oct 22 00:22:43 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: image.lisp,v 1.126 2008-07-18 13:15:40 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(define-binary-class movitz-run-time-context (movitz-heap-object)
  ((run-time-context-start :binary-type :label) ; keep this at the top.
   (type
    :binary-type other-type-byte
    :initform :run-time-context)
   (padding
    :binary-type 3)
   (atomically-continuation
    :binary-type lu32
    :initform 0)
   (raw-scratch0			; A non-GC-root scratch register
    :binary-type lu32
    :initform 0)
   (pointer-start :binary-type :label)
   (ret-trampoline
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (cons-commit
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (cons-non-pointer
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (cons-commit-non-pointer
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (cons-non-header
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (cons-commit-non-header
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)

   (cons-pointer
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   ;; tag-specific class-of primitive-functions
   (fast-class-of :binary-type :label)
   (fast-class-of-even-fixnum		; 0000
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-cons			; 1111
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-character		; 2222
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-tag3			; 3333
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-odd-fixnum		; 4444
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-null			; 5555
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-other			; 6666
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-class-of-symbol		; 7777
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)

   (keyword-search
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function
    :binary-type code-vector-word)
   (decode-keyargs-default
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function
    :binary-type code-vector-word)
   (decode-keyargs-foo
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function
    :binary-type code-vector-word)
   
   (fast-car
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-cdr
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-cddr
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-car-ebx
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-cdr-ebx
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   ;; primitive functions global constants
   (pop-current-values
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (dynamic-variable-lookup
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (dynamic-variable-store
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (dynamic-unwind-next
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (dynamic-variable-install
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (dynamic-variable-uninstall
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (assert-1arg
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (assert-2args
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (assert-3args
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (decode-args-1or2
    :map-binary-write 'movitz-intern-code-vector
    :binary-tag :primitive-function
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-type code-vector-word)
   (box-u32-ecx
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (unbox-u32
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)   
   (fast-cdr-car
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-cons
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (ensure-heap-cons-variable
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-compare-two-reals
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-compare-fixnum-real
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (fast-compare-real-fixnum
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (trampoline-cl-dispatch-1or2
    :binary-type code-vector-word
    :initform nil
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (dynamic-jump-next
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
   (copy-funobj-code-vector-slots
    :binary-type code-vector-word
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :binary-tag :primitive-function)
      
   ;;
   (boolean-one :binary-type :label)
   (not-nil				; not-nil, t-symbol and not-not-nil must be consecutive.
    :binary-type word
    :initform nil
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (boolean-zero :binary-type :label)
   (t-symbol
    :binary-type word
    :initarg :t-symbol
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word)
   (not-not-nil
    :binary-type word
    :initform nil
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   ;;   (null-cons :binary-type :label)
   (null-symbol
    :binary-type movitz-symbol
    :reader movitz-run-time-context-null-symbol
    :initarg :null-symbol)
   
   (complicated-eql
    :initform 'muerte::complicated-eql
    :binary-type word
    :binary-tag :global-function
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word)
   (complicated-compare
    :binary-type word
    :binary-tag :global-function
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-intern)
   (dynamic-env
    :binary-type word
    :initform 0)
   
   (scratch1
    :binary-type word
    :initform 0)
   (scratch2
    :binary-type word
    :initform 0)
   (class
    :binary-type word
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :class
    :accessor run-time-context-class)
   (slots
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :slots
    :initform #(:init nil)
    :accessor run-time-context-slots)
   (unwind-protect-tag
    :binary-type word
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-read-and-intern
    :initform 'muerte::unwind-protect-tag)
   (restart-tag
    :binary-type word
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-read-and-intern
    :initform 'muerte::restart-protect-tag)
   (new-unbound-value
    :binary-type word
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-read-and-intern
    :initform 'unbound)
   (stack-bottom			; REMEMBER BOCHS!
    :binary-type word
    :initform #x0ff000)
   (stack-top				; stack-top must be right after stack-bottom
    :binary-type word			; in order for the bound instruction to work.
    :initform #x100000)
   (+
    :initform 'muerte.cl:+
    :binary-type word
    :binary-tag :global-function
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word)
   (the-class-t
    :binary-type word
    :initform t
    :map-binary-write (lambda (x type)
			(declare (ignore type))
			(movitz-read-and-intern (funcall 'muerte::movitz-find-class x)
						'word))
    :map-binary-read-delayed 'movitz-word)
   (copy-funobj
    :binary-type word
    ;; :accessor movitz-run-time-context-copy-funobj
    :initform 'muerte::copy-funobj
    :map-binary-write (lambda (name type)
			(declare (ignore type))
			(movitz-intern (movitz-env-named-function name))))


   (classes				; A vector of class meta-objects.
    :initform nil			; The first element is the map of corresponding names
    :binary-type word
    :map-binary-write (lambda (x type)
			(declare (ignore x type))
			(let ((map (image-classes-map *image*)))
			  (movitz-read-and-intern
			   (apply #'vector
				  map
				  (mapcar (lambda (x)
					    (funcall 'muerte::movitz-find-class x))
					  map))
			   'word)))
    :map-binary-read-delayed 'movitz-word)
   (physical-address-offset
    :binary-type lu32
    :initform (image-ds-segment-base *image*))
   (nursery-space
    :binary-type word
    :initform nil
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed (lambda (x type)
			       (declare (ignore x type))
			       (movitz-read nil)))
   (allow-other-keys-symbol
    :binary-type word
    :initform :allow-other-keys
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed (lambda (x type)
			       (declare (ignore x type))
			       (movitz-read nil)))
   (self
    :binary-type word
    :initform 6
    :map-binary-read-delayed 'movitz-word)
   (complicated-class-of
    :binary-type word
    :binary-tag :global-function
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-intern)
   (stack-vector
    :binary-type word
    :initform nil
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed (lambda (x type)
			       (declare (ignore x type))
			       (movitz-read nil)))
   (exception-handlers
    :binary-type word
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :exception-handlers
    :accessor movitz-run-time-context-exception-handlers)
   (interrupt-descriptor-table
    :binary-type word
    :accessor movitz-run-time-context-interrupt-descriptor-table
    :initform (make-array 256 :initial-element 'muerte::default-interrupt-trampoline)
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'map-interrupt-trampolines-to-idt)
   (num-values
    :binary-type word			; Fixnum
    :initform 0)
   (values
    :binary-type #.(* 4 +movitz-multiple-values-limit+)))
  (:slot-align null-symbol -5))

(defun atomically-continuation-simple-pf (pf-name)
  (ldb (byte 32 0) (global-constant-offset pf-name))
  #+ignore
  (bt:enum-value 'movitz::atomically-status
		 (list* :restart-primitive-function
			(cons :reset-status-p
			      (if reset-status-p 1 0))
			(cons :data
			      (if (not pf-name)
				  0
				(truncate (+ (tag :null)
					     (bt:slot-offset 'movitz-run-time-context
							     (intern (symbol-name pf-name)
								     :movitz)))
					  4)))
			registers)))

(defun atomically-status-jumper-fn (reset-status-p &rest registers)
  (assert (not reset-status-p))
  (assert (null registers))
  (lambda (jumper)
    (assert (= 0 (mod jumper 4)))
    (bt:enum-value 'movitz::atomically-status
		   (list* :restart-jumper
			  (cons :reset-status-p
				(if reset-status-p 1 0))
			  (cons :data (truncate jumper 4))
			  registers))))

(defmethod movitz-object-offset ((obj movitz-run-time-context)) 0)

(defun global-constant-offset (slot-name)
  (check-type slot-name symbol)
  (let ((slot-name (find-symbol (symbol-name slot-name) :movitz)))
    (assert slot-name)
    (if (not (eq slot-name 'unbound-function))
	(slot-offset 'movitz-run-time-context slot-name)
      (+ (slot-offset 'movitz-run-time-context 'null-symbol)
	 (slot-offset 'movitz-symbol 'function-value)
	 (tag :symbol)))))

(defun make-movitz-run-time-context ()
  (make-instance 'movitz-run-time-context
    :t-symbol (movitz-read 't)
    :null-symbol  *movitz-nil*))

(defclass movitz-image ()
  ((ds-segment-base
    :initarg :ds-segment-base
    :initform #x100000
    :accessor image-ds-segment-base)
   (cs-segment-base
    :initarg :cs-segment-base
    :initform #x100000
    :accessor image-cs-segment-base)))

(defclass symbolic-image (movitz-image)
  ((object-hash
    :accessor image-object-hash)	; object => address
   (address-hash
    :accessor image-address-hash)	; address => object
   (cons-pointer
    :accessor image-cons-pointer)
   (read-map-hash
    :initform (make-hash-table :test #'eql) ; lisp object => movitz object
    :reader image-read-map-hash)
   (inverse-read-map-hash
    :initform (make-hash-table :test #'eql) ; lisp object => movitz object
    :reader image-inverse-read-map-hash)
   (oblist
    :reader image-oblist
    :initform (make-hash-table :test #'eql))
   (global-environment
    :initform (make-global-movitz-environment)
    :reader image-global-environment)
   (struct-slot-descriptions
    :initform (make-hash-table :test #'eq)
    :accessor image-struct-slot-descriptions)
   (start-address
    :initarg :start-address
    :accessor image-start-address)
   (symbol-hash-key-counter
    :initform 0
    :type unsigned-byte
    :accessor image-symbol-hash-key-counter)
   (nil-word
    :accessor image-nil-word)
   (nil-object
    :initarg :nil-object
    :accessor image-nil-object)
   (t-symbol
    :accessor image-t-symbol)
   (bootblock
    :accessor image-bootblock)
   (movitz-modules
    :initarg :movitz-modules
    :initform nil
    :accessor image-movitz-modules)
   (movitz-features
    :initarg :movitz-features
    :accessor image-movitz-features)
   (called-functions
    :initarg :called-functions
    :initform nil
    :accessor image-called-functions)
   (toplevel-funobj
    :accessor image-toplevel-funobj)
   (run-time-context
    :accessor image-run-time-context)
   (load-time-funobjs
    :initform ()
    :accessor image-load-time-funobjs)
   (compile-time-variables
    :initform ()
    :accessor image-compile-time-variables)
   (string-constants
    :initform (make-hash-table :test #'equal)
    :reader image-string-constants)
   (cons-constants
    :initform (make-hash-table :test #'equal)
    :reader image-cons-constants)
   (multiboot-header
    :accessor image-multiboot-header)
   (dump-count
    :initform 0
    :accessor dump-count)
   (function-code-sizes
    :initform (make-hash-table :test #'equal)
    :initarg :function-code-sizes
    :reader function-code-sizes)))

(defmethod image-classes-map ((image symbolic-image))
  '(muerte.cl:null muerte.cl:cons muerte.cl:fixnum muerte.cl:symbol
    muerte.cl:character muerte.cl:function muerte.cl:condition
    muerte.cl:integer muerte.cl:ratio muerte.cl:complex
    muerte.cl:vector muerte.cl:string muerte.cl:bit-vector muerte.cl:array
    muerte.cl:class muerte.cl:standard-class
    muerte.cl:standard-generic-function
    muerte:run-time-context
    muerte.mop:standard-effective-slot-definition
    muerte.mop:funcallable-standard-class
    muerte::basic-restart
    muerte::illegal-object))

(defun class-object-offset (name)
  (let ((name (translate-program name :cl :muerte.cl)))
    (+ (bt:slot-offset 'movitz-basic-vector 'data)
       (* 4 (1+ (or (position name (image-classes-map *image*))
		    (error "No class named ~S in class-map." name)))))))

(defun unbound-value ()
  (declare (special *image*))
  (movitz-read (slot-value (image-run-time-context *image*)
			   'new-unbound-value)))

(defun edi-offset ()
  (declare (special *image*))
  (- (image-nil-word *image*)))

(defmethod image-intern-object ((image symbolic-image) object &optional (size (sizeof object)))
  (assert				; sanity check on "other" storage-types.
      (or (not (typep object 'movitz-heap-object-other))
	  (and (= (- (tag :other))
		  (slot-offset (type-of object)
			       (first (binary-record-slot-names (type-of object)))))
	       (= +other-type-offset+ (slot-offset (type-of object) 'type))))
      ()
    "The MOVITZ-HEAP-OBJECT-OTHER type ~A is malformed!" (type-of object))
  (etypecase object
    (movitz-null
     (image-nil-word image))
    (movitz-heap-object
     (+ (movitz-object-offset object)
	(or (gethash object (image-object-hash image))
	    (let* ((alignment (movitz-storage-alignment object))
		   (new-ptr (if (= (movitz-storage-alignment-offset object)
				   (mod (image-cons-pointer image)
					(movitz-storage-alignment object)))
				(image-cons-pointer image)
			      (+ (image-cons-pointer image)
				 (mod (- (image-cons-pointer image))
				      alignment)
				 (movitz-storage-alignment-offset object)))))
	      (setf (gethash new-ptr (image-address-hash image)) object
		    (gethash object (image-object-hash image)) new-ptr
		    (image-cons-pointer image) (+ new-ptr size))
	      new-ptr))))))

(defmethod image-memref ((image symbolic-image) address &optional (errorp t))
  (let ((obj (gethash address (image-address-hash image) :nothing)))
    (cond
     ((not (typep obj 'movitz-object))
      (when errorp
	(error "Found non-movitz-object at image-address #x~X: ~A" address obj))
      nil)
     (t obj))))

(defmethod search-image ((image symbolic-image) address)
  (loop for a downfrom (logand address -8) by 8
      until (gethash a (image-address-hash image))
      finally (let ((object (gethash a (image-address-hash image))))
		(when (<= address (+ a (sizeof object)))
		  ;; (warn "Found at ~X: ~S" a (gethash a (image-address-hash image)))
		  (return object)))))

(defun search-image-funobj (address &optional (*image* *image*))
  (search-image-funobj-by-image *image* address))

(defmethod search-image-funobj-by-image ((image symbolic-image) address)
  (let ((code-vector (search-image image (1- address))))
    (unless (and (typep code-vector 'movitz-basic-vector)
		 (eq :code (movitz-vector-element-type code-vector)))
      (error "Not a code-vector at #x~8,'0X: ~S" address code-vector))
    (let ((offset (- address (movitz-intern-code-vector code-vector))))
      (assert (not (minusp offset)))
      (format t "~&;; Matched code-vector at #x~X with offset ~D.~%"
	      (image-intern-object image code-vector)
	      offset))
    (with-hash-table-iterator (next-object (image-object-hash *image*))
      (loop with more-objects and object
	  do (multiple-value-setq (more-objects object) (next-object))
	  while more-objects
	  when (typecase object
		 (movitz-funobj
		  (when (eq code-vector (movitz-funobj-code-vector object))
		    object))
		 (movitz-symbol
		  (when (eq code-vector (movitz-symbol-value object))
		    (movitz-print object))))
	  collect it))))

(defun search-primitive-function (address &optional (*image* *image*))
  (let ((code-vector (search-image *image* address)))
    (unless (and (typep code-vector 'movitz-basic-vector)
		 (eq :u8 (movitz-vector-element-type code-vector)))
      (error "Not a code-vector at #x~8,'0X: ~S" address code-vector))
    (format t "~&;; Code vector: #x~X" (movitz-intern code-vector))
    (loop for pf-name in (binary-record-slot-names 'movitz-run-time-context
						   :match-tags :primitive-function)
	when (= (movitz-intern-code-vector code-vector)
		(binary-slot-value (image-run-time-context *image*) pf-name))
	do (format t "~&;; #x~X matches global primitive-function ~W with offset ~D."
		   address pf-name
		   (- address (movitz-intern-code-vector code-vector)))
	and collect pf-name)))



(defun movitz-word (word &optional (type 'word))
  "Return the movitz-object corresponding to (the integer) WORD."
  (assert (eq type 'word))
  (movitz-word-by-image *image* word))

(defun movitz-word-and-print (word &optional (type 'word))
  (movitz-print (movitz-word word type)))

(defmethod movitz-word-by-image ((image symbolic-image) word)
  (case (extract-tag word)
    (#.+fixnum-tags+
     (make-movitz-fixnum
      (make-instance 'movitz-fixnum :value (fixnum-integer word))))
    (:character
     (make-instance 'movitz-character :char (code-char (ldb (byte 8 8) word))))
    (:null
     (image-nil-word image))
    (t (image-memref *image* (logand word #xfffffff8) t))))

(defun movitz-intern-code-vector (object &optional (type 'code-vector-word))
  "Four ways to denote a code-vector: a vector is that vector,
a symbol is considered a primitive-function and the symbol-value is used,
a movitz-funobj is that funobj's code-vector,
a cons is an offset (the car) from some other code-vector (the cdr)."
  (assert (member type '(code-vector-word code-pointer)))
  (etypecase object
    ((or vector movitz-basic-vector)
     (+ 2 (movitz-intern object)))
    ((or symbol movitz-symbol)
     (let ((primitive-code-vector (movitz-symbol-value (movitz-read object))))
       (check-type primitive-code-vector movitz-basic-vector)
       (movitz-intern-code-vector primitive-code-vector type)))
    (movitz-funobj
     (movitz-intern-code-vector (movitz-funobj-code-vector object) type))
    (cons
     ;; a cons denotes an offset (car) from some funobj's (cdr) code-vector.
     (check-type (car object) integer)
     (check-type (cdr object) movitz-funobj)
     (+ (car object) (movitz-intern-code-vector (cdr object) type)))))

(defun movitz-intern-global-function (object &optional (type 'word))
  (assert (eq type 'word))
  (check-type object symbol)
  (let ((x (movitz-env-named-function object)))
    (check-type x movitz-funobj)
    (movitz-intern x 'word)))

(defun movitz-word-code-vector (word &optional (type 'code-vector-word))
  (assert (eq type 'code-vector-word))
  (movitz-word (- word +code-vector-word-offset+)))

(defun copy-hash-table (x)
  (let ((y (make-hash-table :test (hash-table-test x))))
    (maphash (lambda (k v)
	       (setf (gethash k y) v))
	     x)
    y))

(defun make-initial-segment-descriptor-table ()
  (let ((u32-list
	 (let ((bt:*endian* :little-endian))
	   (merge-bytes (with-binary-output-to-list (octet-list)
			  (mapcar (lambda (init-args)
				    (write-binary 'segment-descriptor octet-list
						  (apply #'make-segment-descriptor init-args)))
				  `(()	; 0
				    (:base 0 :limit #xfffff ; 1: physical code
					   :type 14 :dpl 0 :flags (s p d/b g))
				    (:base 0 :limit #xfffff ; 2: physical data
					   :type 2 :dpl 3 :flags (s p d/b g))
				    (:base ,(image-cs-segment-base *image*) ; 3: logical code
					   :limit #xfff00
					   :type 14 :dpl 0 :flags (s p d/b g))
				    (:base ,(image-ds-segment-base *image*) ; 4: logical data
					   :limit #xfff00
					   :type 2 :dpl 0 :flags (s p d/b g))
				    )))
			8 32))))
    (movitz-read (make-movitz-vector (length u32-list)
				     :initial-contents u32-list
				     :element-type '(unsigned-byte 32)))))
		     

(defun make-movitz-image (&rest init-args &key start-address &allow-other-keys)
  (let ((*image* (apply #'make-instance 'symbolic-image
			:nil-object (make-movitz-nil)
			:start-address start-address
			:movitz-features '(:movitz)
			:function-code-sizes
			(if *image*
			    (copy-hash-table (function-code-sizes *image*))
                            (make-hash-table :test #'equal))
			init-args)))
    (setf (image-nil-word *image*)
      (+ 5 (- (slot-offset 'movitz-run-time-context 'null-symbol)
	      (slot-offset 'movitz-run-time-context 'run-time-context-start))
	 (- start-address
	    (image-ds-segment-base *image*))))
    (format t "~&;; NIL value: #x~X.~%" (image-nil-word *image*))
    (assert (eq :null (extract-tag (image-nil-word *image*))) ()
      "NIL value #x~X has tag ~D, but it must be ~D."
      (image-nil-word *image*)
      (ldb (byte 3 0) (image-nil-word *image*))
      (tag :null))
    (setf (image-run-time-context *image*) (make-movitz-run-time-context))
    (setf (image-t-symbol *image*) (movitz-read t))
    ;; (warn "NIL value: #x~X" (image-nil-word *image*))
    *image*))

(defun find-primitive-function (name)
  "Given the NAME of a primitive function, look up 
   that function's code-vector."
  (let ((code-vector
	 (movitz-symbol-value (movitz-read name))))
    (unless (and code-vector (not (eq 'unbound code-vector)))
      (cerror "Install an empty vector instead."
	      "Global constant primitive function ~S is not defined!" name)
      (setf code-vector
	(setf (movitz-symbol-value (movitz-read name))
	  (movitz-read #()))))
    (check-type code-vector movitz-basic-vector)
    code-vector))

(defun create-image (&rest init-args
		     &key (init-file *default-image-init-file*)
			  (gc t)
			  ;; (start-address #x100000)
			  &allow-other-keys)
  (psetq *image* (let ((*image* (apply #'make-movitz-image
				       :start-address #x100000
				       init-args)))
		   (when init-file
		     (movitz-compile-file init-file))
		   *image*)
	 *i* *image*)
  (when gc
    #+allegro (setf (sys:gsgc-parameter :generation-spread) 8)
    #+allegro (excl:gc :tenure)
    #+allegro (excl:gc t))		; We just thrashed a lot of tenured objects.
  *image*)

(defun set-file-position (stream position &optional who)
  (declare (ignore who))
  (or (ignore-errors (file-position stream position))
      (let* ((end (file-position stream :end))
	     (diff (- position end)))
	(dotimes (i diff)
	  (write-byte 0 stream))
	(assert (= position (file-position stream)))))
  (values))

(defun dump-image (&key (path *default-image-file*) ((:image *image*) *image*)
                   (multiboot-p t) ignore-dump-count (qemu-align :floppy))
  "When <multiboot-p> is true, include a MultiBoot-compliant header in the image."
  (when (and (not ignore-dump-count)
	     (= 0 (dump-count *image*)))
    ;; This is a hack to deal with the fact that the first dump won't work
    ;; because the packages aren't properly set up.
    (format t "~&;; Doing initiating dump..")
    (dump-image :path path :multiboot-p multiboot-p :ignore-dump-count t
		:qemu-align nil)
    (assert (plusp (dump-count *image*))))
  (setf (movitz-symbol-value (movitz-read 'muerte:*build-number*))
    (1+ *bootblock-build*))
  (when (eq 'unbound (movitz-symbol-value (movitz-read 'muerte::*initial-segment-descriptor-table*)))
    (setf (movitz-symbol-value (movitz-read 'muerte::*initial-segment-descriptor-table*))
      (make-initial-segment-descriptor-table)))
  (let ((handler (movitz-env-symbol-function 'muerte::interrupt-default-handler)))
    (setf (movitz-run-time-context-exception-handlers (image-run-time-context *image*))
      (movitz-read (make-array 256 :initial-element handler))))
  (setf (movitz-symbol-value (movitz-read 'muerte::*setf-namespace*))
    (movitz-read (movitz-environment-setf-function-names *movitz-global-environment*) t))
  (setf (run-time-context-class (image-run-time-context *image*))
    (muerte::movitz-find-class 'muerte::run-time-context))
  ;;  (setf (run-time-context-slots (image-run-time-context *image*)) #(1 2 3))
  (let ((load-address (image-start-address *image*)))
    (setf (image-cons-pointer *image*) (- load-address
					  (image-ds-segment-base *image*))
	  (image-address-hash *image*) (make-hash-table :test #'eq)
	  (image-object-hash  *image*) (make-hash-table :test #'eq)
	  (image-multiboot-header *image*) (make-instance 'multiboot-header
					     :header-address 0
					     :load-address 0
					     :load-end-address 0
					     :entry-address 0))
    (assert (= load-address (+ (image-intern-object *image* (image-run-time-context *image*))
			       (image-ds-segment-base *image*))))
    (when multiboot-p
      (assert (< (+ (image-intern-object *image* (image-multiboot-header *image*))
		    (sizeof (image-multiboot-header *image*))
		    (- load-address))
		 8192)))
    ;; make the toplevel-funobj
    (unless (image-load-time-funobjs *image*)
      (warn "No top-level funobjs!"))
    (setf (image-load-time-funobjs *image*)
      (stable-sort (copy-list (image-load-time-funobjs *image*)) #'> :key #'third))
    (let* ((toplevel-funobj (make-toplevel-funobj *image*)))
      (setf (image-toplevel-funobj *image*) toplevel-funobj
	    #+ignore ((movitz-run-time-context-toplevel-funobj (image-run-time-context *image*)) toplevel-funobj))
      (format t "~&;; load-sequence:~%~<~A~>~%" (mapcar #'second (image-load-time-funobjs *image*)))
      (movitz-intern toplevel-funobj)
      (let ((init-code-address (+ (movitz-intern-code-vector (movitz-funobj-code-vector toplevel-funobj))
				  (image-cs-segment-base *image*))))
	(dolist (cf (image-called-functions *image*))
	  (unless (typep (movitz-env-named-function (car cf) nil)
			 'movitz-funobj)
	    (warn "Function ~S is called (in ~S) but not defined." (car cf) (cdr cf))))
	(maphash (lambda (symbol function-value)
		   (let ((movitz-symbol (movitz-read symbol)))
		     (etypecase function-value
		       (movitz-funobj
			(setf (movitz-symbol-function-value movitz-symbol) function-value))
		       (movitz-macro
			#+ignore (warn "fv: ~S ~S ~S" symbol function-value (movitz-env-get symbol :macro-expansion))))))
		 (movitz-environment-function-cells (image-global-environment *image*)))
	(let ((run-time-context (image-run-time-context *image*)))
	  ;; pull in functions in run-time-context
	  (dolist (gcf-name (binary-record-slot-names 'movitz-run-time-context :match-tags :global-function))
	    (let* ((gcf-movitz-name (movitz-read (intern (symbol-name gcf-name)
							 ':muerte)))
		   (gcf-funobj (movitz-symbol-function-value gcf-movitz-name)))
	      (setf (slot-value run-time-context gcf-name) 0)
	      (cond
	       ((or (not gcf-funobj)
		    (eq 'unbound gcf-funobj))
		(warn "Global constant function ~S is not defined!" gcf-name))
	       (t (check-type gcf-funobj movitz-funobj)
		  (setf (slot-value run-time-context gcf-name)
		    gcf-funobj)))))
	  ;; pull in primitive functions in run-time-context
	  (dolist (pf-name (binary-record-slot-names 'movitz-run-time-context
						     :match-tags :primitive-function))
	    (setf (slot-value run-time-context pf-name)
	      (find-primitive-function (intern (symbol-name pf-name) :muerte))))
	  #+ignore
	  (loop for k being the hash-keys of (movitz-environment-setf-function-names *movitz-global-environment*)
	      using (hash-value v)
	      do (assert (eq (symbol-value v) 'muerte::setf-placeholder))
	      do (when (eq *movitz-nil* (movitz-symbol-function-value (movitz-read v)))
		   (warn "non-used setf: ~S" v)))
	  ;; symbol plists
	  (loop for (symbol plist) on (movitz-environment-plists *movitz-global-environment*) by #'cddr
              ;; do (warn "sp: ~S ~S" symbol plist)
	      do (let ((x (movitz-read symbol)))
		   (typecase x
		     (movitz-null)
		     (movitz-symbol
		      (setf (movitz-plist x)
			(movitz-read (translate-program (loop for (property value) on plist by #'cddr
							    unless (member property '(special constantp))
							    append (list property value))
							:cl :muerte.cl))))
		     (t (warn "not a symbol for plist: ~S has ~S" symbol plist)))))
	  ;; pull in global properties
	  (loop for (var value) on (image-compile-time-variables *image*) by #'cddr
	      do (let ((mname (movitz-read var))
		       (mvalue (movitz-read value)))
		   (setf (movitz-symbol-value mname) mvalue)))
	  (setf (movitz-symbol-value (movitz-read 'muerte::*packages*))
	    (movitz-read (make-packages-hash))))
	(with-binary-file (stream path
				  :check-stream t
				  :direction :output
				  :if-exists :supersede
				  :if-does-not-exist :create)
	  (set-file-position stream 512) ; leave room for bootblock.
	  (let* ((stack-vector (make-instance 'movitz-basic-vector
				 :num-elements #x3ffe
				 :fill-pointer 0
				 :symbolic-data nil
				 :element-type :stack))
		 (image-start (file-position stream)))
	    (dump-image-core *image* stream) ; dump the kernel proper.
	    ;; make a stack-vector for the root run-time-context
	    (let* ((stack-vector-word
		    (let ((*endian* :little-endian))
		      (write-binary-record stack-vector stream)
		      ;; Intern as _last_ object in image.
		      (movitz-intern stack-vector)))
		   (image-end (file-position stream))
		   (kernel-size (- image-end image-start)))
	      (format t "~&;; Kernel size: ~D octets.~%" kernel-size)
              (ecase qemu-align
		(:floppy
                 ;; QEMU is rather stupid about "auto-detecting" floppy geometries.
                 (loop for qemu-geo in '(320 360 640 720 720 820 840 1440 1440 1600 1640 1660 1760 2080 2240 2400
                                         2880 2952 2988 3200 3200 3360 3444 3486 3520 3680 3840 5760 6240 6400 7040 7680)
                     as qemu-size = (* qemu-geo 512)
                     do (when (>= qemu-size image-end)
                          (set-file-position stream (1- qemu-size) 'pad-image-tail)
                          (write-byte #x0 stream)
                          (return))
                     finally
                      (cerror "Never mind, dump the image without any QEMU geometry alignment."
                              "No matching QEMU floppy geometry for size ~,2F MB."
			      (/ image-end (* 1024 1024)))))
		(:hd (let ((align-image-size (* 512 16 63))) ; Ensure image is multiple of x octets
		       (unless (zerop (mod image-end align-image-size))
			 (set-file-position stream (+ image-end (- (1- align-image-size) (mod image-end 512)))
					    'pad-image-tail)
			 (write-byte #x0 stream))))
		((nil) (let ((align-image-size (* 512 1))) ; Ensure image is multiple of x octets
			 (unless (zerop (mod image-end align-image-size))
			   (set-file-position stream (+ image-end (- (1- align-image-size) (mod image-end 512)))
					      'pad-image-tail)
			   (write-byte #x0 stream)))))
	      (format t "~&;; Image file size: ~D octets.~%" image-end)
	      ;; Write simple stage1 bootblock into sector 0..
	      (format t "~&;; Dump count: ~D." (incf (dump-count *image*)))
	      (flet ((global-slot-position (slot-name)
		       (+ 512
			  (image-nil-word *image*)
			  (image-ds-segment-base *image*)
			  (global-constant-offset slot-name)
			  (- load-address))))
		(with-simple-restart (continue "Don't write a floppy bootloader.")
		  (let ((bootblock (make-bootblock kernel-size
						   load-address
						   init-code-address)))
		    (setf (image-bootblock *image*) bootblock)
		    (set-file-position stream 0)
		    (write-sequence bootblock stream)))
		(let* ((stack-vector-address (+ (image-nil-word *image*)
						(global-constant-offset 'stack-vector)
						(image-ds-segment-base *image*)))
		       (stack-vector-position (- (+ stack-vector-address 512)
						 load-address)))
		  (declare (ignore stack-vector-position))
		  #+ignore(warn "stack-v-pos: ~S => ~S" 
				stack-vector-position
				stack-vector-word)
		  (set-file-position stream (global-slot-position 'stack-vector) 'stack-vector)
		  (write-binary 'word stream stack-vector-word)
		  (set-file-position stream (global-slot-position 'stack-bottom) 'stack-bottom)
		  (write-binary 'lu32 stream (+ 8 (* 8 4096) ; cushion
						(- stack-vector-word (tag :other))))
		  (set-file-position stream (global-slot-position 'stack-top) 'stack-top)
		  (write-binary 'lu32 stream (+ 8 (- stack-vector-word (tag :other))
						(* 4 (movitz-vector-num-elements stack-vector)))))
		(if (not multiboot-p)
		    (format t "~&;; No multiboot header.")
		  ;; Update multiboot header, symbolic and in the file..
		  (let* ((mb (image-multiboot-header *image*))
			 (mb-address (+ (movitz-intern mb)
					(slot-offset 'multiboot-header 'magic)
					(image-ds-segment-base *image*)))
			 (mb-file-position (- (+ mb-address 512)
					      load-address
					      (slot-offset 'multiboot-header 'magic))))
		    (when (< load-address #x100000)
		      (warn "Multiboot load-address #x~x is below the 1MB mark."
			    load-address))
		    (when (> (+ mb-file-position (sizeof mb)) 8192)
		      (warn "Multiboot header at position ~D is above the 8KB mark, ~
this image will not be Multiboot compatible."
			    (+ mb-file-position (sizeof mb))))
		    (set-file-position stream mb-file-position 'multiboot-header)
		    ;; (format t "~&;; Multiboot load-address: #x~X." load-address)
		    (setf (header-address mb) mb-address
			  (load-address mb) load-address
			  (load-end-address mb) (+ load-address kernel-size)
			  (bss-end-address mb) (+ load-address kernel-size)
			  (entry-address mb) init-code-address)
		    (write-binary-record mb stream))))))))))
  (values))

(defun dump-image-core (image stream)
  (let ((*endian* :little-endian)
	(*record-all-funobjs* nil)
	(symbols-size 0)
	(conses-size 0)
	(funobjs-size 0)
	(code-vectors-size 0)
	(strings-size 0)
	(simple-vectors-size 0)
	(total-size 0)
	(symbols-numof 0)
	(gensyms-numof 0)
	(conses-numof 0)
	(funobjs-numof 0)
	(code-vectors-numof 0)
	(strings-numof 0)
	(simple-vectors-numof 0)
	(file-start-position (file-position stream))
	(pad-size 0))
    (declare (special *record-all-funobjs*))
    (loop with prev-obj
	for p upfrom (- (image-start-address image) (image-ds-segment-base image)) by 8
	until (>= p (image-cons-pointer image))
	summing
	  (let ((obj (image-memref image p nil)))
	    (cond
	     ((not obj) 0)		; (+ 1mb (- 1mb)) vs. (+ 0 (- 1mb 1mb))
	     (t (let ((new-pos (+ p file-start-position
				  (- (image-ds-segment-base image)
				     (image-start-address image)))))
		  (let ((pad-delta (- new-pos (file-position stream))))
		    (with-simple-restart (continue "Never mind.")
		      (assert (<= 0 pad-delta 31) ()
			"pad-delta ~S for ~S (prev ~S), p: ~S, new-pos: ~S"
			pad-delta obj prev-obj p new-pos))
		    (incf pad-size pad-delta))
		  (set-file-position stream new-pos obj))
		;; (warn "Dump at address #x~X, filepos #x~X: ~A" p (file-position stream) obj)
		(let ((old-pos (file-position stream))
		      (write-size (write-binary-record obj stream)))
		  (incf total-size write-size)
		  (typecase obj
		    (movitz-basic-vector
		     (case (movitz-vector-element-type obj)
		       (:character (incf strings-numof)
				   (incf strings-size write-size))
		       (:any-t (incf simple-vectors-numof)
			       (incf simple-vectors-size write-size))
		       (:code (incf code-vectors-numof)
			      (incf code-vectors-size write-size))))
		    (movitz-funobj (incf funobjs-numof)
				   (incf funobjs-size write-size))
		    (movitz-symbol (incf symbols-numof)
				   (incf symbols-size write-size)
				   (when (movitz-eql *movitz-nil* (movitz-symbol-package obj))
				     (incf gensyms-numof)))
		    (movitz-cons (incf conses-numof)
				 (incf conses-size write-size)))
		  (assert (= write-size (sizeof obj) (- (file-position stream) old-pos)) ()
		    "Inconsistent write-size(~D)/sizeof(~D)/file-position delta(~D) ~
                       for object ~S."
		    write-size (sizeof obj) (- (file-position stream) old-pos) obj)
		  (setf prev-obj obj)
		  write-size))))
	finally
	  (let ((total-size (file-position stream))
		(sum (+ symbols-size conses-size funobjs-size strings-size
			simple-vectors-size code-vectors-size pad-size)))
	    (format t "~&;;~%;; ~D symbols (~D gensyms) (~,1F KB ~~ ~,1F%), ~D conses (~,1F KB ~~ ~,1F%),
~D funobjs (~,1F KB ~~ ~,1F%), ~D strings (~,1F KB ~~ ~,1F%),
~D simple-vectors (~,1F KB ~~ ~,1F%), ~D code-vectors (~,1F KB ~~ ~,1F%).
~,1F KB (~,1F%) of padding.
In sum this accounts for ~,1F%, or ~D bytes.~%;;~%"
		    symbols-numof gensyms-numof
		    (/ symbols-size 1024) (/ (* symbols-size 100) total-size)
		    conses-numof (/ conses-size 1024) (/ (* conses-size 100) total-size)
		    funobjs-numof (/ funobjs-size 1024) (/ (* funobjs-size 100) total-size)
		    strings-numof (/ strings-size 1024) (/ (* strings-size 100) total-size)
		    simple-vectors-numof (/ simple-vectors-size 1024) (/ (* simple-vectors-size 100) total-size)
		    code-vectors-numof (/ code-vectors-size 1024) (/ (* code-vectors-size 100) total-size)
		    (/ pad-size 1024) (/ (* pad-size 100) total-size)
		    (/ (* sum 100) total-size)
		    sum)))))

(defun intern-movitz-symbol (name)
  (assert (not (member (symbol-package name)
		       '(:common-lisp :movitz)
		       :key #'find-package))
      (name)
    "Trying to movitz-intern a symbol in the ~A package: ~S" (symbol-package name) name)
  (assert (not (eq (symbol-package name)
		   (find-package :movitz)))
      (name)
    "Trying to movitz-intern a symbol in the Common-Lisp package: ~S" name)
  (or (gethash name (image-oblist *image*))
      (let ((symbol (make-movitz-symbol name)))
	(when (get name :setf-placeholder)
	  (setf (movitz-symbol-flags symbol) '(:setf-placeholder)
		(movitz-symbol-value symbol) (movitz-read (get name :setf-placeholder))))
	(setf (gethash name (image-oblist *image*)) symbol)
	(when (symbol-package name)
	  (let ((p (gethash (symbol-package name) (image-read-map-hash *image*))))
	    (when p
	      (setf (movitz-symbol-package symbol) p))))
	(when (or (eq 'muerte.cl:t name)
		  (keywordp (translate-program name :muerte.cl :cl)))
	  (pushnew :constant-variable (movitz-symbol-flags symbol))
	  (setf (movitz-symbol-value symbol)
	    (movitz-read (translate-program (symbol-value (translate-program name :muerte.cl :cl))
					    :cl :muerte.cl))))
	symbol)))

(defun make-packages-hash (&optional (*image* *image*))
  (let ((lisp-to-movitz-package (make-hash-table :test #'eq))
	(packages-hash (make-hash-table :test #'equal :size 23)))
    (labels ((movitz-package-name (name &optional symbol)
	       (declare (ignore symbol))
	       (cond
		((string= (string :keyword) name)
		 name)
		((and (< 7 (length name))
		      (string= (string 'muerte.) name :end2 7))
		 (subseq name 7))
		(t #+ignore (warn "Package ~S ~@[for symbol ~S ~]is not a Movitz package."
				  name symbol)
		   name)))
	     (ensure-package (package-name lisp-package &optional context)
	       (restart-case (assert (not (member (package-name lisp-package)
						  '(common-lisp movitz
						    #+allegro excl
						    #+allegro sys
						    #+allegro aclmop
						    #+sbcl sb-ext)
						  :test #'string=)) ()
						  "I don't think you really want to dump the package ~A ~@[for symbol ~S~] with Movitz."
						  lisp-package context)
		 (use-muerte ()
		   :report "Substitute the muerte pacakge."
		   (return-from ensure-package (ensure-package :muerte (find-package :muerte)))))
	       (setf (gethash lisp-package lisp-to-movitz-package)
		 (or (gethash package-name packages-hash nil)
		     (let* ((nicks (mapcar #'movitz-package-name (package-nicknames lisp-package)))
			    (p (funcall 'muerte::make-package-object
					:name package-name
					:shadowing-symbols-list (package-shadowing-symbols lisp-package)
					:external-symbols (make-hash-table :test #'equal)
					:internal-symbols (make-hash-table :test #'equal)
					:nicknames nicks
					:use-list (mapcar #'(lambda (up) 
							      (ensure-package (movitz-package-name (package-name up))
									      up context))
							  (package-use-list lisp-package)))))
		       (setf (gethash package-name packages-hash) p)
		       (dolist (nick nicks)
			 (setf (gethash nick packages-hash) p))
		       p)))))
      (let ((movitz-cl-package (ensure-package (symbol-name :common-lisp)
					       (find-package :muerte.common-lisp))))
	(setf (gethash "NIL" (funcall 'muerte:package-object-external-symbols movitz-cl-package))
	  nil))
      (ensure-package (symbol-name :common-lisp-user)
		      (find-package :muerte.common-lisp-user))
      (loop for symbol being the hash-key of (image-oblist *image*)
	  as lisp-package = (symbol-package symbol)
	  as package-name = (and lisp-package
				 (movitz-package-name (package-name lisp-package) symbol))
	  when package-name
	  do (let* ((movitz-package (ensure-package package-name lisp-package symbol)))
	       (multiple-value-bind (symbol status)
		   (find-symbol (symbol-name symbol) (symbol-package symbol))
		 (ecase status
		   (:internal
		    (setf (gethash (symbol-name symbol)
				   (funcall 'muerte:package-object-internal-symbols movitz-package))
		      symbol))
		   (:external
		    ;; (warn "putting external ~S in ~S" symbol package-name)
		    (setf (gethash (symbol-name symbol)
				   (funcall 'muerte:package-object-external-symbols movitz-package))
		      symbol))
		   (:inherited
		    (warn "inherited symbol: ~S" symbol))))))
;;;    (warn "PA: ~S" packages-hash)
      (let ((movitz-packages (movitz-read packages-hash)))
	(maphash (lambda (lisp-package movitz-package)
		   (setf (gethash lisp-package (image-read-map-hash *image*))
		     (movitz-read movitz-package)))
		 lisp-to-movitz-package)
	(setf (slot-value (movitz-run-time-context-null-symbol (image-run-time-context *image*))
			  'package)
	  (movitz-read (ensure-package (string :common-lisp) :muerte.common-lisp)))
	(loop for symbol being the hash-key of (image-oblist *image*)
	   as lisp-package = (symbol-package symbol)
	   as package-name = (and lisp-package
				  (movitz-package-name (package-name lisp-package) symbol))
	   when package-name
	   do (let* ((movitz-package (ensure-package package-name lisp-package symbol)))
		(setf (movitz-symbol-package (movitz-read symbol))
		      (movitz-read movitz-package))))
	movitz-packages))))


(defun run-time-context-find-slot (offset)
  "Return the name of the run-time-context slot located at offset."
  (dolist (slot-name (bt:binary-record-slot-names 'movitz-run-time-context))
    (when (= offset (bt:slot-offset 'movitz-run-time-context slot-name))
      (return slot-name))))

#-ia-x86
(defun comment-instruction (instruction funobj pc)
  "Return a list of strings that comments on INSTRUCTION."
  (declare (ignore pc))
  (loop for operand in (asm:instruction-operands instruction)
     when (and (typep operand 'asm:indirect-operand)
	       (member :edi operand)
	       (run-time-context-find-slot (asm:indirect-operand-offset operand))
	       (not (member (asm:instruction-operator instruction)
			    '(:leal :lea))))
     collect (format nil "<Global slot ~A>" 
		     (run-time-context-find-slot (asm:indirect-operand-offset operand)))
;;      when (and (typep operand 'ia-x86::operand-indirect-register)
;; 	       (eq 'ia-x86::edi (ia-x86::operand-register operand))
;; 	       (typep instruction 'ia-x86-instr::lea)
;; 	       (or (not (ia-x86::operand-register2 operand))
;; 		   (eq 'ia-x86::edi (ia-x86::operand-register2 operand))))
;;      collect (let ((x (+ (* (ia-x86::operand-scale operand)
;; 			    (image-nil-word *image*))
;; 			 (ia-x86::operand-offset operand)
;; 			 (ecase (ia-x86::operand-register2 operand)
;; 			   (ia-x86::edi (image-nil-word *image*))
;; 			   ((nil) 0)))))
;; 	       (case (ldb (byte 3 0) x)
;; 		 (#.(tag :character)
;; 		    (format nil "Immediate ~D (char ~S)"
;; 			    x (code-char (ldb (byte 8 8) x))))
;; 		 (#.(mapcar 'tag +fixnum-tags+)
;; 		    (format nil "Immediate ~D (fixnum ~D #x~X)"
;; 			    x
;; 			    (truncate x +movitz-fixnum-factor+)
;; 			    (truncate x +movitz-fixnum-factor+)))
;; 		 (t (format nil "Immediate ~D" x))))
     when (and funobj
	       (typep operand 'asm:indirect-operand)
	       (member :esi operand)
	       (= 2 (length operand))
	       (<= 12 (asm:indirect-operand-offset operand)))
     collect (format nil "~A"
		     (nth (truncate (- (+ (asm:indirect-operand-offset operand)
					  (if (member :edi operand)
					      (image-nil-word *image*)
					      0))
				       (slot-offset 'movitz-funobj 'constant0))
				    4)
			  (movitz-funobj-const-list funobj)))
;;      when (and funobj
;; 	       (typep operand 'ia-x86::operand-indirect-register)
;; 	       (eq 'ia-x86::esi (ia-x86::operand-register2 operand))
;; 	       (eq 'ia-x86::edi (ia-x86::operand-register operand))
;; 	       (<= 12 (ia-x86::operand-offset operand)))
;;      collect (format nil "~A" (nth (truncate (- (+ (ia-x86::operand-offset operand)
;; 						   (* (ia-x86::operand-scale operand)
;; 						      (image-nil-word *image*)))
;; 						(slot-offset 'movitz-funobj 'constant0))
;; 					     4)
;; 				   (movitz-funobj-const-list funobj)))
;;      when (typep operand 'ia-x86::operand-rel-pointer)
;;      collect (let* ((x (+ pc
;; 			  (imagpart (ia-x86::instruction-original-datum instruction))
;; 			  (length (ia-x86:instruction-prefixes instruction))
;; 			  (ia-x86::operand-offset operand)))
;; 		    (label (and funobj (car (find x (movitz-funobj-symtab funobj) :key #'cdr)))))
;; 	       (if label
;; 		   (format nil "branch to ~S at ~D" label x)
;; 		   (format nil "branch to ~D" x)))
     when (and (typep operand '(and integer asm:immediate-operand))
	       (<= #x100 operand #x10000)
	       (= (tag :character) (mod operand 256)))
     collect (format nil "#\\~C" (code-char (truncate operand 256)))
     when (and (typep operand '(and integer asm:immediate-operand))
	       (zerop (mod operand +movitz-fixnum-factor+)))
     collect (format nil "#x~X" (truncate operand +movitz-fixnum-factor+))))

#+ia-x86
(defun comment-instruction (instruction funobj pc)
  "Return a list of strings that comments on INSTRUCTION."
  (loop for operand in (ia-x86::instruction-operands instruction)
      when (and (typep operand 'ia-x86::operand-indirect-register)
		(eq 'ia-x86::edi (ia-x86::operand-register operand))
		(not (ia-x86::operand-register2 operand))
		(= 1 (ia-x86::operand-scale operand))
		(run-time-context-find-slot (ia-x86::operand-offset operand))
		(not (typep instruction 'ia-x86-instr::lea)))
      collect (format nil "<Global slot ~A>" 
		      (run-time-context-find-slot (ia-x86::operand-offset operand)))
      when (and (typep operand 'ia-x86::operand-indirect-register)
		(eq 'ia-x86::edi (ia-x86::operand-register operand))
		(typep instruction 'ia-x86-instr::lea)
		(or (not (ia-x86::operand-register2 operand))
		    (eq 'ia-x86::edi (ia-x86::operand-register2 operand))))
      collect (let ((x (+ (* (ia-x86::operand-scale operand)
			     (image-nil-word *image*))
			  (ia-x86::operand-offset operand)
			  (ecase (ia-x86::operand-register2 operand)
			    (ia-x86::edi (image-nil-word *image*))
			    ((nil) 0)))))
		(case (ldb (byte 3 0) x)
		  (#.(tag :character)
		     (format nil "Immediate ~D (char ~S)"
			     x (code-char (ldb (byte 8 8) x))))
		  (#.(mapcar 'tag +fixnum-tags+)
		   (format nil "Immediate ~D (fixnum ~D #x~X)"
			   x
			   (truncate x +movitz-fixnum-factor+)
			   (truncate x +movitz-fixnum-factor+)))
		  (t (format nil "Immediate ~D" x))))
      when (and funobj
		(typep operand 'ia-x86::operand-indirect-register)
		(eq 'ia-x86::esi (ia-x86::operand-register operand))
		(member (ia-x86::operand-register2 operand) '(ia-x86::edi nil))
		(= 1 (ia-x86::operand-scale operand))
		#+ignore (= (mod (slot-offset 'movitz-funobj 'constant0) 4)
			    (mod (ia-x86::operand-offset operand) 4))
		(<= 12 (ia-x86::operand-offset operand)))
      collect (format nil "~A"
		      (nth (truncate (- (+ (ia-x86::operand-offset operand)
					   (if (eq 'ia-x86::edi (ia-x86::operand-register2 operand))
					       (image-nil-word *image*)
					     0))
					(slot-offset 'movitz-funobj 'constant0))
				     4)
			   (movitz-funobj-const-list funobj)))
      when (and funobj
		(typep operand 'ia-x86::operand-indirect-register)
		(eq 'ia-x86::esi (ia-x86::operand-register2 operand))
		(eq 'ia-x86::edi (ia-x86::operand-register operand))
		(<= 12 (ia-x86::operand-offset operand)))
      collect (format nil "~A" (nth (truncate (- (+ (ia-x86::operand-offset operand)
						    (* (ia-x86::operand-scale operand)
						       (image-nil-word *image*)))
						 (slot-offset 'movitz-funobj 'constant0))
					      4)
				    (movitz-funobj-const-list funobj)))
      when (typep operand 'ia-x86::operand-rel-pointer)
      collect (let* ((x (+ pc
			   (imagpart (ia-x86::instruction-original-datum instruction))
			   (length (ia-x86:instruction-prefixes instruction))
			   (ia-x86::operand-offset operand)))
		     (label (and funobj (car (find x (movitz-funobj-symtab funobj) :key #'cdr)))))
		(if label
		    (format nil "branch to ~S at ~D" label x)
		  (format nil "branch to ~D" x)))
      when (and (typep operand 'ia-x86::operand-immediate)
		(<= #x100 (ia-x86::operand-value operand) #x10000)
		(= (tag :character) (mod (ia-x86::operand-value operand) 256)))
      collect (format nil "#\\~C" (code-char (truncate (ia-x86::operand-value operand) 256)))
      when (and (typep operand 'ia-x86::operand-immediate)
		(zerop (mod (ia-x86::operand-value operand)
			    +movitz-fixnum-factor+)))
      collect (format nil "#x~X" (truncate (ia-x86::operand-value operand)
					   +movitz-fixnum-factor+))))
		  
(defun movitz-disassemble (name  &rest args &key ((:image *image*) *image*) &allow-other-keys)
  (let* ((funobj (or (movitz-env-named-function name)
                     (error "~S has no function definition." name))))
    (declare (special *image*))
    (apply #'movitz-disassemble-funobj funobj :name name args)))

(defun movitz-assembly (name &optional (*image* *image*))
  (let* ((funobj (movitz-env-named-function name)))
    (declare (special *image*))
    (format t "~{~A~%~}" (movitz-funobj-symbolic-code funobj))))

(defun movitz-disassemble-toplevel (module)
  (let ((funobj (car (find module (image-load-time-funobjs *image*) :key #'second))))
    (assert funobj (module)
      "No load funobj found for module ~S." module)
    (movitz-disassemble-funobj funobj :name module)))

(defun movitz-disassemble-method (name lambda-list &optional qualifiers)
  (let* ((gf (or (movitz-env-named-function name)
		 (error "No function named ~S." name)))
	 (specializing-lambda-list
	  (subseq lambda-list 0
		  (position-if (lambda (x)
				 (and (symbolp x)
				      (char= #\& (char (string x) 0))))
			       lambda-list)))
	 (specializers (mapcar #'muerte::find-specializer
			       (mapcar (lambda (x)
					 (if (consp x)
					     (second x)
					   'muerte.cl::t))
				       specializing-lambda-list)))
	 (method (muerte::movitz-find-method gf qualifiers specializers))
	 (funobj (muerte::movitz-slot-value method 'muerte::function))
	 (*print-base* 16))
    (movitz-disassemble-funobj funobj)))

(defparameter *recursive-disassemble-remember-funobjs* nil)

(defun movitz-foo (funobj &key (name (movitz-funobj-name funobj)) ((:image *image*) *image*)
				  (recursive t))
  (coerce (movitz-vector-symbolic-data (movitz-funobj-code-vector funobj))
	  'list))

#-ia-x86
(defun movitz-disassemble-funobj (funobj &key (name (movitz-funobj-name funobj)) ((:image *image*) *image*)
				  (recursive t))
  (let ((code (coerce (movitz-vector-symbolic-data (movitz-funobj-code-vector funobj))
		      'list))
	(entry-points (loop for slot in '(code-vector%1op code-vector%2op code-vector%3op)
			 for entry-arg-count upfrom 1
			 for entry = (slot-value funobj slot)
			 when (and (consp entry)
				   (eq funobj (cdr entry)))
			 collect (cons (car entry)
				       entry-arg-count))))
    (let ((*print-case* :downcase))
      (format t "~&;; Movitz Disassembly of ~A:
;;  ~D Constant~:P~@[: ~A~].
~:{~4D: ~16<~{ ~2,'0X~}~;~> ~A~@[ ;~{ ~A~}~]~%~}"
	      (movitz-print (or (movitz-funobj-name funobj) name))
	      (length (movitz-funobj-const-list funobj))
	      (movitz-funobj-const-list funobj)
	      (loop with pc = 0
		 for (data . instruction) in (let ((asm-x86:*cpu-mode* :32-bit))
					       (asm:disassemble-proglist code
									 :symtab (movitz-funobj-symtab funobj)
									 :collect-data t))
		 when (assoc pc entry-points)
		 collect (list pc nil
			       (format nil "  => Entry-point for ~D arguments <=" (cdr (assoc pc entry-points)))
			       nil)
		 when (let ((x (find pc (movitz-funobj-symtab funobj) :key #'cdr)))
			(when x (list pc (list (format nil "  ~A" (car x))) "" nil)))
		 collect it
		 collect (list pc data instruction (comment-instruction instruction funobj pc))
		 do (incf pc (length data))))))
  (when recursive
    (let ((*recursive-disassemble-remember-funobjs*
	   (cons funobj *recursive-disassemble-remember-funobjs*)))
      (loop for x in (movitz-funobj-const-list funobj)
	 do (when (and (typep x '(and movitz-funobj (not movitz-funobj-standard-gf)))
		       (not (member x *recursive-disassemble-remember-funobjs*)))
	      (push x *recursive-disassemble-remember-funobjs*)
	      (terpri)
	      (movitz-disassemble-funobj x))))))
  
  

#+ia-x86
(defun movitz-disassemble-funobj (funobj &key (name (movitz-funobj-name funobj)) ((:image *image*) *image*)
				  (recursive t))
  (let* ((code-vector (movitz-funobj-code-vector funobj))
	 (code (map 'vector #'identity
		    (movitz-vector-symbolic-data code-vector)))
	 (code-position 0)
	 (entry-points (map 'list #'identity (subseq code (movitz-vector-fill-pointer code-vector)))))
    (format t "~&;; Movitz Disassembly of ~A:~@[
;;  ~D Constants: ~A~]
~:{~4D: ~16<~{ ~2,'0X~}~;~> ~A~@[ ;~{ ~A~}~]~%~}"
	    (movitz-print (or (movitz-funobj-name funobj) name))
	    (length (movitz-funobj-const-list funobj))
	    (movitz-funobj-const-list funobj)
	    (loop
	       for pc = 0 then code-position
	       for instruction = (ia-x86:decode-read-octet
				  #'(lambda ()
				      (when (< code-position
					       (movitz-vector-fill-pointer code-vector))
					(prog1
					    (aref code code-position)
					  (incf code-position)))))
	       for cbyte = (and instruction
				(ia-x86::instruction-original-datum instruction))
	       until (null instruction)
	       when (let ((x (find pc (movitz-funobj-symtab funobj) :key #'cdr)))
		      (when x (list pc (list (format nil "  ~S" (car x))) "" nil)))
	       collect it
	       when (some (lambda (x)
			    (and (plusp pc) (= pc x)))
			  entry-points)
	       collect (list pc nil
			     (format nil "  => Entry-point for ~D arguments <="
				     (1+ (position-if (lambda (x)
							(= pc x))
						      entry-points)))
			     nil)
	       collect (list pc
			     (ia-x86::cbyte-to-octet-list cbyte)
			     instruction
			     (comment-instruction instruction funobj pc)))))
  (when recursive
    (let ((*recursive-disassemble-remember-funobjs*
	   (cons funobj *recursive-disassemble-remember-funobjs*)))
      (loop for x in (movitz-funobj-const-list funobj)
	 do (when (and (typep x '(and movitz-funobj (not movitz-funobj-standard-gf)))
		       (not (member x *recursive-disassemble-remember-funobjs*)))
	      (push x *recursive-disassemble-remember-funobjs*)
	      (terpri)
	      (movitz-disassemble-funobj x)))))
  (values))

#-ia-x86
(defun movitz-disassemble-primitive (name &optional (*image* *image*))
  (let* ((code-vector (cond
		       ((slot-exists-p (image-run-time-context *image*) name)
			(slot-value (image-run-time-context *image*) name))
		       (t (movitz-symbol-value (movitz-read name)))))
	 (code (coerce (movitz-vector-symbolic-data code-vector)
		       'list)))
    (format t "~&;; Movitz disassembly of ~S:
~:{~4D: ~16<~{ ~2,'0X~}~;~> ~A~@[ ;~{ ~A~}~]~%~}"
	    name
	    (loop with pc = 0
	       for (data . instruction) in (asm:disassemble-proglist code :collect-data t)
	       collect (list pc
			     data
			     instruction
			     (comment-instruction instruction nil pc))
	       do (incf pc (length data))))
    (values)))

#+ia-x86
(defun movitz-disassemble-primitive (name &optional (*image* *image*))
  (let* ((code-vector (cond
		       ((slot-exists-p (image-run-time-context *image*) name)
			(slot-value (image-run-time-context *image*) name))
		       (t (movitz-symbol-value (movitz-read name)))))
	 (code (map 'vector #'identity
		    (movitz-vector-symbolic-data code-vector)))
	 (code-position 0))
    (format t "~&;; Movitz disassembly of ~S:
~:{~4D: ~16<~{ ~2,'0X~}~;~> ~A~@[ ;~{ ~A~}~]~%~}"
	    name
	    (loop
		for pc = 0 then code-position
		for instruction = (ia-x86:decode-read-octet
				   #'(lambda ()
				       (when (< code-position (length code))
					 (prog1
					     (aref code code-position)
					   (incf code-position)))))
		until (null instruction)
		for cbyte = (ia-x86::instruction-original-datum instruction)
		collect (list pc
			      (ia-x86::cbyte-to-octet-list cbyte)
			      instruction
			      (comment-instruction instruction nil pc))))
    (values)))

(defmethod image-read-intern-constant ((*image* symbolic-image) expr)
  (typecase expr
    (string
     (or (gethash expr (image-string-constants *image*))
	 (setf (gethash expr (image-string-constants *image*))
	   (movitz-read expr))))
    (cons
     (or (gethash expr (image-cons-constants *image*))
	 (setf (gethash expr (image-cons-constants *image*))
	   (movitz-read expr))))
    (t (movitz-read expr))))

;;; "Reader"

(defmethod image-lisp-to-movitz-object ((image symbolic-image) lisp-object)
  (gethash lisp-object (image-read-map-hash image)))

(defmethod (setf image-lisp-to-movitz-object) (movitz-object (image symbolic-image) lisp-object)
  (setf (gethash movitz-object (image-inverse-read-map-hash image)) lisp-object
	(gethash lisp-object (image-read-map-hash image)) movitz-object))

(defmethod image-movitz-to-lisp-object ((image symbolic-image) movitz-object)
  (gethash movitz-object (image-inverse-read-map-hash image)))

(defmacro with-movitz-read-context (options &body body)
  (declare (ignore options))
  `(let ((*movitz-reader-clean-map*
	  (if (boundp '*movitz-reader-clean-map*)
	      (symbol-value '*movitz-reader-clean-map*)
	    (make-hash-table :test #'eq))))
     (declare (special *movitz-reader-clean-map*))
     ,@body))

(defun movitz-read (expr &optional re-read)
  "Map native lisp data to movitz-objects. Makes sure that when two EXPR are EQ, ~@
   the Movitz objects are also EQ, under the same image."
  (declare (optimize (debug 3) (speed 0)))
  (with-movitz-read-context ()
    (when (typep expr 'movitz-object)
      (return-from movitz-read expr))
    (or (unless re-read
	  (let ((old-object (image-lisp-to-movitz-object *image* expr)))
	    (when (and old-object
		       (not (gethash old-object *movitz-reader-clean-map*)))
	      (setf (gethash old-object *movitz-reader-clean-map*) t)
	      (update-movitz-object old-object expr))
	    old-object))
	(setf (image-lisp-to-movitz-object *image* expr)
	      (etypecase expr
		(null *movitz-nil*)
		((member t) (movitz-read 'muerte.cl:t))
		((eql unbound) (make-instance 'movitz-unbound-value))
		(symbol (intern-movitz-symbol expr))
		(integer (make-movitz-integer expr))
		(character (make-movitz-character expr))
		(string (or (gethash expr (image-string-constants *image*))
			    (setf (gethash expr (image-string-constants *image*))
				  (make-movitz-string expr))))
		(vector (make-movitz-vector (length expr)
					    :element-type (array-element-type expr)
					    :initial-contents expr))
		(cons
		 (or (let ((old-cons (gethash expr (image-cons-constants *image*))))
		       (when old-cons
			 (update-movitz-object old-cons expr)
			 old-cons))
		     (setf (gethash expr (image-cons-constants *image*))
			   (if (eq '#0=#:error
				   (ignore-errors
				     (when (not (list-length expr))
				       '#0#)))
			       (multiple-value-bind (unfolded-expr cdr-index)
				   (unfold-circular-list expr)
				 (let ((result (movitz-read unfolded-expr)))
				   (setf (movitz-last-cdr result)
					 (movitz-nthcdr cdr-index result))
				   result))
			       (make-movitz-cons (movitz-read (car expr))
						 (movitz-read (cdr expr)))))))
		(hash-table
		 (make-movitz-hash-table expr))
		(pathname
		 (make-instance 'movitz-struct
				:class (muerte::movitz-find-class 'muerte::pathname)
				:length 1
				:slot-values (list (movitz-read (namestring expr)))))
		(complex
		 (make-instance 'movitz-struct
				:class (muerte::movitz-find-class 'muerte::complex)
				:length 2
				:slot-values (list (movitz-read (realpart expr))
						   (movitz-read (imagpart expr)))))
		(ratio
		 (make-instance 'movitz-ratio
				:value expr))
		(structure-object
		 (let ((slot-descriptions (gethash (type-of expr)
						   (image-struct-slot-descriptions *image*)
						   nil)))
		   (unless slot-descriptions
		     (error "Don't know how to movitz-read struct: ~S" expr))
		   (let ((movitz-object (make-instance 'movitz-struct
						       :class (muerte::movitz-find-class (type-of expr))
						       :length (length slot-descriptions))))
		     (setf (image-lisp-to-movitz-object *image* expr) movitz-object)
		     (setf (slot-value movitz-object 'slot-values)
			   (mapcar #'(lambda (slot)
				       (movitz-read (slot-value expr (if (consp slot) (car slot) slot))))
				   slot-descriptions))
		     movitz-object)))
		(float			; XXX
		 (movitz-read (rationalize expr)))
		(class
		 (muerte::movitz-find-class (translate-program (class-name expr)
							       :cl :muerte.cl)))
		(array			; XXX
		 (movitz-read nil)))))))

;;;

(defun movitz-make-upload-form (object &optional (quotep t))
  "Not completed."
  (typecase object
    ((or movitz-null null) "()")
    (cons
     (format nil "(list~{ ~A~})"
	     (mapcar #'movitz-make-upload-form object)))
    (movitz-cons
     (format nil "(list~{ ~A~})"
	     (mapcar #'movitz-make-upload-form (movitz-print object))))
    (movitz-funobj
     (format nil "(internal:make-funobj :name ~A :constants ~A :code-vector ~A)"
	     (movitz-make-upload-form (movitz-funobj-name object))
	     (movitz-make-upload-form (movitz-funobj-const-list object))
	     (movitz-print (movitz-funobj-code-vector object))))
    (movitz-symbol
     (let ((package (movitz-symbol-package object)))
       (cond
	((eq *movitz-nil* package) 
	 (if (member :setf-placeholder (movitz-symbol-flags object))
	     (format nil "(internal:setf-intern ~A)"
		     (movitz-make-upload-form (movitz-symbol-value object)))
	   (format nil "~:[~;'~]#:~A" quotep (movitz-print object))))
	(t (check-type package movitz-struct)
	   (assert (eq (movitz-struct-class package)
		       (muerte::movitz-find-class 'muerte::package-object)))
	   (let ((package-name (intern (movitz-print (first (movitz-struct-slot-values package))))))
	     (case package-name
	       (keyword (format nil ":~A" (movitz-print object)))
	       (common-lisp (format nil "~:[~;'~]~A" quotep (movitz-print object)))
	       (t (format nil "~:[~;'~]~A:~A" quotep package-name (movitz-print object)))))))))
    (movitz-basic-vector
     (case (movitz-vector-element-type object)
       (:character (format nil "\"~A\"" (movitz-print object)))
       (t (movitz-print object))))
    (t (format nil "~A" (movitz-print object)))))
      

(defun movitz-upload-function (name &optional (destination :bochs) (verbose nil))
  (unless (stringp destination)
    (setf destination
      (ecase destination
	(:kayak "fe80::240:f4ff:fe36:6f02%xl0")
	(:decpc "fe80::240:5ff:fe18:66d7%xl0")
	(:bochs "fe80::240:5ff:fe18:66d8%xl0"))))
  (let ((funobj (movitz-env-symbol-function name))
	(*print-readably* t)
	(*print-pretty* nil)
	(*print-base* 16)
	(*print-radix* nil))
    (let ((command (format nil "(internal:install-function ~A (list~{ ~A~}) ~W)"
			   (movitz-make-upload-form (movitz-read name))
			   (mapcar #'movitz-make-upload-form (movitz-funobj-const-list funobj))
			   (movitz-print (movitz-funobj-code-vector funobj)))))
      (when verbose
	(pprint command) (terpri) (force-output))
      command
      #+allegro (if destination
		    (excl::run-shell-command (format nil "./udp6-send.py ~A 1 ~S" destination command))
		  command))))
	    

;;; "Printer"

(defun movitz-print (expr)
  "Find the host lisp object equivalent to the Movitz object expr."
  (etypecase expr
    (integer expr)
    (symbol expr)
    (array expr)
    (cons (mapcar #'movitz-print expr))
    ((or (satisfies movitz-null) movitz-run-time-context) nil)
    (movitz-unbound-value 'unbound)
    (movitz-fixnum
     (movitz-fixnum-value expr))
    (movitz-std-instance expr)
    (movitz-struct expr)
    (movitz-heap-object
     (or (image-movitz-to-lisp-object *image* expr)
	 (error "Unknown Movitz object: ~S" expr)))))

(defmethod make-toplevel-funobj ((*image* symbolic-image))
  (declare (special *image*))
  (let ((toplevel-code (loop for (funobj) in (image-load-time-funobjs *image*)
			   collect `(muerte::simple-funcall ,funobj)))
	;; We need toplevel-funobj's identity in the code below.
	(toplevel-funobj (make-instance 'movitz-funobj-pass1)))
    (make-compiled-funobj 'muerte::toplevel-function ()
			  '((muerte::without-function-prelude))
			  `(muerte.cl:progn
			     (muerte::with-inline-assembly (:returns :nothing)
			       (:cli)
			       (:cld)	; clear direction flag => "normal" register GC roots.

			       (:movw ,(1- (* 8 5)) (:esp -6))
			       (:movl ,(+ (movitz-read-and-intern
					   'muerte::*initial-segment-descriptor-table* 'word)
					  (image-ds-segment-base *image*))
				      :ecx)
			       (:movl (:ecx ,(bt:slot-offset 'movitz-symbol 'value))
				      :ecx)
			       (:addl ,(+ (bt:slot-offset 'movitz-basic-vector 'data)
					  (image-ds-segment-base *image*))
				      :ecx)
			       (:movl :ecx (:esp -4))
			       (:lgdt (:esp -6))

			       ;; Move to new CS
			       (:pushl ,(ash (* 3 8) 0)) ; push segment selector
			       (:call (:pc+ 0)) ; push EIP
			      jmp-base
			       (:subl '(:funcall ,(lambda (base dest)
						    (+ (image-cs-segment-base *image*) (- dest) base))
					
					'jmp-base 'jmp-destination)
				      (:esp))
			       (:jmp-segment (:esp))
			      jmp-destination
			       
			       (:movw ,(* 4 8) :cx)
			       (:movw :cx :ds)
			       (:movw :cx :es)
			       (:movw :cx :fs)
			       (:movw :cx :ss)
			       (:movw ,(* 2 8) :cx)
			       (:movw :cx :gs) ; physical context segment

			       (:movl ,(image-nil-word *image*) :edi)
			       (:globally (:movl (:edi (:edi-offset stack-top)) :esp))

			       (:pushl #x37ab7378)
			       (:pushl #x37ab7378)
			       (:pushl 0)
			       (:pushl 0)
			       (:movl :esp :ebp)

			       (:movl '(:funcall ,(lambda () (movitz-intern toplevel-funobj)))
				      :esi)
			       (:pushl :esi)
			       (:pushl :edi)
			       (:cmpl #x2badb002 :eax)
			       (:jne 'no-multiboot)
			       (:movl ,(movitz-read-and-intern 'muerte::*multiboot-data* 'word)
				      :eax)
			       ;; (:compile-form (:result-mode :eax) 'muerte::*multiboot-data*)
			       ;; (:shll ,+movitz-fixnum-shift+ :ebx)
			       (:movl :ebx (:eax ,(bt:slot-offset 'movitz-symbol 'value)))
			      no-multiboot)
			       			       ;; Check that the stack works..
;;;			       (:pushl #xabbabeef)
;;;			       (:popl :eax)
;;;			       (:cmpl #xabbabeef :eax)
;;;			       (:jne '(:sub-program (stack-doesnt-work)
;;;				       (:movl :ebp :eax)
;;;				       (:movl #xb8020 :ebx)
;;;				       ,@(mkasm-write-word-eax-ebx)
;;;				       (:movl (:edi -1) :eax)
;;;				       (:movl #xb8040 :ebx)
;;;				       ,@(mkasm-write-word-eax-ebx)
;;;				       (:jmp (:pc+ -2)))))

			     ,@toplevel-code
			     (muerte::halt-cpu))
			  nil t :funobj toplevel-funobj)))

(defun mkasm-write-word-eax-ebx ()
  (let ((loop-label (make-symbol "write-word-loop"))
	(l1 (make-symbol "write-word-l1"))
	(l2 (make-symbol "write-word-l2"))
	(l3 (make-symbol "write-word-l3"))
	(l4 (make-symbol "write-word-l4")))
    `(;; (:compile-two-forms (:eax :ebx) ,word ,dest)
      (:movl :eax :edx)

      ;; (:shrl #.los0::+movitz-fixnum-shift+ :ebx)
      (:movb 2 :cl)

      ((:gs-override) :movl #x07000700 (:ebx 0))
      ((:gs-override) :movl #x07000700 (:ebx 4))
      ((:gs-override) :movl #x07000700 (:ebx 8))
      ((:gs-override) :movl #x07000700 (:ebx 12))
      ,loop-label

      (:andl #x0f0f0f0f :eax)
      (:addl #x30303030 :eax)

      (:cmpb #x39 :al) (:jle ',l1) (:addb 7 :al)
      ,l1 ((:gs-override) :movb :al (14 :ebx)) ; 8
      (:cmpb #x39 :ah) (:jle ',l2) (:addb 7 :ah)
      ,l2 ((:gs-override) :movb :ah (10 :ebx)) ; 6

      (:shrl 16 :eax)
      
      (:cmpb #x39 :al) (:jle ',l3) (:addb 7 :al)
      ,l3 ((:gs-override) :movb :al (6 :ebx)) ; 4
      (:cmpb #x39 :ah) (:jle ',l4) (:addb 7 :ah)
      ,l4 ((:gs-override) :movb :ah (2 :ebx)) ; 2

      (:movl :edx :eax)
      (:shrl 4 :eax)
      (:subl 2 :ebx)
      (:decb :cl)
      (:jnz ',loop-label))))
    

;;;

