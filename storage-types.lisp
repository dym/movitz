;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      storage-types.lisp
;;;; Description:   Physical storage structures for Movitz objects.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Oct 22 00:22:43 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: storage-types.lisp,v 1.65 2008-04-27 19:23:25 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(define-unsigned lu64 8 :little-endian)

(define-bitfield segment-descriptor (lu64)
  (((:numeric limit0 16 0))
   ((:numeric limit1 4 48))
   ((:numeric base0 24 16))
   ((:numeric base1 8 56))
   ((:numeric type 4 40))
   ((:numeric dpl 2 45))
   ((:bits)
    s 44
    p 47
    avl 52
    reserved 53
    d/b 54
    g 55)))

(defun make-segment-descriptor (&key (limit 0) (base 0) (type 0) (dpl 0) (flags nil))
  (check-type limit (unsigned-byte 20))
  (check-type base (unsigned-byte 32))
  `((limit0 . ,(ldb (byte 16 0) limit))
    (limit1 . ,(ldb (byte 4 16) limit))
    (base0  . ,(ldb (byte 24 0) base))
    (base1  . ,(ldb (byte 8 24) base))
    (type   . ,type)
    (dpl    . ,dpl)
    ,@flags))

(defmacro with-image-stream-position-remembered (opts &body body)
  (declare (ignore opts))
  (let ((v (gensym)))
    `(let ((,v (file-position (image-stream *image*))))
       (unwind-protect (progn ,@body)
	 (file-position (image-stream *image*) ,v)))))

(define-enum other-type-byte (u8)
  :fixnum 0
  :even-fixnum 0
  :odd-fixnum 4
  :cons 1
  :character 2
  :tag0 0
  :tag1 1
  :tag2 2
  :tag3 3				; unused
  :tag4 4
  :tag5 5
  :tag6 6
  :tag7 7
  ;; :immediate 4
  :null 5
  :other 6
  :symbol 7

  ;; The lower 2 bits of these are significant in mysterious ways.
  ;; 10: Requires GC parsing.
  ;; 00: Requires no GC parsing (all GC-safe lisp-vals).
  ;; 11: Illegal/special values
  :basic-vector #x22
  :defstruct #x2a
  :basic-restart #x32
  :funobj #x3a
  :bignum #x4a
  :ratio #x52
  :complex #x5a
  :std-instance #x40
  :run-time-context #x62
  :illegal #x13
  :infant-object #x23)

(defconstant +fixnum-tags+ '(:even-fixnum :odd-fixnum))
(defparameter +scan-skip-word+ #x00000003)

(defun tag (type &optional (wide-tag 0))
  (logior (bt:enum-value 'other-type-byte type)
	  (ash wide-tag 8)))

(defun tag-name (number)
  (find number '(:even-fixnum :odd-fixnum :cons :character :null :other :symbol)
	:key 'tag))

(defun extract-tag (word)
  (tag-name (ldb (byte 3 0) word)))

(defun extract-pointer (word)
  (logand word #xfffffff8))

(defun slot-map (type &optional (offset 0))
  (let ((slots (binary-record-slot-names type)))
    (loop for slot in slots
	as o = (- (bt:slot-offset type slot) offset)
	collect (list (intern (symbol-name slot) :muerte)
		      (intern (symbol-name (binary-slot-type type slot)) :muerte)
		      (truncate o 4)
		      (rem o 4)))))

(define-unsigned word 4 :little-endian)
(define-unsigned code-vector-word 4 :little-endian) ; A word that points to a code-vector, +2
(define-unsigned code-pointer 4 :little-endian) ; A pointer anywhere, pointing to code.

(defclass movitz-object ()
  ((browsed-slots
    :initarg :browser-properties
    :initform nil
    :accessor movitz-object-browser-properties)))

(defclass movitz-immediate-object (movitz-object) ())
(defclass movitz-heap-object (movitz-object)
  ((word
    :accessor movitz-heap-object-word)))
(defclass movitz-heap-object-other (movitz-heap-object) ())

(defmethod movitz-object-offset ((obj movitz-heap-object-other)) 6)
(defmethod movitz-storage-alignment ((obj movitz-heap-object)) 8)
(defmethod movitz-storage-alignment-offset ((obj movitz-heap-object)) 0)

;;;

(defgeneric movitz-references (obj)
  (:documentation "Return the objects referenced by OBJ."))

(defmethod movitz-references (obj)
  (mapcar #'(lambda (slot)
	      (slot-value obj slot))
	  (binary-record-slot-names (find-binary-type (type-of obj)))))


(defmethod movitz-intern ((obj movitz-heap-object) &optional type)
  (declare (ignore type))
  (image-intern-object *image* obj))

(defmethod movitz-intern ((obj movitz-immediate-object) &optional type)
  (declare (ignore type))
  (movitz-immediate-value obj))

(defun movitz-read-and-intern (expr type)
  (ecase type
    (word
     (cond
      ((typep expr 'movitz-object)
       (movitz-intern expr))
      (t (movitz-intern (movitz-read expr)))))
    (code-vector-word
     (movitz-intern-code-vector expr))))

(defmethod update-movitz-object ((obj movitz-heap-object) lisp-obj)
  (declare (ignore lisp-obj))
  (break "Don't know how to update ~W." obj))

(defmethod update-movitz-object ((obj movitz-immediate-object) lisp-obj)
  (declare (ignore lisp-obj))
  (values))
  
;;; Fixnums

(eval-when (:compile-toplevel :execute :load-toplevel)
  (defparameter +movitz-fixnum-bits+ 30)
  (defparameter +movitz-fixnum-shift+ (- 32 +movitz-fixnum-bits+))
  (defparameter +movitz-fixnum-factor+ (expt 2 +movitz-fixnum-shift+))
  (defparameter +movitz-fixnum-zmask+ (1- +movitz-fixnum-factor+))
  (defparameter +movitz-most-positive-fixnum+ (1- (expt 2 (1- +movitz-fixnum-bits+))))
  (defparameter +movitz-most-negative-fixnum+ (- (expt 2 (1- +movitz-fixnum-bits+))))

  (defparameter +object-pointer-shift+ 0)
  (defparameter +other-type-offset+ (- -6 +object-pointer-shift+)))

(defun fixnum-integer (word)
  "For a Movitz word, that must be a fixnum, return the corresponding
integer (native lisp) value."
  (assert (member (extract-tag word) +fixnum-tags+) (word)
    "The word ~W is not a fixnum." word)
  (let ((x (ldb (byte (1- +movitz-fixnum-bits+)
		      (- 32 +movitz-fixnum-bits+))
		word)))
    (if (logbitp 31 word)
	(- (1+ (logxor x +movitz-most-positive-fixnum+)))
      x)))

(define-binary-class movitz-fixnum (movitz-immediate-object)
  ((value :binary-type word
	  :initarg :value
	  :reader movitz-fixnum-value)))

(defmethod print-object ((object movitz-fixnum) stream)
  (print-unreadable-object (object stream :type t)
    (write (movitz-fixnum-value object) :stream stream))
  object)

(defun make-movitz-fixnum (value)
  (check-type value (signed-byte #.+movitz-fixnum-bits+))
  (make-instance 'movitz-fixnum :value value))

(defmethod movitz-immediate-value ((obj movitz-fixnum))
  (dpb (movitz-fixnum-value obj)
       (byte +movitz-fixnum-bits+ (- 32 +movitz-fixnum-bits+))
       0))

(defclass movitz-unboxed-integer (movitz-immediate-object) ())
(defclass movitz-unboxed-integer-u8 (movitz-unboxed-integer) ())
(defclass movitz-unboxed-integer-u32 (movitz-unboxed-integer) ())

;;; Characters

(define-binary-class movitz-character (movitz-immediate-object)
  ((char :binary-type word
	 :initarg :char
	 :type character
	 :reader movitz-char)))

(defun make-movitz-character (char)
  (check-type char character)
  (make-instance 'movitz-character :char char))

(defmethod movitz-immediate-value ((obj movitz-character))
  (dpb (char-code (movitz-char obj))
       (byte 8 8)
       (tag :character)))

(defmethod print-object ((x movitz-character) stream)
  (print-unreadable-object (x stream)
    (format stream "MOVITZ-CHARACTER: ~S" (movitz-char x))))

;;; Code element

(define-binary-class movitz-code (movitz-immediate-object)
  ((byte :binary-type (define-unsigned code 1)
	 :reader movitz-code-byte
	 :initarg byte)))

(defun make-movitz-code (byte)
  (make-instance 'movitz-code 'byte byte))    

;;; Conses

(define-binary-class movitz-cons (movitz-heap-object)
  ((car :binary-type word
	:map-binary-write 'movitz-intern
	:map-binary-read-delayed 'movitz-word
	:initarg :car
	:accessor movitz-car)
   (cdr :binary-type word
	:map-binary-write 'movitz-intern
	:map-binary-read-delayed 'movitz-word
	:initarg :cdr
	:accessor movitz-cdr))
  (:slot-align car #.(- -1 +object-pointer-shift+)))

(defmethod movitz-object-offset ((obj movitz-cons)) 1)

(defmethod update-movitz-object ((movitz-cons movitz-cons) (lisp-cons cons))
  (setf (movitz-car movitz-cons) (movitz-read (car lisp-cons))
	(movitz-cdr movitz-cons) (movitz-read (cdr lisp-cons))))

(defun make-movitz-cons (car cdr)
  (check-type car movitz-object)
  (check-type cdr movitz-object)
  (make-instance 'movitz-cons
    :car car
    :cdr cdr))

(defun print-cons (ic stream)
  (typecase (movitz-cdr ic)
    (movitz-null (format stream "~A" (movitz-car ic)))
    (movitz-cons (format stream "~A " (movitz-car ic)))
    (t (format stream "~A . ~A" (movitz-car ic) (movitz-cdr ic)))))

(defun movitz-list-length (x)
  (etypecase x
    (list (list-length x))
    (movitz-null 0)
    (movitz-cons
     (flet ((movitz-endp (x) (eq x *movitz-nil*)))
       (do ((n 0 (+ n 2))		;Counter.
	    (fast x (movitz-cdr (movitz-cdr fast))) ;Fast pointer: leaps by 2.
	    (slow x (movitz-cdr slow)))	;Slow pointer: leaps by 1.
	   (nil)
	 ;; If fast pointer hits the end, return the count.
	 (when (movitz-endp fast) (return n))
	 (when (movitz-endp (movitz-cdr fast)) (return (+ n 1)))
	 ;; If fast pointer eventually equals slow pointer,
	 ;;  then we must be stuck in a circular list.
	 ;; (A deeper property is the converse: if we are
	 ;;  stuck in a circular list, then eventually the
	 ;;  fast pointer will equal the slow pointer.
	 ;;  That fact justifies this implementation.)
	 (when (and (eq fast slow) (> n 0))
	   (warn "Circular list: ~S" x)
	   (return nil)))))))

(defmethod print-object ((obj movitz-cons) stream)
  (format stream "#&(")
  (loop for ic = obj then (movitz-cdr ic) as i from 0 to (or *print-length* 100)
      while (typep ic 'movitz-cons)
      do (print-cons ic stream)
      finally (if (>= i 16)
		  (format stream "...)")
		(format stream ")")))
  obj)

(defun movitz-nthcdr (n movitz-list)
  (if (zerop n)
      movitz-list
    (movitz-nthcdr (1- n) (movitz-cdr movitz-list))))

(defun (setf movitz-last-cdr) (value movitz-list)
  (if (not (typep (movitz-cdr movitz-list) 'movitz-cons))
      (setf (movitz-cdr movitz-list) value)
    (setf (movitz-last-cdr (movitz-cdr movitz-list)) value)))

;;; movitz-vectors

(define-binary-class movitz-basic-vector (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :reader movitz-vector-type
    :initform :basic-vector)
   (element-type
    :binary-type (define-enum movitz-vector-element-type (u8)
		   :any-t 0
		   :character 1
		   :u8 2
		   :u16 3
		   :u32 4
		   :stack 5
		   :bit 6
		   :code 7
		   :indirects 8)
    :initarg :element-type
    :reader movitz-vector-element-type)
   (fill-pointer
    :binary-type lu16
    :initarg :fill-pointer
    :accessor movitz-vector-fill-pointer
    :map-binary-write (lambda (x &optional type)
			(declare (ignore type))
			(check-type x (unsigned-byte 14))
			(* x 4))
    :map-binary-read (lambda (x &optional type)
		       (declare (ignore type))
		       (assert (zerop (mod x 4)))
		       (truncate x 4)))
   (num-elements
    :binary-type word
    :initarg :num-elements
    :reader movitz-vector-num-elements
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word-and-print)
   (data
    :binary-lisp-type :label)		; data follows physically here
   (symbolic-data
    :initarg :symbolic-data
    :initform nil
    :accessor movitz-vector-symbolic-data))
  (:slot-align type #.+other-type-offset+))

(defmethod print-object ((object movitz-basic-vector) stream)
  (cond
   ((eq :character (movitz-vector-element-type object))
    (print-unreadable-object (object stream :type t :identity nil)
      (write (map 'string #'identity (movitz-vector-symbolic-data object))
	     :stream stream))
    object)
   (t (call-next-method))))
    
(defun basic-vector-type-tag (element-type)
  (dpb (enum-value 'movitz-vector-element-type element-type)
       (byte 8 8)
       (enum-value 'other-type-byte :basic-vector)))

(defun movitz-type-word-size (type)
  "What's the size of TYPE in words?"
  (truncate (sizeof (intern (symbol-name type) :movitz)) 4))

(defun movitz-svref (vector index)
  (elt (movitz-vector-symbolic-data vector) index))

(defun movitz-vector-element-type-size (element-type)
  (ecase element-type
    ((:any-t :u32 :stack) 32)
    ((:character :u8 :code) 8)
    (:u16 16)
    (:bit 1)))

(defmethod update-movitz-object ((movitz-vector movitz-basic-vector) (vector vector))
  (when (eq :any-t (movitz-vector-element-type movitz-vector))
    (loop for i from 0 below (length vector)
	do (setf (aref (movitz-vector-symbolic-data movitz-vector) i)
	     (movitz-read (aref vector i)))))
  (values))

(defmethod write-binary-record ((obj movitz-basic-vector) stream)
  (flet ((write-element (type stream data)
	   (ecase type
	     ((:u8 :code)(write-binary 'u8 stream data))
	     (:u16       (write-binary 'u16 stream data))
	     (:u32       (write-binary 'u32 stream data))
	     (:character (write-binary 'char8 stream data))
	     (:any-t     (write-binary 'word stream (movitz-read-and-intern data 'word))))))
    (+ (call-next-method)		; header
       (multiple-value-bind (data type)
	   (case (movitz-vector-element-type obj)
	     (:bit (let ((data (movitz-vector-symbolic-data obj)))
		     (values (loop for byte upfrom 0 below (ceiling (length data) 8)
				collect (loop for bit from 0 to 7
					   sum (* (let ((b (+ (* byte 8) bit)))
						    (if (< b (length data))
							(bit data b)
							0))
						  (expt 2 bit))))
			     :u8)))
	     (t (values (movitz-vector-symbolic-data obj)
			(movitz-vector-element-type obj))))
	 (etypecase data
	   (list 
	    (loop for datum in data
	       sum (write-element type stream datum)))
	   (vector
	    (loop for datum across data
	       sum (write-element type stream datum))))))))

(defmethod read-binary-record ((type-name (eql 'movitz-basic-vector)) stream &key &allow-other-keys)
  (let ((object (call-next-method)))
    (setf (movitz-vector-symbolic-data object)
      (loop for i from 1 to (movitz-vector-num-elements object)
	  collecting
	    (ecase (movitz-vector-element-type object)
	      ((:u8 :code)(read-binary 'u8 stream))
	      (:u16       (read-binary 'u16 stream))
	      (:u32       (read-binary 'u32 stream))
	      (:character (read-binary 'char8 stream))
	      (:any-t     (let ((word (read-binary 'word stream)))
			    (with-image-stream-position-remembered ()
			      (movitz-word word)))))))
    object))

(defmethod sizeof ((object movitz-basic-vector))
  (+ (call-next-method)
     (ceiling (* (movitz-vector-element-type-size (slot-value object 'element-type))
		 (slot-value object 'num-elements))
	      8)))

(defun movitz-vector-upgrade-type (type)
  (cond
   ((eq type 'code)
    (values :code 0))
   ((subtypep type 'bit)
    (values :bit 0))
   ((subtypep type '(unsigned-byte 8))
    (values :u8 0))
   ((subtypep type '(unsigned-byte 16))
    (values :u16 0))
   ((subtypep type '(unsigned-byte 32))
    (values :u32 0))
   ((subtypep type 'character)
    (values :character #\null))
   (t (values :any-t nil)))
  #+ignore (case type
	     (movitz-unboxed-integer-u8
	      (values :u8 0))
	     (movitz-unboxed-integer-u32
	      (values :u32 0))
	     (movitz-character
	      (values :character #\null))
	     (movitz-code
	      (values :code 0))
	     (t (values :any-t nil))))

(defun make-movitz-vector (size &key (element-type t)
				     (initial-contents nil)
				     (initial-element *movitz-nil* initial-element-p)
				     (alignment 8)
				     (alignment-offset 0)
				     (flags nil)
				     fill-pointer)
  (assert (or (null initial-contents)
	      (= size (length initial-contents))) (size initial-contents)
    "The initial-contents must be the same length as SIZE.")
;;;  (assert (subtypep element-type 'movitz-object) ()
;;;    "ELEMENT-TYPE must be a subtype of MOVITZ-OBJECT.")
;;;  (assert (or initial-contents
;;;	      (not initial-element-p)
;;;	      (typep initial-element element-type)) ()
;;;    "INITIAL-ELEMENT's type ~A is not of ELEMENT-TYPE ~A."
;;;    (type-of initial-element) element-type)
  (assert (and (>= (log alignment 2) 3)
	       (zerop (rem (log alignment 2) 1)))
      (alignment)
    "Illegal alignment: ~A." alignment)
  (multiple-value-bind (et default-element)
      (movitz-vector-upgrade-type element-type)
    (when initial-element-p
      (assert (not initial-contents) ()
	"Can't provide both initial-element and initial-contents."))
    (unless initial-contents
      (setf initial-contents
	(make-array size :initial-element (or (and initial-element-p initial-element)
					      default-element))))
    (assert (member et '(:any-t :bit :character :u8 :u32 :code)))
    (when flags (break "flags: ~S" flags))
    (when (and alignment-offset (plusp alignment-offset))
      (break "alignment: ~S" alignment-offset))
    (make-instance 'movitz-basic-vector
      :element-type et
      :num-elements size
      :symbolic-data (case et
		       (:any-t
			(map 'vector #'movitz-read initial-contents))
		       (t initial-contents))
      :fill-pointer (cond
		     ((not (typep size '(unsigned-byte 14)))
		      0)
		     ((integerp fill-pointer)
		      fill-pointer)
		     (t size)))))

(defun make-movitz-string (string)
  (make-movitz-vector (length string)
		   :element-type 'character
		   :initial-contents (map 'list #'identity string)))

(defun movitz-stringp (x)
  (and (typep x '(or movitz-basic-vector))
       (eq :character (movitz-vector-element-type x))))

(deftype movitz-string ()
  '(satisfies movitz-stringp))

;;;

(define-binary-class movitz-unbound-value (movitz-immediate-object)
  ())

(defmethod movitz-intern ((obj movitz-unbound-value) &optional type)
  (declare (ignore type))
  #x7fffffff)

;;; Symbols

(define-binary-class movitz-symbol (movitz-heap-object)
  ((function-value
    :binary-type word
    :accessor movitz-symbol-function-value
    :map-binary-write 'movitz-read-and-intern-function-value
    :map-binary-read-delayed 'movitz-word
    :initarg :function-value
    :initform 'muerte::unbound-function)
   (value
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initform 'unbound
    :accessor movitz-symbol-value
    :initarg :value)
   (plist
    :binary-type word
    :accessor movitz-plist
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initform nil
    :initarg :plist)
   (name
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :name
    :accessor movitz-symbol-name)
   (package
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initform nil
    :accessor movitz-symbol-package)
   (flags
    :binary-type (define-bitfield movitz-symbol-flags (lu16)
		   (((:bits)
		     :special-variable 3
		     :constant-variable 4
		     :setf-placeholder 5)))
    :accessor movitz-symbol-flags
    :initarg :flags
    :initform nil)
   (hash-key
    :binary-lisp-type lu16
    :reader movitz-symbol-hash-key
    :initarg :hash-key)
   (lisp-symbol
    :initform nil
    :initarg :lisp-symbol))
  (:slot-align function-value -7))

#+ignore
(defmethod write-binary-record :before ((obj movitz-symbol) stream)
  (declare (ignore stream))
  (setf (movitz-plist obj)
    (movitz-read
     (translate-program (translate-program (getf (movitz-environment-plists *movitz-global-environment*)
						 (slot-value obj 'lisp-symbol))
					   :cl :muerte.cl)
			:movitz :muerte))))

(defmethod movitz-object-offset ((obj movitz-symbol)) 7)

(defmethod update-movitz-object ((movitz-symbol movitz-symbol) (symbol symbol))
  (setf ;; (movitz-plist movitz-symbol) (movitz-read (symbol-plist symbol))
	(movitz-symbol-name movitz-symbol) (movitz-read (symbol-name symbol)))
  (values))

(defun make-movitz-symbol (name)
  (let ((name-string (image-read-intern-constant *image* (symbol-name name))))
    (make-instance 'movitz-symbol
      :hash-key (movitz-sxhash name-string)
      :name name-string
      :lisp-symbol name)))

(defmethod print-object ((object movitz-symbol) stream)
  (typecase (movitz-symbol-name object)
    (movitz-basic-vector
     (print-unreadable-object (object stream :type 'movitz-symbol)
       (format stream "|~A|"
	       (map 'string #'identity
		    (slot-value (slot-value object 'name) 'symbolic-data))))
     object)
    (t (call-next-method))))

(defun movitz-read-and-intern-function-value (obj type)
  (assert (eq type 'word))
  (cond
   ((typep obj 'movitz-funobj)
    (movitz-intern obj))
   ((symbolp obj)
    (let ((x (movitz-env-named-function obj)))
      (check-type x movitz-funobj)
      (movitz-intern x)))
   (t (error "Illegal function value: ~S." obj))))

;;; NIL


(define-binary-class movitz-null (movitz-symbol) ())

(defun make-movitz-nil ()
  (make-instance 'movitz-null
    :name (symbol-name nil)
    :value nil
    :plist nil
    :hash-key 0
    :flags '(:constant-variable)))

(defmethod movitz-intern ((object movitz-null) &optional (type 'word))
  (assert (eq 'word type))
  (image-nil-word *image*))

(defun movitz-null (x)
  (typep x 'movitz-null))

(deftype movitz-list ()
  `(or movitz-cons movitz-null))

;;; Compiled funobj

(define-binary-class movitz-funobj (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :initform :funobj)
   (funobj-type
    :binary-type (define-enum movitz-funobj-type (u8)
		   :standard-function 0
		   :generic-function 1
		   :method-function 2
		   :macro-function 3)
    :initform :standard-function
    :accessor movitz-funobj-type)
   (debug-info
    ;; Bits 0-4: The value of the start-stack-frame-setup label.
    ;; Bit    5: The code-vector's uses-stack-frame-p.
    :binary-type 'lu16
    :initform 0)
   (code-vector
    :binary-type code-vector-word
    :initform 'muerte::no-code-vector
    :initarg :code-vector
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector
    :accessor movitz-funobj-code-vector)
   (code-vector%1op
    :binary-type code-pointer
    :initform 'muerte::trampoline-funcall%1op
    :initarg :code-vector%1op
    :map-binary-write 'movitz-intern-code-vector
    :accessor movitz-funobj-code-vector%1op)
   (code-vector%2op
    :binary-type code-pointer
    :initform 'muerte::trampoline-funcall%2op
    :initarg :code-vector%2op
    :map-binary-write 'movitz-intern-code-vector
    :accessor movitz-funobj-code-vector%2op)
   (code-vector%3op
    :binary-type code-pointer
    :initform 'muerte::trampoline-funcall%3op
    :initarg :code-vector%3op
    :map-binary-write 'movitz-intern-code-vector
    :accessor movitz-funobj-code-vector%3op)
   (lambda-list
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :reader movitz-funobj-lambda-list
    :initarg :lambda-list)
   (name
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :accessor movitz-funobj-name
    :initarg :name)
   (num-jumpers				; how many of the first constants are jumpers.
    :binary-type lu16			; 14 bits, the lower 16 bits of a fixnum.
    :initform 0				; This, in order to see this as a fixnum while
    :accessor movitz-funobj-num-jumpers	; GC scanning.
    :initarg :num-jumpers
    :map-binary-write (lambda (x &optional type)
			(declare (ignore type))
			(check-type x (unsigned-byte 14))
			(* x +movitz-fixnum-factor+))
    :map-binary-read (lambda (x &optional type)
		       (declare (ignore type))
		       (assert (zerop (ldb (byte 2 0) x)))
		       (/ x +movitz-fixnum-factor+)))
   (num-constants
    :binary-type lu16
    :initform 0
    :initarg :num-constants
    :accessor movitz-funobj-num-constants)
   ;; The funobj's constants follow here..
   (constant0
    :binary-type :label)
   ;; A standard-generic-function will have three constants:
   ;; The class, the slots, and the discriminating-function.
   (const-list				;
    ;; :initform ()
    :initarg :const-list
    :accessor movitz-funobj-const-list)
   (jumpers-map
    :initarg :jumpers-map
    :accessor movitz-funobj-jumpers-map)
   (symbolic-name
    :initarg :symbolic-name
    :accessor movitz-funobj-symbolic-name)
   (symbolic-code 
    :initarg :symbolic-code
    :accessor movitz-funobj-symbolic-code)
   (symtab
    :initform nil
    :accessor movitz-funobj-symtab)
   (borrowed-bindings
    :initarg :borrowed-bindings
    :initform nil
    :accessor borrowed-bindings)
   (function-envs
    :accessor function-envs)
   (funobj-env
    :initarg :funobj-env
    :accessor funobj-env)   
   (extent
    :initarg :extent
    :initform :unused
    :accessor movitz-funobj-extent)
   (allocation
    :accessor movitz-allocation)
   (usage
    :initform nil
    :accessor movitz-funobj-usage)
   (sub-function-binding-usage		; a plist used during lexical analysis
    :initform nil
    :accessor sub-function-binding-usage)
   (entry-protocol
    :initform :default
    :initarg :entry-protocol
    :reader funobj-entry-protocol)
   (headers-on-stack-frame-p
    :initform nil
    :accessor headers-on-stack-frame-p))
  (:slot-align type #.+other-type-offset+))

(defmethod write-binary-record ((obj movitz-funobj) stream)
  (declare (special *record-all-funobjs*))
  (assert (movitz-funobj-code-vector obj) (obj)
    "No code-vector for funobj named ~S." (movitz-funobj-name obj))
  #+ignore
  (assert (= (movitz-funobj-num-constants obj)
	     (length (movitz-funobj-const-list obj))))
  (+ (call-next-method)			; header
     (loop for data in (movitz-funobj-const-list obj)
	 as pos upfrom 0
	 summing (if (>= pos (movitz-funobj-num-jumpers obj))
		     (write-binary 'word stream (movitz-intern data))
		   (let ((x (cdr (assoc data (movitz-funobj-symtab obj)))))
		     (assert (integerp x) ()
		       "Unable to resolve jumper ~S." data)
		     (write-binary 'u32 stream
				   (+ x (movitz-intern-code-vector (movitz-funobj-code-vector obj)))))))))

(defmethod print-object ((object movitz-funobj) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (write (movitz-print (movitz-funobj-name object)) :stream stream)))

(defmethod sizeof ((obj movitz-funobj))
  (+ (sizeof (find-binary-type 'movitz-funobj))
     (* (movitz-funobj-num-constants obj)
	(sizeof 'word))))

(defun make-movitz-funobj (lambda-list &key (name ""))
  (check-type name (or symbol cons))
  (make-instance 'movitz-funobj
    :lambda-list lambda-list
    :name name))

(defun funobj-name (x)
  (typecase x
    (movitz-funobj
     (movitz-funobj-name x))))

;;;

(define-binary-class movitz-funobj-standard-gf (movitz-funobj)
  ;; This class is binary congruent with movitz-funobj.
  ((type
    :binary-type other-type-byte)
   (funobj-type
    :binary-type movitz-funobj-type
    :initform :generic-function)
   (debug-info
    ;; Bits 0-4: The value of the start-stack-frame-setup label.
    :binary-type 'lu16
    :initform 0)
   (code-vector
    :binary-type code-vector-word
    :initform 'muerte::standard-gf-dispatcher
    :map-binary-write 'movitz-intern-code-vector
    :map-binary-read-delayed 'movitz-word-code-vector)
   (code-vector%1op
    :initform 'muerte::standard-gf-dispatcher%1op
    :binary-type code-pointer
    :map-binary-write 'movitz-intern-code-vector)
   (code-vector%2op
    :initform 'muerte::standard-gf-dispatcher%2op
    :binary-type code-pointer
    :map-binary-write 'movitz-intern-code-vector)
   (code-vector%3op
    :initform 'muerte::standard-gf-dispatcher%3op
    :binary-type code-pointer
    :map-binary-write 'movitz-intern-code-vector)
   (lambda-list
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (name
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (num-jumpers
    :binary-type lu16
    :initform 0
    :accessor movitz-funobj-num-jumpers
    :map-binary-write (lambda (x &optional type)
		       (declare (ignore type))
		       (check-type x (unsigned-byte 14))
		       (* x +movitz-fixnum-factor+))
    :map-binary-read (lambda (x &optional type)
		       (declare (ignore type))
		       (assert (zerop (ldb (byte 2 0) x)))
		       (/ x +movitz-fixnum-factor+)))
   (num-constants
    :binary-type lu16
    :initform (/ (- (sizeof 'movitz-funobj-standard-gf)
		    (sizeof 'movitz-funobj))
		 4))			; XXXXXXX MUST MATCH NUMBER OF WORDS BELOW XXXXXXXXXXX
   (standard-gf-function		; a movitz-funobj which is called by dispatcher (in code-vector)
    :accessor standard-gf-function
    :initarg :function
    :initform 'muerte::unbound-function
    :binary-type word
    :map-binary-write 'movitz-read-and-intern-function-value)
   (num-required-arguments
    :initarg :num-required-arguments
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word-and-print)
   (classes-to-emf-table
    :initarg :classes-to-emf-table
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word-and-print)
   (eql-specializer-table
    :initform nil
    :initarg :eql-specializer-table
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word-and-print)
   (standard-gf-class
    :accessor standard-gf-class
    :initarg :class
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (standard-gf-slots
    :accessor standard-gf-slots
    :initarg :slots
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (plist
    :initform nil))
  (:slot-align type #.+other-type-offset+))

(defmethod movitz-funobj-const-list ((funobj movitz-funobj-standard-gf))
  nil)

(defun make-standard-gf (class slots &key lambda-list (name "unnamed")
					  (function 'muerte::unbound-function)
					  num-required-arguments
					  classes-to-emf-table)
  (make-instance 'movitz-funobj-standard-gf
    :lambda-list lambda-list
    :name name
    :class class
    :slots slots
    :function function
    :num-required-arguments num-required-arguments
    :classes-to-emf-table classes-to-emf-table))

;;;

(define-binary-class movitz-struct (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :initform :defstruct)
   (pad :binary-lisp-type 1)
   (length
    :binary-type lu16
    :initarg :length
    :accessor movitz-struct-length
    :map-binary-write (lambda (x &optional type)
			(declare (ignore type))
			(check-type x (unsigned-byte 14))
			(* x 4))
    :map-binary-read (lambda (x &optional type)
		       (declare (ignore type))
		       (assert (zerop (mod x 4)))
		       (truncate x 4)))
   (class
    :binary-type word
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word
    :reader movitz-struct-class
    :initarg :class)
   (slot0 :binary-lisp-type :label)	; the slot values follows here.
   (slot-values
    :initform '()
    :initarg :slot-values
    :accessor movitz-struct-slot-values))
  (:slot-align type #.+other-type-offset+))

(defmethod update-movitz-object ((movitz-struct movitz-struct) lisp-struct)
  (declare (ignore lisp-struct))
  (values))

(defmethod sizeof ((obj movitz-struct))
  (+ (sizeof 'movitz-struct)
     (* 4 (length (movitz-struct-slot-values obj)))))

(defmethod write-binary-record ((obj movitz-struct) stream)
  (+ (call-next-method)			; header
     (loop for slot-value in (movitz-struct-slot-values obj)
	 for slot-word = (movitz-read-and-intern slot-value 'word)
	 summing (write-binary 'word stream slot-word))))

(defmethod read-binary-record ((type-name (eql 'movitz-struct)) stream &key)
  (let ((object (call-next-method)))
    (setf (movitz-struct-slot-values object)
      (loop for i from 1 to (movitz-struct-length object)
	  collect
	    (let ((word (read-binary 'word stream)))
	      (with-image-stream-position-remembered ()
		(movitz-word word)))))
    object))

(defmethod print-object ((object movitz-struct) stream)
  (print-unreadable-object (object stream :type t)
    (format stream "~S" (slot-value object 'class))))

;;;


(defconstant +undefined-hash-key+
    'muerte::--no-hash-key--)

(defun movitz-sxhash (object)
  "Must match the SXHASH function in :cl/hash-tables."
  (typecase object
    (movitz-null
     0)
    (movitz-symbol
     (movitz-symbol-hash-key object))
    (movitz-string
     (let* ((object (movitz-print object))
	    (result (if (not (> (length object) 8))
			0
		      (char-code (char-upcase (aref object (- (length object) 3)))))))
       (dotimes (i (min 8 (length object)))
	 (incf result result)
	 (incf result
	       (if (evenp i)
		   (char-code (char-upcase (aref object i)))
		 (* 7 (char-code (char-upcase (aref object i)))))))
       (ldb (byte 16 0)
	    (+ (* #x10ad (length object))
	       result))))
    (movitz-fixnum
     (movitz-fixnum-value object))
    (t (warn "Don't know how to take SXHASH of ~S." object)
       0)))

(defvar *hash-table-size-factor* 5/4)

(defun find-movitz-hash-table-test (lisp-hash)
  (ecase (hash-table-test lisp-hash)
    ((eq #+clisp ext:fasthash-eq)
     (values 'muerte.cl:eq 'muerte::sxhash-eq))
    ((eql #+clisp ext:fasthash-eql)
     (values 'muerte.cl:eql 'muerte.cl::sxhash))
    ((equal #+clisp ext:fasthash-equal)
     (values 'muerte.cl:equal 'muerte.cl::sxhash))))

(defun make-movitz-hash-table (lisp-hash)
  (let* ((undef (movitz-read +undefined-hash-key+))
	 (hash-count (hash-table-count lisp-hash))
	 (hash-size (logand -2 (truncate (* 2 (+ 7 hash-count)
					    *hash-table-size-factor*))))
	 (bucket-data (make-array hash-size :initial-element undef)))
    (multiple-value-bind (hash-test hash-sxhash)
	(find-movitz-hash-table-test lisp-hash)
      (loop for key being the hash-keys of lisp-hash using (hash-value value)
	  for movitz-key = (movitz-read key)
	  for movitz-value = (movitz-read value)
	  do (loop for pos = (rem (* 2 (movitz-sxhash movitz-key)) hash-size)
		 then (rem (+ 2 pos) hash-size)
		 until (eq undef (svref bucket-data pos))
;;;		 do (warn "Hash collision at ~D of ~D: ~S ~S!"
;;;			  pos hash-size movitz-key (elt bucket-data pos))
;;;	       finally (warn "Hash: pos ~D: ~S ~S" pos movitz-key movitz-value)
;;;	       finally (when (equal "NIL" key)
;;;			 (warn "key: ~S, value: ~S pos: ~S" movitz-key movitz-value pos))
		 finally (setf (svref bucket-data pos) movitz-key
			       (svref bucket-data (1+ pos)) movitz-value)))
      (let* ((bucket (make-movitz-vector hash-size :initial-contents bucket-data))
	     (lh (make-instance 'movitz-struct
		   :class (muerte::movitz-find-class 'muerte::hash-table)
		   :length 4
		   :slot-values (list hash-test ; test-function
				      bucket
				      hash-sxhash
				      hash-count))))
	lh))))

(defmethod update-movitz-object ((movitz-hash movitz-struct) (lisp-hash hash-table))
  "Keep <movitz-hash> in sync with <lisp-hash>."
  (assert (= 4 (length (movitz-struct-slot-values movitz-hash))))
  (let* ((undef (movitz-read +undefined-hash-key+))
	 (old-bucket (second (movitz-struct-slot-values movitz-hash)))
	 (hash-count (hash-table-count lisp-hash))
	 (hash-size (logand -2 (truncate (* 2 (+ 7 hash-count)
					    *hash-table-size-factor*))))
	 (bucket-data (or (and old-bucket
			       (= (length (movitz-vector-symbolic-data old-bucket))
				  hash-size)
			       (fill (movitz-vector-symbolic-data old-bucket) undef))
			  (make-array hash-size :initial-element undef))))
    (multiple-value-bind (hash-test hash-sxhash)
	(find-movitz-hash-table-test lisp-hash)
      (loop for key being the hash-keys of lisp-hash using (hash-value value)
	  for movitz-key = (movitz-read key)
	  for movitz-value = (movitz-read value)
	  do (loop for pos = (rem (* 2 (movitz-sxhash movitz-key)) hash-size)
		 then (rem (+ 2 pos) hash-size)
		 until (eq undef (svref bucket-data pos))
;;;	       do (warn "Hash collision at ~D of ~D: ~S ~S!"
;;;			pos hash-size movitz-key (elt bucket-data pos))
;;;	       finally (warn "Hash: pos ~D: ~S ~S" pos movitz-key movitz-value)
;;;	       finally (when (equal "NIL" key)
;;;			 (warn "key: ~S, value: ~S pos: ~S" movitz-key movitz-value pos))
		 finally
		   (setf (svref bucket-data pos) movitz-key
			 (svref bucket-data (1+ pos)) movitz-value)))
      (setf (first (movitz-struct-slot-values movitz-hash)) hash-test
	    (second (movitz-struct-slot-values movitz-hash)) (movitz-read bucket-data)
	    (third (movitz-struct-slot-values movitz-hash)) hash-sxhash
	    (fourth (movitz-struct-slot-values movitz-hash)) hash-count)
      movitz-hash)))
					     
;;;

;;;(unless (typep *movitz-nil* 'movitz-nil)
;;;  (warn "Creating new *MOVITZ-NIL* object!")
;;;  (setf *movitz-nil* (make-movitz-nil)))


(define-binary-class gate-descriptor ()
  ((offset-low
    :binary-type u16
    :initarg offset-low)
   (selector
    :binary-type u16
    :initarg selector)
   (count
    :binary-type u8
    :initarg count)
   (access
    :initarg access
    :binary-type (define-bitfield gate-descriptor-access (u8)
		   (((:numeric privilege-level 2 5))
		    ((:enum :byte (5 0)) :task         #x5
					 :interrupt    #xe
					 :interrupt-16 #x6
					 :trap         #xf
					 :trap-16      #x7)
		    ((:bits) segment-present 7))))
   (offset-high
    :binary-type u16
    :initarg offset-high)))

(defun make-gate-descriptor (type offset &key (segment-selector 0) (privilege 0) (count 0))
  (check-type offset (unsigned-byte 32))
  (check-type count (integer 0 31))
  (check-type privilege (integer 0 3))
  (make-instance 'gate-descriptor
    'offset-low (ldb (byte 16 0) offset)
    'offset-high (ldb (byte 16 16) offset)
    'selector segment-selector
    'count (ldb (byte 5 0) count)
    'access (list `(privilege-level . ,privilege)
		  type
		  'segment-present)))

(defun map-interrupt-trampolines-to-idt (trampolines type)
  (check-type trampolines vector)
  (assert (eq type 'word))
  (let* ((byte-list
	  (with-binary-output-to-list (bytes)
	    (loop for trampoline across trampolines
		as exception-vector upfrom 0
		do (let* ((trampoline-address (movitz-intern (find-primitive-function trampoline)))
			  (symtab (movitz-env-get trampoline :symtab))
			  (trampoline-offset (cdr (assoc exception-vector symtab))))
		     (assert symtab ()
		       "No symtab for exception trampoline ~S." trampoline)
		     (write-binary-record
		      (make-gate-descriptor ':interrupt
					    (+ (slot-offset 'movitz-basic-vector 'data)
					       trampoline-address
					       trampoline-offset)
					    :segment-selector (* 3 8))
		      bytes))))))
    (let ((l32 (merge-bytes byte-list 8 32)))
      (movitz-intern (make-movitz-vector (length l32)
					 :element-type '(unsigned-byte 32)
					 :initial-contents l32)))))


;;; std-instance

(define-binary-class movitz-std-instance (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :initform :std-instance)
   (pad :binary-lisp-type 3)
   (dummy
    :binary-type word
    :initform nil
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word)
   (class
    :binary-type word
    :map-binary-write 'movitz-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :class
    :accessor movitz-std-instance-class)
   (slots
    :binary-type word
    :map-binary-write 'movitz-read-and-intern
    :map-binary-read-delayed 'movitz-word
    :initarg :slots
    :accessor movitz-std-instance-slots))
  (:slot-align type #.+other-type-offset+))

;; (defmethod movitz-object-offset ((obj movitz-std-instance)) (- #x1e))

(defun make-movitz-std-instance (class slots)
  (make-instance 'movitz-std-instance
    :class (movitz-read class)
    :slots slots))

(defmethod print-object ((object movitz-std-instance) stream)
  (print-unreadable-object (object stream :identity t)
    (format stream "movitz-obj")
    (when (not (boundp '*movitz-obj-no-recurse*))
      (let ((*print-level* nil)
	    (*movitz-obj-no-recurse* t))
	(declare (special *movitz-obj-no-recurse*))
	(write-char #\space stream)
	(write (aref (movitz-print (slot-value object 'slots)) 0)
	       :stream stream))))
  object)

(defmethod update-movitz-object ((object movitz-std-instance) lisp-object)
  object)

;;;;

(define-binary-class movitz-bignum (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :initform :bignum)
   (sign
    :binary-type u8
    :initarg :sign
    :accessor movitz-bignum-sign)
   (length
    :binary-type lu16
    :initarg :length
    :accessor movitz-bignum-length
    :map-binary-write (lambda (x &optional type)
			(declare (ignore type))
			(check-type x (unsigned-byte 14))
			(* x 4))
    :map-binary-read (lambda (x &optional type)
		       (declare (ignore type))
		       (assert (zerop (mod x 4)))
		       (truncate x 4)))
   (bigit0 :binary-type :label)
   (value
    :initarg :value
    :accessor movitz-bignum-value))
  (:slot-align type #.+other-type-offset+))

(defmethod write-binary-record ((obj movitz-bignum) stream)
  (let* ((num (movitz-bignum-value obj))
	 (length (ceiling (integer-length (abs num)) 32)))
    (check-type length (unsigned-byte 16))
    (setf (movitz-bignum-length obj) length
	  (movitz-bignum-sign obj) (if (minusp num) #xff #x00))
    (+ (call-next-method)		; header
       (loop for b from 0 below length
	   summing (write-binary 'lu32 stream (ldb (byte 32 (* b 32)) (abs num)))))))

(defun make-movitz-integer (value)
  (if (<= +movitz-most-negative-fixnum+ value +movitz-most-positive-fixnum+)
      (make-movitz-fixnum value)
    (make-instance 'movitz-bignum
      :value value)))

(defmethod sizeof ((obj movitz-bignum))
  (+ (sizeof 'movitz-bignum)
     (* 4 (ceiling (integer-length (abs (movitz-bignum-value obj))) 32))))

(defmethod update-movitz-object ((object movitz-bignum) lisp-object)
  (assert (= (movitz-bignum-value object) lisp-object))
  object)


(defmethod read-binary-record ((type-name (eql 'movitz-bignum)) stream &key)
  (let* ((header (call-next-method))
	 (x (loop for i from 0 below (movitz-bignum-length header)
		summing (ash (read-binary 'u32 stream) (* i 32)))))
    (setf (movitz-bignum-value header)
      (ecase (movitz-bignum-sign header)
	(#x00 x)
	(#xff (- x))))
    header))

(define-binary-class movitz-ratio (movitz-heap-object-other)
  ((type
    :binary-type other-type-byte
    :initform :ratio)
   (dummy0
    :binary-type u8
    :initform 0)
   (dummy1
    :binary-type lu16
    :initform 0)
   (dummy2
    :binary-type word
    :initform 0)
   (numerator
    :binary-type word
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-read-and-intern)
   (denominator
    :binary-type word
    :map-binary-read-delayed 'movitz-word
    :map-binary-write 'movitz-read-and-intern)
   (value
    :reader movitz-ratio-value
    :initarg :value))
  (:slot-align type #.+other-type-offset+))

(defmethod write-binary-record ((obj movitz-ratio) stream)
  (declare (ignore stream))
  (let ((value (movitz-ratio-value obj)))
    (check-type value ratio)
    (setf (slot-value obj 'numerator) (numerator value)
	  (slot-value obj 'denominator) (denominator value))
    (call-next-method)))


(defmethod update-movitz-object ((object movitz-ratio) lisp-object)
  (assert (= (movitz-ratio-value object) lisp-object))
  object)

(defmethod update-movitz-object ((object movitz-ratio) (lisp-object float))
  (assert (= (movitz-ratio-value object) (rationalize lisp-object)))
  object)

(defmethod print-object ((x movitz-ratio) stream)
  (print-unreadable-object (x stream :type t)
    (format stream "~D" (slot-value x 'value)))
  x)

