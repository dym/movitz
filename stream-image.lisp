;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      stream-image.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Aug 27 14:46:50 2001
;;;;                
;;;; $Id: stream-image.lisp,v 1.7 2004/06/29 23:15:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(in-package movitz)


(defclass stream-image (image)
  ((stream
    :reader image-stream
    :initarg :stream)
   (offset
    :initarg :offset
    :accessor image-stream-offset)
   (start-address
    :initarg :start-address
    :initform #x100000
    :reader image-start-address)
   (nil-word
    :initarg :nil-word
    :initform (if (boundp '*image*)
		  (image-nil-word *image*)
		(progn
		  (format *query-io* "~&Please enter the stream-images NIL value: ")
		  (read *query-io*)))
    :reader image-nil-word)))

(defmethod image-register32 ((image stream-image) register-name)
  (declare (ignorable image) (ignore register-name))
  (error "A stream-image has no CPU state."))

(defmethod (setf image-stream-position) (value (image stream-image) &optional physicalp)
  (check-type value (integer 0 *))
  (assert (file-position (image-stream image)
			 (+ (image-stream-offset image)
			    (if physicalp 0 (image-ds-segment-base image))
			    value))
      (value)
    "Unable to set memory-stream's file-position to #x~X." value))

(defmethod image-constant-block ((image stream-image))
  (movitz-word (image-register32 image :edi)))

(defmethod movitz-word-by-image ((image stream-image) word)
  (let ((object (case (extract-tag word)
		  ((:even-fixnum :odd-fixnum)
		   (make-instance 'movitz-fixnum :value (ldb (byte 29 2) word)))
		  (:cons
		   (setf (image-stream-position image) (extract-pointer word))
		   (read-binary 'movitz-cons (image-stream image)))
		  (:character
		   (make-instance 'movitz-character :char (code-char (ldb (byte 8 8) word))))
		  (:null
		   #+ignore
		   (assert (= (- word (tag :null)) (image-constant-block-address image)) (word)
		     "The word #x~8,'0X has NIL tag but isn't NIL." word)
		   (setf (image-stream-position image) 0 #+ignore (- word (tag :null)))
		   (let ((object (read-binary 'movitz-constant-block (image-stream image))))
		     (setf (movitz-heap-object-word (movitz-constant-block-null-symbol object))
		       word)
		     object))
		  (:symbol
		   ;; (warn "loading new symbol at ~S" word)
		   (setf (image-stream-position image)
		     (- word (tag :symbol)))
		   (read-binary 'movitz-symbol (image-stream image)))
		  (:other
		   (setf (image-stream-position image)
		     (+ 0 (extract-pointer word)))
		   (let* ((type-code (read-binary 'u8 (image-stream image)))
			  (type-tag (enum-symbolic-value 'other-type-byte type-code)))
		     (setf (image-stream-position image)
		       (extract-pointer word))
		     (case type-tag
		       (:funobj
			(read-binary 'movitz-funobj (image-stream image)))
		       (:basic-vector
			(read-binary 'movitz-basic-vector (image-stream image)))
		       (:vector
			(read-binary 'movitz-vector (image-stream image)))
		       (:defstruct
			   (read-binary 'movitz-struct (image-stream image)))
		       (:std-instance
			(read-binary 'movitz-std-instance (image-stream image)))
		       (t (warn "unknown other object: #x~X: ~S code #x~X."
				word type-tag type-code)
			  (make-instance 'movitz-fixnum :value (truncate word 4))))))
		  (t (make-instance 'movitz-fixnum :value 0)))))
    (when (typep object 'movitz-heap-object)
      (setf (movitz-heap-object-word object) word))
    object))

(defmethod image-intern-object ((image stream-image) object &optional (size (sizeof object)))
  (declare (ignore size))
  (movitz-heap-object-word object))

(defmethod image-lisp-to-movitz-object ((image stream-image) lisp-object)
  (etypecase lisp-object
    (null
     (movitz-word-by-image image (image-nil-word image)))
    ((signed-byte 30)
     (make-movitz-fixnum lisp-object))))

(defmethod (setf image-lisp-to-movitz-object) (movitz-object (image stream-image) lisp-object)
  (declare (ignore lisp-object))
  movitz-object)



