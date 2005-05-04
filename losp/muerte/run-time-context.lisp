;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromsoe, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      run-time-context.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov 12 18:33:02 2003
;;;;                
;;;; $Id: run-time-context.lisp,v 1.20 2005/05/04 07:43:27 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)
(provide :muerte/run-time-context)

(in-package muerte)

;;;;

(defclass run-time-context-class (std-slotted-class built-in-class) ())

(defclass run-time-context (t)
  ((name
    :initarg :name
    :initform :anonymous
    :accessor run-time-context-name)
   (stack-vector
    :initarg :stack-vector))
  (:metaclass run-time-context-class)
  (:size #.(bt:sizeof 'movitz::movitz-run-time-context))
  (:slot-map #.(movitz::slot-map 'movitz::movitz-run-time-context
			       (cl:+ (bt:slot-offset 'movitz::movitz-run-time-context
						     'movitz::run-time-context-start)
				     0))))

(defmethod slot-value-using-class ((class run-time-context-class) object
				   (slot standard-effective-slot-definition))
  (with-unbound-protect (svref (%run-time-context-slot 'slots object)
			       (slot-definition-location slot))
    (slot-unbound class object (slot-definition-name slot))))

(defmethod (setf slot-value-using-class) (new-value (class run-time-context-class) object
					  (slot standard-effective-slot-definition))
  (let ((location (slot-definition-location slot))
	(slots (%run-time-context-slot 'slots object)))
    (setf (svref slots location) new-value)))

(defmethod slot-boundp-using-class ((class run-time-context-class) object
				    (slot standard-effective-slot-definition))
  (not (eq (load-global-constant new-unbound-value)
	   (svref (%run-time-context-slot 'slots object)
		  (slot-definition-location slot)))))

(defmethod allocate-instance ((class run-time-context-class) &rest initargs)
  (declare (dynamic-extent initargs) (ignore initargs))
  (let ((x (clone-run-time-context)))
    (setf (%run-time-context-slot 'class x) class)
    (setf (%run-time-context-slot 'slots x)
      (allocate-slot-storage (count-if 'instance-slot-p (class-slots class))
			     (load-global-constant new-unbound-value)))
    x))

(defmethod initialize-instance ((instance run-time-context) &rest initargs)
  (declare (dynamic-extent initargs))
  (apply 'shared-initialize instance t initargs))

(defmethod shared-initialize ((instance run-time-context) slot-names &rest all-keys)
  (declare (dynamic-extent all-keys))
  (dolist (slot (class-slots (class-of instance)))
    (let ((slot-name (slot-definition-name slot)))
      (multiple-value-bind (init-key init-value foundp)
	  (get-properties all-keys (slot-definition-initargs slot))
	(declare (ignore init-key))
	(if foundp
	    (setf (slot-value instance slot-name) init-value)
	  (when (and (not (slot-boundp instance slot-name))
		     (not (null (slot-definition-initfunction slot)))
		     (or (eq slot-names t)
			 (member slot-name slot-names)))
	    (let ((initfunction (slot-definition-initfunction slot)))
	      (setf (slot-value instance slot-name)
		(etypecase initfunction
		  (cons (cadr initfunction)) ; '(quote <obj>)
		  (function (funcall initfunction))))))))))
  instance)

(defmethod compute-effective-slot-reader ((class run-time-context-class) slot)
  (let ((slot-location (slot-definition-location slot)))
    (check-type slot-location positive-fixnum)
    (lambda (instance)
      (with-unbound-protect (svref (%run-time-context-slot 'slots instance) slot-location)
	(slot-unbound-trampoline instance slot-location)))))

(defmethod compute-effective-slot-writer ((class run-time-context-class) slot)
  (let ((slot-location (slot-definition-location slot)))
    (check-type slot-location positive-fixnum)
    (lambda (value instance)
      (setf (svref (%run-time-context-slot 'slots instance) slot-location)
	value))))

(defmethod print-object ((x run-time-context) stream)
  (print-unreadable-object (x stream :type t :identity t)
    (format stream "~S" (run-time-context-name x)))
  x)

;;;

(defun current-run-time-context ()
  (current-run-time-context))

(defun find-run-time-context-slot (context slot-name &optional (errorp t))
  (or (assoc slot-name (slot-value (class-of context) 'slot-map))
      (when errorp
	(error "No run-time-context slot named ~S in ~S." slot-name context))))

(defun %run-time-context-slot (slot-name &optional (context (current-run-time-context)))
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (word
       (memref context -6 :index (third slot)))
      (code-vector-word
       (memref context -6 :index (third slot) :type :code-vector))
      (lu32
       (memref context -6 :index (third slot) :type :unsigned-byte32)))))

(defun (setf %run-time-context-slot) (value slot-name &optional (context (current-run-time-context)))
  (check-type context run-time-context)
  (let ((slot (find-run-time-context-slot context slot-name)))
    (ecase (second slot)
      (word
       (setf (memref context -6 :index (third slot)) value))
      (lu32
       (setf (memref context -6 :index (third slot) :type :unsigned-byte32) value))
      (code-vector-word
       (setf (memref context -6 :index (third slot) :type :code-vector) value)))))

(defun clone-run-time-context (&key (parent (current-run-time-context))
				    (name :anonymous))
  (check-type parent run-time-context)
  (let ((context (%shallow-copy-object parent (movitz-type-word-size 'movitz-run-time-context))))
    (setf (%run-time-context-slot 'slots context) (copy-seq (%run-time-context-slot 'slots parent))
	  (%run-time-context-slot 'self context) context
	  (%run-time-context-slot 'atomically-continuation context) 0)
    context))

(defun %run-time-context-install-stack (context
					&optional (control-stack
						   (make-array 8192 :element-type '(unsigned-byte 32)))
						  (cushion 1024))
  (check-type control-stack vector)
  (assert (< cushion (array-dimension control-stack 0)))
  (setf (%run-time-context-slot 'control-stack context) control-stack)
  (setf (%run-time-context-slot 'stack-top context)
    (+ (object-location control-stack) 8
       (* 4 (array-dimension control-stack 0))))
  (setf (%run-time-context-slot 'stack-bottom context)
    (+ (object-location control-stack) 8
       (* 4 cushion)))
  control-stack)

