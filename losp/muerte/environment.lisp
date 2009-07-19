;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      environment.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Oct 20 00:41:57 2001
;;;;                
;;;; $Id: environment.lisp,v 1.19 2009-07-19 18:57:48 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/environment)

(in-package muerte)

(defun pprint-clumps (stream clumps &optional colon at)
  "A clump is the quantity of 8 bytes."
  (declare (ignore colon at))
  (cond
   ((< clumps 64)
    (format stream "~D bytes" (* clumps 8)))
   ((< clumps #x20000)
    (format stream "~D.~D KB"
	    (truncate clumps 128)
	    (truncate (* 10 (rem clumps 128)) 128)))
   (t (format stream "~D.~D MB"
	      (truncate clumps (* 128 1024))
	      (truncate (* 10 (rem clumps #x20000)) #x20000)))))

(defun room (&optional x)
  (declare (ignore x))
  (let ((clumps (malloc-cons-pointer)))
    (format t "Heap used: ~D clumps = ~/muerte:pprint-clumps/." clumps clumps))
  (values))

(defparameter *trace-level* 0)
(defparameter *trace-escape* nil)
(defvar *trace-map* nil)

(defun function-name-symbol (function-name)
  (etypecase function-name
    (symbol
     function-name)
    ((cons (eql setf) (cons symbol null))
     (gethash (cadr function-name) *setf-namespace*))))

(defun match-caller (name)
  (do ((frame (stack-frame-uplink nil (current-stack-frame))
	      (stack-frame-uplink nil frame)))
      ((not (plusp frame)))
    (let ((f (stack-frame-funobj nil frame)))
      (cond
       ((not (typep f 'function))
	(return nil))
       ((equal name (funobj-name f))
	(return t))
       ((and (consp (funobj-name f)) (eq 'method (car (funobj-name f)))
	     (equal name (second (funobj-name f))))
	(return t))
       ((equal name 'eval)
	(return nil))))))

(defun do-trace (function-name &key (callers t))
  (when (assoc function-name *trace-map* :test #'equal)
    (do-untrace function-name))
  (let ((function-symbol (function-name-symbol function-name)))
    (assert (fboundp function-symbol) (function-name)
      "Can't trace undefined function ~S." function-name)
    (let* ((real-function (symbol-function function-symbol))
	   (wrapper (lambda (&rest args)
		      (declare (dynamic-extent args))
		      (if *trace-escape*
			  (apply real-function args)
			(let ((*trace-escape* t))
			  (cond
			   ((and (not (eq t callers))
				 (notany 'match-caller callers))
			    (apply real-function args))
			   (t (let ((*trace-escape* t))
				(fresh-line *trace-output*)
				(dotimes (i *trace-level*)
				  (write-string "  " *trace-output*))
				(format *trace-output* "~&~D: (~S~{ ~S~})~%"
					*trace-level* function-name args))
			      (multiple-value-call
				  (lambda (&rest results)
				    (declare (dynamic-extent results))
				    (let ((*trace-escape* t))
				      (fresh-line *trace-output*)
				      (dotimes (i (min *trace-level* 10))
					(write-string "  " *trace-output*))
				      (format *trace-output* "~&~D: =>~{ ~W~^,~}.~%"
					      *trace-level* results)
				      (values-list results)))
				(let ((*trace-level* (1+ *trace-level*))
				      (*trace-escape* nil))
				  (apply real-function args))))))))))
      (push (cons function-name
		  real-function)
	    *trace-map*)
      (setf (symbol-function function-symbol)
	wrapper)))
  (values))

(defmacro trace (&rest names)
  (if (null names)
      `(mapcar #'car *trace-map*)
      `(progn
	 ,@(mapcar (lambda (name)
		     `(do-trace ',name))
		   names)
	 (values))))

(defun do-untrace (name)
  (let ((map (assoc name *trace-map*)))
    (assert map () "~S is not traced." name)
    (let ((function-name-symbol (function-name-symbol name))
	  (function (cdr map)))
      (setf (symbol-function function-name-symbol)
	function)
      (setf *trace-map*
	(delete name *trace-map* :key 'car))))
  (values))

(defmacro untrace (&rest names)
  (if (null names)
      '(do () ((null muerte::*trace-map*))
	(do-untrace (caar muerte::*trace-map*)))
      `(progn
	 ,@(mapcar (lambda (name)
		     `(do-untrace ',name))
		   names)
	 (values))))

(defun time-skew-measure (mem x-lo x-hi)
  (declare (ignore mem))
  (multiple-value-bind (y-lo y-hi)
      (read-time-stamp-counter)
    (assert (<= x-hi y-hi))
    (- y-lo x-lo (if (< y-lo x-lo) most-negative-fixnum 0))))

(defun report-time (start-mem start-time-lo start-time-hi)
  (multiple-value-bind (end-time-lo end-time-hi)
      (read-time-stamp-counter)
    (let* ((skew (or (get 'report-time 'skew)
		     (setf (get 'report-time 'skew)
		       (loop repeat 10	; warm up caches.
			   as x = (multiple-value-bind (x-lo x-hi)
				      (read-time-stamp-counter)
				    (constantly-true 123)
				    (time-skew-measure start-mem x-lo x-hi))
			   finally (return x)))))
	   (clumps (and start-mem (- (malloc-cons-pointer) start-mem)))
	   (delta-time (+ (ash (- end-time-hi start-time-hi) 29)
			  (- end-time-lo start-time-lo skew))))
      (format t "~&;; CPU cycles: ~:D.~%~@[;; Space used: ~D clumps = ~/muerte:pprint-clumps/.~]~%"
	      delta-time clumps clumps))))

(defmacro time (form)
  `(let ((start-mem (malloc-cons-pointer)))
     (multiple-value-bind (start-time-lo start-time-hi)
	 (read-time-stamp-counter)
       (multiple-value-prog1
	   ,form
	 (report-time start-mem start-time-lo start-time-hi)))))

(defun describe (object &optional stream)
  (describe-object object (output-stream-designator stream))
  (values))
  
(defmethod describe-object (object stream)
  (format stream "Don't know how to describe ~S." object))

(defmethod describe-object ((object function) stream)
  (let ((arglist (funobj-lambda-list object)))
    (format stream "The function ~S takes arglist ~:A."
	    (funobj-name object)
	    arglist)))

(defun sleep (seconds)
  (declare (ignore seconds))
  (error "There is no default implementation of sleep."))

(defstruct random-state state)

(defvar *random-state* #s(random-state :state 0))

(defmethod documentation (x doc-type)
  nil)
