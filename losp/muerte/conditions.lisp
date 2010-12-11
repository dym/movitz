;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      conditions.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov 20 15:47:04 2002
;;;;                
;;;; $Id: conditions.lisp,v 1.29 2009-07-19 18:54:32 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/conditions)

(in-package muerte)

(defparameter *break-on-signals* nil)

(defparameter *debugger-function* nil)
(defvar *debugger-dynamic-context* nil)
(defparameter *debugger-invoked-stack-frame* nil)
(defvar *debugger-condition*)

(defmacro define-condition (name parent-types slot-specs &rest options)
  `(progn
     (defclass ,name ,(or parent-types '(condition)) ,slot-specs (:metaclass read-only-class))
     ,@(let ((reporter (cadr (assoc :report options))))
	 (when reporter
	   `((defmethod print-object ((condition ,name) stream)
	       (if *print-escape*
		   (call-next-method)
		 (funcall (function ,reporter) condition stream))
	       condition))))
     ',name))

(define-condition condition (standard-object)
  ((format-control
    :initarg :format-control
    :initform nil
    :reader condition-format-control)
   (format-arguments
    :initarg :format-arguments
    :initform nil
    :reader condition-format-arguments))
  (:report (lambda (condition stream)
	     (if (or *print-escape*
		     (not (condition-format-control condition)))
		 (call-next-method)
	       (apply #'format stream
		      (condition-format-control condition)
		      (condition-format-arguments condition))))))

(define-condition simple-condition (condition)
  ((format-control
    :reader simple-condition-format-control)
   (format-arguments
    :reader simple-condition-format-arguments)))
(define-condition serious-condition () ())
(define-condition error (serious-condition) ())
(define-condition storage-condition (serious-condition) ())
(define-condition warning () ())
(define-condition style-warning () ())
(define-condition simple-error (simple-condition error) ())
(define-condition simple-warning (simple-condition warning) ())
(define-condition parse-error (error) ())

(define-condition cell-error (error)
  ((name
    :initarg :name
    :reader cell-error-name))
  (:report (lambda (c s)
	     (format s "Error accessing cell ~S."
		     (cell-error-name c)))))

(define-condition undefined-function (cell-error)
  ()
  (:report (lambda (c s)
	     (format s "Undefined function ~S."
		     (cell-error-name c)))))

(define-condition undefined-function-call (undefined-function)
  ((arguments
    :initarg :arguments
    :reader undefined-function-call-arguments))
  (:report (lambda (c s)
	     (format s "Undefined function ~S called with arguments ~:S."
		     (cell-error-name c)
		     (undefined-function-call-arguments c)))))
		  
(define-condition unbound-variable (cell-error)
  ()
  (:report (lambda (c s)
	     (format s "Unbound variable ~S."
		     (cell-error-name c)))))

(define-condition unbound-slot (cell-error)
  ((instance
    :initarg :instance
    :reader unbound-slot-instance))
  (:report (lambda (c s)
             (format s "The slot ~S is unbound in the object ~S."
                     (cell-error-name c)
                     (unbound-slot-instance c)))))


(define-condition print-not-readable (error)
  ((object
    :initarg :object
    :reader print-not-readable-object))
  (:report (lambda (c s)
             (format s "Cannot print ~S readably."
                     (print-not-readable-object c)))))

(define-condition program-error (error) ())

(defun simple-program-error (format-control &rest format-arguments)
  (error 'program-error
	 :format-control format-control
	 :format-argumetns format-arguments))

(define-condition type-error (error)
  ((expected-type
    :initarg :expected-type
    :reader type-error-expected-type)
   (datum
    :initarg :datum
    :reader type-error-datum))
  (:report (lambda (c s)
	     (format s "The object ~Z `~S' is not of type ~S."
		     (type-error-datum c)
		     (type-error-datum c)
		     (type-error-expected-type c)))))

(define-condition simple-type-error (simple-condition type-error) ())

(define-condition etypecase-error (type-error)
  ()
  (:report (lambda (c s)
	     (format s "The object '~S' fell through an etypecase where the legal types were ~S."
		     (type-error-datum c)
		     (type-error-expected-type c)))))

(defun etypecase-error (datum expecteds)
  (error 'etypecase-error
	 :datum datum
	 :expected-type (cons 'or expecteds)))

(define-condition ecase-error (type-error)
  ()
  (:report (lambda (c s)
	     (format s "The object '~S' fell through an ecase where the legal cases were ~S."
		     (type-error-datum c)
		     (type-error-expected-type c)))))

(defun ecase-error (datum expecteds)
  (error 'ecase-error
	 :datum datum
	 :expected-type (cons 'member expecteds)))

(define-condition control-error (error) ())

(define-condition throw-error (control-error)
  ((tag
    :initarg :tag
    :reader throw-error-tag))
  (:report (lambda (c s)
	     (format s "Cannot throw to tag `~S'." (throw-error-tag c)))))

(define-condition wrong-argument-count (program-error)
  ((function
    :initarg :function
    :reader condition-function)
   (argument-count
    :initarg :argument-count
    :reader condition-argument-count))
  (:report (lambda (c s)
	     (format s "Function ~S ~:A received ~:[an incorrect number of~;~:*~D~] arguments."
		     (funobj-name (condition-function c))
		     (funobj-lambda-list (condition-function c))
		     (condition-argument-count c)))))

(define-condition index-out-of-range (error)
  ((index
    :initarg :index
    :reader condition-index)
   (range
    :initarg :range
    :reader condition-range))
  (:report (lambda (c s)
	     (format s "Index ~D is beyond range 0-~D."
		     (condition-index c)
		     (condition-range c)))))

(define-condition stream-error (error)
  ((stream
    :initarg :stream
    :reader stream-error-stream)))

(define-condition reader-error (parse-error stream-error) ())

(define-condition end-of-file (stream-error)
  ()
  (:report (lambda (c s)
	     (format s "End of file encountered on ~W."
		     (stream-error-stream c)))))

(define-condition arithmetic-error (error)
  ((operation
    :initarg :operation
    :initform nil
    :reader arithmetic-error-operation)
   (operands
    :initarg :operands
    :initform nil
    :reader arithmetic-error-operands)))

(define-condition division-by-zero (arithmetic-error)
  ()
  (:report (lambda (c s)
	     (declare (ignore c))
	     (format s "Division by zero."))))

(define-condition package-error (error)
  ((package
    :initarg :package
    :initform nil
    :reader package-error-package)))

(define-condition file-error (error)
  ((pathname
    :initarg :pathname
    :initform nil
    :reader file-error-pathname)))

(defun make-condition (type &rest slot-initializations)
  (declare (dynamic-extent slot-initializations))
  (apply 'make-instance type slot-initializations))


(defun warn (datum &rest arguments)
  (declare (dynamic-extent arguments))
  (cond
   ((not (eq t (get 'clos-bootstrap 'have-bootstrapped)))
    (fresh-line)
    (write-string "Warning: ")
    (apply 'format t datum arguments)
    (fresh-line))
   (t (with-simple-restart (muffle-warning "Muffle warning.")
	(let ((c (signal-simple 'simple-warning datum arguments))
	      (*standard-output* *error-output*))
	  (typecase datum
	    (string
	     (fresh-line)
	     (write-string "Warning: ")
	     (apply 'format t datum arguments)
	     (terpri))
	    (t (format t "~&Warning: ~A"
		       (or c (coerce-to-condition 'simple-warning datum arguments)))))))))
  nil)

(defun coerce-to-condition (default-type datum args)
  ;; (declare (dynamic-extent args))
  (etypecase datum
    (condition
     datum)
    (symbol
     (apply 'make-condition datum args))
    (string
     (make-condition default-type
       :format-control datum
       :format-arguments (copy-list args)))))

(defun signal-simple (default-type datum args)
  "Signal the condition denoted by a condition designator.
Will only make-instance a condition when it is required.
Return the condition object, if there was one."
  (let* ((class (etypecase datum
		  (symbol
		   (or (find-class datum nil)
		       (error "No condition class named ~S." datum)))
		  (string
		   (find-class default-type))
		  (condition
		   (class-of datum))))
	 (cpl (class-precedence-list class))
	 (condition nil)
	 (bos-type *break-on-signals*))
    (with-simple-restart (continue "Ignore *break-on-signals*.")
      (let ((*break-on-signals* nil)) ; avoid recursive error if *b-o-s* is faulty.
	(when (typecase bos-type
		(null nil)
		(symbol
		 (let ((bos-class (find-class bos-type nil)))
		   (if (not bos-class)
		       (typep (class-prototype-value class) bos-type)
                       (member bos-class cpl))))
		(list
		 (typep (class-prototype-value class) bos-type))
		(t (member bos-type cpl)))
	  (break "Signalling ~S" datum))))
    (macrolet ((invoke-handler (handler)
		 `(funcall ,handler
			   (or condition
			       (setf condition
                                     (coerce-to-condition default-type datum args))))))
      (let ((*active-condition-handlers* *active-condition-handlers*))
	(do () ((null *active-condition-handlers*))
	  (let ((handlers (pop *active-condition-handlers*)))
	    (dolist (handler handlers)
	      (let ((handler-type (car handler)))
		(typecase handler-type
		  (symbol
		   (let ((handler-class (find-class handler-type nil)))
		     (when (if (not handler-class)
			       (typep (class-prototype-value class) handler-type)
                               (progn
                                 (setf (car handler) handler-class) ; XXX memoize this find-class..
                                 (member handler-class cpl)))
		       (invoke-handler (cdr handler)))))
		  (cons
		   (when (typep (class-prototype-value class) handler-type)
		     (invoke-handler (cdr handler))))
		  (null)
		  (t (when (member handler-type cpl)
		       (invoke-handler (cdr handler)))))))))))
    (or condition
	(when (typep datum condition)
	  datum))))

(defun signal (datum &rest args)
  (declare (dynamic-extent args))
  (signal-simple 'simple-condition datum args)
  nil)

(defun invoke-debugger (condition)
  (when *debugger-hook*
    (let ((hook *debugger-hook*)
	  (*debugger-hook* nil))
      (funcall hook condition hook)))
  #+ignore
  (unless *debugger-function*
    (setf *debugger-function* #'muerte.init::my-debugger))
  (cond
   ((not *debugger-function*)
    (let ((*never-use-print-object* t))
      (backtrace :spartan t :conflate nil))
    (format t "~&No debugger in *debugger-function*...")
    (dotimes (i 100000)
      (write-string ""))
    (format t "Trying to continue or abort.")
    (invoke-restart (or (find-restart 'continue)
			(find-restart 'abort)
			(format t "~%Condition for debugger: ~Z" condition)
			(format t "~%No abort restart is active. Halting CPU.")
			(halt-cpu))))
   (t (let ((*debugger-invoked-stack-frame* (stack-frame-uplink nil (current-stack-frame))))
	(funcall *debugger-function* condition))))
  (format *debug-io* "~&Debugger ~@[on ~S ]returned!~%Trying to abort...~%" condition)
  (let ((r (find-restart 'abort)))
    (when r
      (invoke-restart r))
    (format *debug-io* "~&Aborting failed. Halting CPU.")
    (halt-cpu)))

(defun invoke-debugger-on-designator (&rest designator)
  (declare (dynamic-extent designator))
  (if (or (eq 'break (car designator))
	  (and *error-no-condition-for-debugger*
	       (symbolp (car designator)))
	  ;; don't let an error trigger CLOS bootstrapping.
	  (not (eq t (get 'clos-bootstrap 'have-bootstrapped))))
      (invoke-debugger designator)
    (invoke-debugger (coerce-to-condition (car designator)
					  (cadr designator)
					  (cddr designator)))))

(defun break (&optional format-control &rest format-arguments)
  (declare (dynamic-extent format-arguments))
  (with-simple-restart (continue "Return from break~:[.~;~:*: ~?~]" format-control format-arguments)
    ;; (format *debug-io* "~&Break: ~?" format-control format-arguments)
    (let ((*debugger-hook* nil))
      (apply 'invoke-debugger-on-designator
	     'break
	     (or format-control "Break was invoked.")
	     format-arguments)))
  nil)

(define-condition newline () ())

(define-condition floating-point-inexact (arithmetic-error) ())
(define-condition floating-point-invalid-operation (arithmetic-error) ())
(define-condition floating-point-overflow (arithmetic-error) ())
(define-condition floating-point-underflow (arithmetic-error) ())
