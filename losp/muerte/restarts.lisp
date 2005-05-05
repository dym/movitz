;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      restarts.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Oct 28 09:27:13 2003
;;;;                
;;;; $Id: restarts.lisp,v 1.6 2005/05/05 20:51:51 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/restarts)

(in-package muerte)

(defmacro restart-bind (restart-specs &body body)
  (if (null restart-specs)
      `(progn ,@body)
    (let ((restart-spec (car restart-specs))
	  (rest-specs (cdr restart-specs)))
      (destructuring-bind (name function &key interactive-function
					      report-function
					      test-function)
	  restart-spec
	`(with-basic-restart (,name ,function ,interactive-function
				    ,test-function ,report-function)
	   (restart-bind ,rest-specs ,@body))))))

(defun dynamic-context->basic-restart (context)
  (assert (< (%run-time-context-slot nil 'stack-bottom)
	     context
	     (%run-time-context-slot nil 'stack-top)))
  (assert (eq (load-global-constant restart-tag)
	      (stack-frame-ref nil context 1 :lisp)))
  (let ((x (- (%run-time-context-slot nil 'stack-top) context)))
    (assert (below x #x1000000))
    (with-inline-assembly (:returns :eax)
      (:compile-form (:result-mode :eax) x)
      (:shll 6 :eax)
      (:movb #.(movitz::tag :basic-restart) :al))))

(defun basic-restart->dynamic-context (basic-restart)
  (check-type basic-restart basic-restart)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) basic-restart)
    (:movb 0 :al)
    (:locally (:movl (:edi (:edi-offset stack-top)) :ecx))
    (:shrl 6 :eax)
    (:negl :eax)
    (:leal (:eax :ecx) :eax)))

(define-simple-typep (basic-restart basic-restart-p) (x)
  (with-inline-assembly (:returns :boolean-zf=1)
    (:compile-form (:result-mode :eax) x)
    (:cmpb #.(movitz::tag :basic-restart) :al)
    (:jne 'fail)
    (:shrl 6 :eax)
    (:locally (:movl (:edi (:edi-offset stack-top)) :ecx))
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ebx))
;;    (:shll 2 :ebx)
    (:subl :ebx :ecx)
    (:cmpl :eax :ecx)
    (:jna 'fail)
    (:globally (:movl (:edi (:edi-offset restart-tag)) :ebx))
    (:negl :eax)
    (:locally (:movl (:edi (:edi-offset stack-top)) :ecx))
    (:cmpl :ebx (:eax :ecx 4))
   fail))

(defun restart-name (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -1 :lisp))))

(defun restart-function (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -2 :lisp))))

(defun restart-interactive-function (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -3 :lisp))))

(defun restart-test (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -4 :lisp))))

(defun restart-format-control (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -5 :lisp))))

(defun restart-args (restart)
  (etypecase restart
    (basic-restart
     (stack-frame-ref nil (basic-restart->dynamic-context restart)
		      -6 :lisp))))

(defun invoke-restart (restart-designator &rest arguments)
  (declare (dynamic-extent arguments))
  (let ((restart (find-restart restart-designator)))
    (typecase restart
      (basic-restart
       (let ((function (restart-function restart)))
	 (etypecase function
	   (function
	    (apply function arguments))
	   (symbol
	    (exact-throw (basic-restart->dynamic-context restart)
			 (ecase function
			   ((with-simple-restart)
			    (values nil t))))))))
      (t (error 'control-error
		:format-control "Can't invoke invalid restart ~S."
		:format-arguments (list restart-designator))))))

(defun invoke-restart-interactively (restart-designator)
  (let ((restart (find-restart restart-designator)))
    (typecase restart
      (basic-restart
       (let ((interactive-function (restart-interactive-function restart)))
	 (etypecase interactive-function
	   (function
	    (apply 'invoke-restart restart (funcall interactive-function)))
	   (null
	    (invoke-restart restart)))))
      (t (error 'control-error
		:format-control "Can't interactively invoke invalid restart ~S."
		:format-arguments (list restart-designator))))))

(defun find-restart-from-context (specifier context &optional condition)
  (declare (ignore condition))
  (etypecase specifier
    (basic-restart
     specifier)
    (symbol
     (with-each-dynamic-context (context)
       ((:basic-restart context name)
	(when (eq name specifier)
	  (return (dynamic-context->basic-restart context))))))))

(defun find-restart (specifier &optional condition)
  (find-restart-from-context specifier (current-dynamic-context) condition))

(defun find-restart-by-index (index &optional (context (current-dynamic-context)))
  (let ((counter 0))
    (with-each-dynamic-context (context)
      ((:basic-restart context)
       (when (= counter index)
	 (return (dynamic-context->basic-restart context)))
       (incf counter)))))

(defun compute-restarts (&optional condition)
  (declare (ignore condition))
  (let (computed-restarts)
    (with-each-dynamic-context ()
      ((:basic-restart context name)
       (declare (ignore name))
       (push (dynamic-context->basic-restart context)
	     computed-restarts)))
    (nreverse computed-restarts)))

(defun map-active-restarts (&optional function (context (current-dynamic-context)))
  "Map function over each active restart, ordered by the innermost one first.
   The function is called with two arguments: the restart and the index.
   Returns the number of restarts."
  (let ((index 0))
    (with-each-dynamic-context (context)
      ((:basic-restart context)
       (when function
	 (funcall function (dynamic-context->basic-restart context) index))
       (incf index)))
    index))

(defmethod print-object ((restart restart) stream)
  (cond
   (*print-escape*
    (print-unreadable-object (restart stream :type nil :identity t)
      (format stream "Restart ~W" (restart-name restart))))
   ((not *print-escape*)
    (etypecase restart
      (basic-restart
       (if (not (restart-format-control restart))
	   (write (restart-name restart) :stream stream)
	 (apply 'format stream
		(restart-format-control restart)
		(restart-args restart)))))))
  restart)

;;;;

(defun abort (&optional condition)
  (let ((r (find-restart 'abort condition)))
    (when r (invoke-restart r))
    (formatted-error 'control-error "Abort failed.")))

(defun continue ()
  (let ((r (find-restart 'continue)))
    (when r
      (invoke-restart r))))
			 
(defun muffle-warning (&optional condition)
  (let ((r (find-restart 'muffle-warning condition)))
    (when r (invoke-restart r))
    (formatted-error 'control-error "Muffle-warning failed.")))

