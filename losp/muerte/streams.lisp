;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      streams.lisp
;;;; Description:   Basic I/O streams code.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Jun 30 14:33:15 2003
;;;;                
;;;; $Id: streams.lisp,v 1.6 2008-04-21 19:42:57 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)
(provide :muerte/streams)

(in-package muerte)

(defgeneric stream-write-char (stream character)
  (:no-clos-fallback stream-no-clos))

(defmethod stream-write-char ((stream string) character)
  (vector-push-extend character stream)
  character)

(defmethod stream-write-char ((stream function) character)
  (funcall stream 'stream-write-char character))

(defgeneric stream-read-char (stream)
  (:no-clos-fallback stream-no-clos))

(defmethod stream-read-char ((stream function))
  (funcall stream 'stream-read-char))

(defun output-stream-designator (d)
  (cond
   ((eq nil d) *standard-output*)
   ((eq t d)   *terminal-io*)
   (t d)))

(defun input-stream-designator (d)
  (cond
   ((eq nil d) *standard-input*)
   ((eq t d) *terminal-io*)
   (t d)))

(defun install-streams-printing (&optional (new-stdout (make-instance 'muerte.x86-pc::vga-text-console)))
  ;; (check-type new-stdout stream)
  (let ((s new-stdout))
    (setf *standard-output* s
	  *debug-io* s
	  *terminal-io* s
	  *trace-output* s
	  *query-io* s))
  (values))

(defgeneric stream-write-string (stream string &optional start end)
  (:no-clos-fallback :unspecialized-method))

(defmethod stream-write-string (stream string &optional (start 0) (end (length string)))
  (with-subvector-accessor (string-ref string start end)
    (do ((i start (1+ i)))
	((>= i end))
      (stream-write-char stream (string-ref i))))
  string)

(defgeneric stream-write-escaped-string (stream string escaped-char &optional start end)
  (:no-clos-fallback :unspecialized-method))

(defmethod stream-write-escaped-string (stream string escaped-char
					&optional (start 0) (end (length string)))
  (stream-write-char stream escaped-char)
  (with-subvector-accessor (string-ref string start end)
    (do ((i start (1+ i)))
	((>= i end))
      (let ((c (string-ref i)))
	(when (or (eql c escaped-char) (char= c #\\))
	  (stream-write-char stream #\\))
	(stream-write-char stream c))))
  (stream-write-char stream escaped-char)
  string)

(defgeneric stream-fresh-line (stream)
  (:no-clos-fallback stream-no-clos))

(defmethod stream-fresh-line (stream)
  (stream-write-char stream #\Newline)
  t)

(defmethod stream-fresh-line ((stream function))
  (funcall stream 'stream-fresh-line))

(defun stream-no-clos (stream &rest args)
  (declare (dynamic-extent args))
  (etypecase stream
    (string
     (case (funobj-name *forward-generic-function*)
       (stream-write-char
	(vector-push-extend (car args) stream)
	(car args))
       (stream-fresh-line
	(vector-push-extend #\newline stream)
	t)))
    (function
     (apply stream (funobj-name *forward-generic-function*) args))))


;;;;


(defun read-char (&optional input-stream (eof-error-p t) eof-value recursive-p)
  " => char"
  (%read-char (input-stream-designator input-stream) eof-error-p eof-value recursive-p t))

(defun read-key (&optional input-stream (eof-error-p t) eof-value recursive-p)
  " => char, symbol, etc."
  (%read-key (input-stream-designator input-stream) eof-error-p eof-value recursive-p t))

(defun finish-output (&optional stream)
  "finish-output attempts to ensure that any buffered output sent to output-stream has reached its
destination, and then returns."
  (let ((stream (output-stream-designator stream)))
    (etypecase stream
      (function)			; NOP
      (simple-stream
       (%finish-output stream)))))

(defclass string-stream (stream) ())

(defun make-string-input-stream (string &optional (start 0) (end nil))
  )

(defun make-string-output-stream ())


(defclass broadcast-stream (stream)
  ((streams
    :reader concatenated-stream-streams
    :initarg :streams)))

(defclass concatenated-stream (stream)
  ((streams
    :reader concatenated-stream-streams
    :initarg :streams)))

(defclass echo-stream (stream)
  ((input-stream
    :reader echo-stream-input-stream
    :initarg :input-stream)
   (output-stream
    :reader echo-stream-output-stream
    :initarg :output-stream)))

(defclass file-stream (stream)
  ())

(defclass synonym-stream (stream)
  ((symbol
    :initarg :symbol
    :reader synonym-stream-symbol)))

(defclass two-way-stream (stream)
  ((input
    :initarg :input
    :reader two-way-stream-input-stream)
   (output
    :initarg :output
    :reader two-way-stream-output-stream)))


