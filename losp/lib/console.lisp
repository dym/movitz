;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      console.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Aug 14 18:14:16 2003
;;;;                
;;;; $Id: console.lisp,v 1.6 2004/11/24 16:23:11 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/console)

(in-package muerte.lib)

(defmacro with-saved-excursion ((stream) &body body)
  (let ((stream-var (gensym))
	(x-var (gensym))
	(y-var (gensym))
	(scroll-var (gensym)))
    `(let ((,stream-var ,stream))
       (let ((,x-var (cursor-x ,stream-var))
	     (,y-var (cursor-y ,stream-var))
	     (,scroll-var *scroll-offset*))
	 (unwind-protect (progn ,@body)
	   (setf (cursor-x ,stream-var) ,x-var
		 (cursor-y ,stream-var) (- ,y-var (- *scroll-offset* ,scroll-var))))))))


(defgeneric cursor-x (console)
  (:no-clos-fallback console-no-clos))

(defgeneric (setf cursor-x) (x console)
  (:no-clos-fallback console-no-clos))

(defgeneric cursor-y (console)
  (:no-clos-fallback console-no-clos))

(defgeneric (setf cursor-y) (y console)
  (:no-clos-fallback console-no-clos))

(defgeneric console-width (console)
  (:no-clos-fallback console-no-clos))

(defgeneric console-height (console)
  (:no-clos-fallback console-no-clos))

(defmethod cursor-x ((console function))
  (funcall console 'cursor-x))

(defmethod (setf cursor-x) (x (console function))
  (funcall console '(setf cursor-x) x))

(defmethod cursor-y ((console function))
  (funcall console 'cursor-y))

(defmethod (setf cursor-y) (y (console function))
  (funcall console '(setf cursor-y) y))

(defmethod console-height (console)
  (funcall console 'console-height))

(defmethod console-width (console)
  (funcall console 'console-width))

(defgeneric clear-line (console x y)
  (:no-clos-fallback console-no-clos))

(defmethod clear-line ((console function) x y)
  (funcall console 'clear-line x y))

(defgeneric scroll-down (console)
  (:no-clos-fallback console-no-clos))

(defmethod scroll-down ((console function))
  (funcall console 'scroll-down))

(defgeneric console-char (console x y))
(defgeneric (setf console-char) (character console x y))
(defgeneric put-string (console string x y &optional start end))

(defgeneric local-echo-p (console)
  (:no-clos-fallback console-no-clos))

(defmethod local-echo-p ((console function))
  (funcall console 'local-echo-p))

(defun console-no-clos (&rest args)
  (declare (dynamic-extent args))
  (let* ((op (funobj-name *forward-generic-function*)))
    (cond
     ((symbolp op)
      (apply (car args) op (cdr args)))
     ((and (listp op) (eq 'setf (car op)))
      (apply (cadr args) op (car args) (cddr args)))
     (t (error "op: ~S args: ~S" op args)))))

(defclass console ()
  ((width
    :initarg :width
    :reader console-width)
   (height
    :initarg :height
    :reader console-height)
   #+ignore ((cursor-x
	      :initarg :cursor-x
	      :accessor cursor-x)
	     (cursor-y
	      :initarg :cursor-y
	      :accessor cursor-y))))

(defmethod stream-fresh-line ((stream console))
  (if (zerop (cursor-x stream))
      nil
    (progn
      (stream-write-char stream #\newline)
      t)))

(defmethod stream-write-char ((stream console) character)
  (labels ((do-write (stream character)
	     (with-accessors ((cursor-x cursor-x)
			      (cursor-y cursor-y)
			      (width console-width)
			      (height console-height))
		 stream
	       (case character
		 (#\newline
		  (setf cursor-x 0)
		  (cond
		   ((= height (1+ cursor-y))
		    (scroll-down stream))
		   (t (incf cursor-y))))
		 (#\backspace
		  (if (/= 0 cursor-x)
		      (decf cursor-x)
		    (progn
		      (decf cursor-y)
		      (setf cursor-x (1- width)))))
		 (#\return
		   (setf cursor-x 0))
		 (#\tab
		  (do-write stream #\space)
		  (do () ((zerop (rem cursor-x 8)))
		    (do-write stream #\space)))
		 (t (when (>= cursor-x width)
		      (do-write stream #\newline))
		    (setf (console-char stream cursor-x cursor-y) character)
		    (incf cursor-x))))))
    (do-write stream character)
    character))

(defmethod stream-write-string ((stream console) string &optional (start 0) (end (length string)))
  (loop with w = (console-width stream)
      with x = (cursor-x stream) and y = (cursor-y stream)
      for i from start below end
      as char = (char string i)
      do (when (>= x w)
	   (setf (cursor-x stream) x)
	   (stream-write-char stream #\newline)
	   (setf x (cursor-x stream) y (cursor-y stream)))
	 (cond
	  ((graphic-char-p char)
	   (setf (console-char stream x y) char)
	   (incf x))
	  (t (setf (cursor-x stream) x)
	     (stream-write-char stream char)
	     (setf x (cursor-x stream) y (cursor-y stream))))
      finally
	(setf (cursor-x stream) x))
  string)

#+ignore
(defmethod stream-write-escaped-string ((stream console) string escaped-char
					&optional (start 0) (end (length string)))
  (stream-write-char stream escaped-char)
  (loop with w = (console-width stream)
      with x = (cursor-x stream) and y = (cursor-y stream)
      for i from start below end
      as char = (char string i)
      do (when (>= x w)
	   (setf (cursor-x stream) x)
	   (stream-write-char stream #\newline)
	   (setf x (cursor-x stream) y (cursor-y stream)))
	 (when (or (eql char escaped-char) (char= char #\\))
	   (setf (console-char stream x y) #\\)
	   (incf x))
	 (when (>= x w)
	   (setf (cursor-x stream) x)
	   (stream-write-char stream #\newline)
	   (setf x (cursor-x stream) y (cursor-y stream)))
	 (cond
	  ((graphic-char-p char)
	   (setf (console-char stream x y) char)
	   (incf x))
	  (t (setf (cursor-x stream) x)
	     (stream-write-char stream char)
	     (setf x (cursor-x stream) y (cursor-y stream))))
      finally
	(setf (cursor-x stream) x))
  (stream-write-char stream escaped-char)
  string)

(defmethod scroll-down ((console console))
  "This method is painfully slow, and so should be specialized if at all possible."
  (dotimes (y (1- (console-height console)))
    (dotimes (x (console-width console))
      (setf (console-char console x y)
	(console-char console x (1+ y)))))
  (clear-line console 0 (1- (console-height console)))
  (signal 'muerte::newline)
  nil)

(defmethod scroll-down :after (console)
  (incf *scroll-offset*))

(defmethod clear-console ((console console))
  (dotimes (y (console-height console))
    (clear-line console 0 y)))

