;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      print.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep  3 11:48:19 2001
;;;;                
;;;; $Id: print.lisp,v 1.5 2004/04/06 14:29:33 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :x86-pc/package)
(require :muerte/typep)
(require :muerte/integers)
(provide :muerte/print)

(in-package muerte)

(defvar *print-escape* t)
(defvar *print-readably* nil)
(defvar *print-gensym* t)
(defvar *print-base* 16)
(defvar *print-radix* t)
(defvar *print-array* t)
(defvar *print-length* 8)
(defvar *print-level* 3)
(defvar *print-pretty* t)
(defvar *print-circle* nil)

(defvar *print-safely* nil)

(defvar *standard-output* #'muerte.x86-pc::textmode-console)
(defvar *standard-input* #'muerte.x86-pc::textmode-console)
(defvar *debug-io* #'muerte.x86-pc::textmode-console)
(defvar *terminal-io* #'muerte.x86-pc::textmode-console)
(defvar *trace-output* #'muerte.x86-pc::textmode-console)
(defvar *error-output* #'muerte.x86-pc::textmode-console)
(defvar *query-io* #'muerte.x86-pc::textmode-console)

(defvar *never-use-print-object* :after-clos-bootstrapped)

(defun init-print-unreadable (object stream &optional type-p)
  (when *print-readably*
    (error 'print-not-readable :object object))
  (write-string "#<" stream)
  (when type-p
    (write (type-of object) :stream stream))
  nil)

(defmacro print-unreadable-object ((object stream &key type identity) &body body)
  (let ((stream-var (gensym "stream-var-"))
	(object-var (gensym "object-var-")))
    `(let ((,stream-var ,stream)
	   (,object-var ,object))
       (init-print-unreadable ,object-var ,stream-var
			      ,@(when type (list type)))
       ,@body
       ,(when identity
	  `(when ,identity
	     (format ,stream-var " @ ~Z" ,object-var)))
       (write-char #\> ,stream-var)
       nil)))

(defun write-digit (x stream)
  (if (<= 0 x 9)
      (write-char (code-char (+ x (char-code #\0))) stream)
    (write-char (code-char (+ x -10 (char-code #\a))) stream)))
     
(defun write-simple-integer (x base stream)
  (cond
   ((< x 0)
    (write-char #\- stream)
    (write-simple-integer (- x) base stream))
   (t (let ((bigit (truncate x base)))
	(unless (zerop bigit)
	  (write-simple-integer bigit base stream)))
      (write-digit (rem x base) stream))))

(defun write-lowlevel-integer (x stream base comma-char comma-interval mincol padchar sign-char pos)
  (let ((bigit (truncate x base)))
    (cond
     ((zerop bigit)
      (when mincol
	(do ((i (+ pos 1 (if sign-char 1 0) (if comma-interval (truncate pos comma-interval) 0))
		(1+ i)))
	    ((>= i mincol))
	  (write-char padchar stream)))
      (when sign-char
	(write-char sign-char stream)))
     (t (write-lowlevel-integer bigit stream base comma-char comma-interval
				mincol padchar sign-char (1+ pos)))))
  (write-digit (rem x base) stream)
  (when (and comma-interval (plusp pos) (zerop (rem pos comma-interval)))
    (write-char comma-char stream))
  nil)

(defun write-integer (x stream &key (base *print-base*) (radix *print-radix*)
				    mincol (padchar #\space)
				    (sign-always nil) (comma-char #\,) (comma-interval nil))
  (when radix
    (case base
      (10)				; put a #\. at the end.
      (2 (write-string "#b" stream))
      (8 (write-string "#o" stream))
      (16 (write-string "#x" stream))
      (t (write-char #\# stream)
	 (write-simple-integer base 10 stream)
	 (write-char #\r stream))))
  (block minus-hack			; don't barf on most-negative-fixnum
    (multiple-value-bind (sign-char print-value)
	(cond
	 ((minusp x)
	  (if (not (eq x most-negative-fixnum))
	      (values #\- (- x))
	    (return-from minus-hack
	      (write-string (case base
			      (2 #.(cl:format cl:nil "~B" movitz::+movitz-most-negative-fixnum+))
			      (8 #.(cl:format cl:nil "~O" movitz::+movitz-most-negative-fixnum+))
			      (10 #.(cl:format cl:nil "~D" movitz::+movitz-most-negative-fixnum+))
			      (16 #.(cl:format cl:nil "~X" movitz::+movitz-most-negative-fixnum+))
			      (t "minus-hack"))
			    stream))))
	 (sign-always
	  (values #\+ x))
	 (t (values nil x)))
      (write-lowlevel-integer print-value stream base comma-char comma-interval
			      mincol padchar sign-char 0)))
  (when (and radix (= 10 base))
    (write-char #\. stream))
  nil)

(defun write-char (character &optional stream)
  (%write-char character (output-stream-designator stream)))
       
(defun write-string (string &optional stream &key (start 0) (end (length string)))
  (with-subvector-accessor (string-ref string start end)
    (do ((i start (1+ i)))
	((>= i end))
      (write-char (string-ref i) stream)))
  #+ignore (stream-write-string (output-stream-designator stream) string start end))

(defun write-line (string &optional stream &key (start 0) (end (length string)))
  (write-string string stream :start start :end end)
  (write-char #\Newline stream)
  string)

(defun write (object &rest key-args
	      &key stream case circle safe-recursive-call
		   (array *print-array*) (base *print-base*)
		   ((:escape *print-escape*) *print-escape*)
		   ((:gensym *print-gensym*) *print-gensym*)
		   (length *print-length*)
		   (level *print-level*) lines miser-width pprint-dispatch
		   (pretty *print-pretty*) (radix *print-radix*)
		   ((:readably *print-readably*) *print-readably*)
		   right-margin)
  (declare (dynamic-extent key-args)
	   (special *read-base* *package*)
	   (ignore case circle pprint-dispatch miser-width right-margin lines))
  (cond
   ((and *print-safely* (not safe-recursive-call))
    (handler-case (apply #'write object :safe-recursive-call t key-args)
      (t (condition)
	(write-string "#<printer error>" stream))))
   ((and (not pretty)
	 (not *never-use-print-object*))
    (print-object object stream))
   (t (let ((do-escape-p (or *print-escape* *print-readably*))
	    (stream (output-stream-designator stream))
	    (*print-level* (minus-if level 1)))
	(typecase object
	  (character
	   (if (not do-escape-p)
	       (write-char object stream)
	     (progn
	       (write-string "#\\" stream)
	       (let ((name (char-name object)))
		 (if name
		     (write-string name stream)
		   (write-char object stream))))))
	  (null
	   (write-string (symbol-name nil) stream))
	  ((or cons tag5)
	   (cond
	    ((and *print-level* (minusp *print-level*))
	     (write-char #\# stream))
	    ((and (eq 'quote (car object))
		  (not (cddr object)))
	     (write-char #\' stream)
	     (write (cadr object) :stream stream))
	    (t (labels ((write-cons (c stream length)
			  (cond
			   ((and length (= 0 length))
			    (write-string "...)"))
			   (t (write (car c) :stream stream)
			      (typecase (cdr c)
				(null
				 (write-char #\) stream))
				(cons
				 (write-char #\space stream)
				 (write-cons (cdr c) stream (minus-if length 1)))
				(t
				 (write-string " . " stream)
				 (write (cdr c) :stream stream)
				 (write-char #\) stream)))))))
		 (write-char #\( stream)
		 (write-cons object stream length)))))
	  (integer
	   (write-integer object stream :base base :radix radix))
	  (string
	   (if do-escape-p
	       (stream-write-escaped-string stream object #\")
	     (write-string object stream)))
	  (symbol			; 22.1.3.3 Printing Symbols
	   (flet ((write-symbol-name (symbol stream)
		    (let ((name (symbol-name symbol)))
		      (if (and (plusp (length name))
			       (every (lambda (c)
					(or (upper-case-p c)
					    (member c '(#\- #\% #\$ #\* #\@ #\. #\& #\< #\> #\=))
					    (digit-char-p c)))
				      name)
			       (not (every (lambda (c)
					     (or (digit-char-p c *read-base*)
						 (member c '(#\.))))
					   name)))
			  (write-string name stream)
			(stream-write-escaped-string stream name #\|)))))
	     (cond
	      ((not do-escape-p)
	       (write-symbol-name object stream))
	      ((eq (symbol-package object) (find-package "KEYWORD"))
	       (write-string ":" stream)
	       (write-symbol-name object stream))
	      ((or (eq (symbol-package object) *package*)
		   (eq (find-symbol (string object))
		       object))
	       (write-symbol-name object stream))
	      ((symbol-package object)
	       (let ((package (symbol-package object)))
		 (write-string (package-name package) stream)
		 (write-string (if (gethash (symbol-name object)
					    (package-object-external-symbols package))
				   ":" "::")
			       stream)
		 (write-symbol-name object stream)))
	      ((not (symbol-package object))
	       (when *print-gensym*
		 (write-string "#:" stream))
	       (write-symbol-name object stream))
	      (t (error "Huh?")))))
	  (vector
	   (cond
	    ((and *print-level* (minusp *print-level*))
	     (write-char #\# stream))
	    ((or array *print-readably*)
	     (write-string "#(" stream)
	     (cond
	      ((and length (< length (length object)))
	       (dotimes (i length)
		 (unless (= 0 i)
		   (write-char #\space stream))
		 (write (aref object i)))
	       (write-string " ...)" stream))
	      (t (dotimes (i (length object))
		   (unless (= 0 i)
		     (write-char #\space stream))
		   (write (aref object i) :stream stream))
		 (write-char #\) stream))))
	    (t (print-unreadable-object (object stream :identity t)
		 (princ (type-of object) stream)))))
	  (standard-gf-instance
	   (print-unreadable-object (object stream)
	     (format stream "gf ~S" (funobj-name object))))
	  (compiled-function
	   (print-unreadable-object (object stream)
	     (format stream "function ~S" (funobj-name object))))
	  (hash-table
	   (print-unreadable-object (object stream :identity nil :type nil)
	     (format stream "~S hash-table with ~D entries"
		     (let ((test (hash-table-test object)))
		       (if (typep test 'compiled-function)
			   (funobj-name test)
			 test))
		     (hash-table-count object))))
	  (package
	   (if (package-name object)
	       (print-unreadable-object (object stream :identity nil :type nil)
		 (format stream "Package ~A with ~D+~D symbols"
			 (package-name object)
			 (hash-table-count (package-object-external-symbols object))
			 (hash-table-count (package-object-internal-symbols object))))
	     (print-unreadable-object (object stream :identity t :type t))))
	  (t (if (not *never-use-print-object*)
		 (print-object object stream)
	       (print-unreadable-object (object stream :identity t)
		 (cond
		  ((typep object 'std-instance)
		   (write-string "[std-instance]" stream)
		   (write (standard-instance-access (std-instance-class object) 0) :stream stream))
		  ((typep object 'standard-gf-instance)
		   (write-string "[std-gf-instance]" stream))
		  (t (princ (type-of object) stream))))))))))
  object)

(defun prin1 (object &optional stream)
  (write object :stream stream :escape t))

(defun princ (object &optional stream)
  (write object :stream stream :escape nil :readably nil))

(defun print (object &optional stream)
  (terpri stream)
  (write object :stream stream :escape t)
  (write-char #\Space stream)
  object)

(defun pprint (object &optional stream)
  (write object :stream stream :escape t :pretty t)
  (values))

(defun terpri (&optional stream)
  (write-char #\newline stream)
  nil)

(defun fresh-line (&optional stream)
  (let ((stream (output-stream-designator stream)))
    (if (functionp stream)
	(funcall stream 'stream-fresh-line)
      (terpri stream)))
  #+ignore (stream-fresh-line (output-stream-designator stream)))

(defun print-word-indirect (x stream)
  (check-type x fixnum "A fixnum-pointer.")
  (when *print-radix*
    (write-string "#x" stream))
  (let ((z nil))
    #.(cl:cons 'progn
	       (cl:loop for octet from 3 downto 1
		   collecting 
		     `(let ((n (memref x 0 ,octet :unsigned-byte8)))
			(when (setq z (or z (<= #x10 n)))
			  (write-digit (ldb (byte 4 4) n) stream))
			(when (setq z (or z (plusp n)))
			  (write-digit (ldb (byte 4 0) n) stream)))))
    (let ((n (memref x 0 0 :unsigned-byte8)))
      (when (or z (<= #x10 n))
	(write-digit (ldb (byte 4 4) n) stream))
      (write-digit (ldb (byte 4 0) n) stream)))
  (values))

(defun print-word (x stream)
  (when *print-radix*
    (write-string "#x" stream))
  (let ((z nil))
    #.(cl:cons 'progn
	       (cl:loop for nibble from 7 downto 1
		   collecting 
		     `(let ((n (word-nibble x ,nibble)))
			(when (setq z (or z (plusp n)))
			  (write-digit n stream))))))
  (write-digit (word-nibble x 0) stream)
  (values))
