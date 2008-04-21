;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      print.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep  3 11:48:19 2001
;;;;                
;;;; $Id: print.lisp,v 1.27 2008-04-21 19:42:26 ffjeld Exp $
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
(defvar *print-case* :upcase)
(defvar *print-lines* nil)
(defvar *print-miser-width* nil)

(defvar *print-safely* nil)

(defvar *standard-output* #'muerte.x86-pc::textmode-console)
(defvar *standard-input* #'muerte.x86-pc::textmode-console)
(defvar *debug-io* #'muerte.x86-pc::textmode-console)
(defvar *terminal-io* #'muerte.x86-pc::textmode-console)
(defvar *trace-output* #'muerte.x86-pc::textmode-console)
(defvar *error-output* #'muerte.x86-pc::textmode-console)
(defvar *query-io* #'muerte.x86-pc::textmode-console)

(defvar *never-use-print-object* :after-clos-bootstrapped)

(defun init-print-unreadable (object stream &optional type-p bodyless-p)
  (when *print-readably*
    (error 'print-not-readable :object object))
  (write-string "#<" stream)
  (when type-p
    (write (type-of object) :stream stream)
    (unless bodyless-p
      (write-char #\space stream)))
  nil)

(defmacro print-unreadable-object ((object stream &key type identity) &body body)
  (let ((stream-var (gensym "stream-var-"))
	(object-var (gensym "object-var-")))
    `(let ((,stream-var ,stream)
	   (,object-var ,object))
       (init-print-unreadable ,object-var ,stream-var
			      ,@(when type (list type))
			      ,@(when (and type (null body)) (list t)))
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

(defun write-integer-lowlevel (x stream base comma-char comma-interval mincol padchar sign-char pos)
  (multiple-value-bind (remainder digit)
      (truncate x base)
    (cond
     ((zerop remainder)
      (when mincol
	(do ((i (+ pos 1 (if sign-char 1 0) (if comma-interval (truncate pos comma-interval) 0))
		(1+ i)))
	    ((>= i mincol))
	  (declare (index i))
	  (write-char padchar stream)))
      (when sign-char
	(write-char sign-char stream)))
     (t (write-integer-lowlevel remainder stream base comma-char comma-interval
				mincol padchar sign-char (1+ pos))))
    (write-digit digit stream))
  (when (and comma-interval (plusp pos) (zerop (rem pos comma-interval)))
    (write-char comma-char stream))
  nil)

(defun write-integer-lowlevel-ldb (x stream comma-char comma-interval mincol padchar sign-char pos
				   digit-length)
  (let* ((digit (ldb (byte digit-length (* pos digit-length)) x)))
    (cond
     ((<= (integer-length x) (* (1+ pos) digit-length))
      (when mincol
	(do ((i (+ pos 1 (if sign-char 1 0) (if comma-interval (truncate pos comma-interval) 0))
		(1+ i)))
	    ((>= i mincol))
	  (write-char padchar stream)))
      (when sign-char
	(write-char sign-char stream)))
     (t (write-integer-lowlevel-ldb x stream comma-char comma-interval
				    mincol padchar sign-char (1+ pos) digit-length)))
    (write-digit digit stream))
  (when (and comma-interval (plusp pos) (zerop (rem pos comma-interval)))
    (write-char comma-char stream))
  nil)

(defun write-integer (x stream base radix
		      &optional mincol (padchar #\space)
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
  (multiple-value-bind (sign-char print-value)
      (cond
       ((minusp x)
	(values #\- (- x)))
       (sign-always
	(values #\+ x))
       (t (values nil x)))
    (if (= 1 (logcount base))
	(write-integer-lowlevel-ldb print-value stream comma-char comma-interval
				    mincol padchar sign-char 0 (1- (integer-length base)))
      (write-integer-lowlevel print-value stream base comma-char comma-interval
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
      (declare (index i))
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
  (numargs-case
   (t (object &key stream
	      ;; lines miser-width pprint-dispatch right-margin case circle
	      ((:array *print-array*) *print-array*)
	      ((:base *print-base*) *print-base*)
	      ((:escape *print-escape*) *print-escape*)
	      ((:gensym *print-gensym*) *print-gensym*)
	      ((:length *print-length*) *print-length*)
	      ((:level *print-level*) *print-level*)
	      ((:pretty *print-pretty*) *print-pretty*)
	      ((:radix *print-radix*) *print-radix*)
	      ((:readably *print-readably*) *print-readably*))
      (let ((*standard-output* (output-stream-designator stream)))
	(write object)))
   (1 (object)
      (if (not *print-safely*)
	  (internal-write object)
	(handler-case (internal-write object)
	  (serious-condition (c)
	    (print-unreadable-object (c *standard-output* :type t :identity t)
	      (format t "(while printing ~Z)" object))))))))

(defun write-to-string (object &rest args)
  (declare (dynamic-extent args))
  (let ((string (make-array 24 :element-type 'character :fill-pointer 0 :adjustable t)))
    (apply 'write object :stream string args)
    string))

(defun internal-write (object)
  (let ((stream *standard-output*))
    (cond
     ((and (not *print-pretty*)
	   (not *never-use-print-object*))
      (print-object object stream))
     (t (let ((do-escape-p (or *print-escape* *print-readably*))
	      (*print-level* (minus-if *print-level* 1)))
	  (typecase object
	    (unbound-value
	     (write-string "#<unbound!>" stream))
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
	     (let ((level *print-level*))
	       (cond
		 ((and (not do-escape-p)
		       level
		       (minusp level))
		  (write-char #\# stream))
		 ((and (eq 'quote (car object))
		       (not (cddr object)))
		  (write-char #\' stream)
		  (write (cadr object)))
                 ((and (eq 'backquote (car object))
		       (not (cddr object)))
		  (write-char #\` stream)
		  (write (cadr object)))
                 ((and (eq 'backquote-comma (car object))
		       (not (cddr object)))
		  (write-char #\, stream)
		  (write (cadr object)))
                 ((and (eq 'function (car object))
		       (not (cddr object)))
		  (write-char #\# stream)
                  (write-char #\' stream)
		  (write (cadr object)))
		 (t (labels ((write-cons (c stream length)
			       (cond
				 ((and length (= 0 length))
				  (write-string "...)"))
				 (t (write (car c))
				    (typecase (cdr c)
				      (null
				       (write-char #\) stream))
				      (cons
				       (write-char #\space stream)
				       (write-cons (cdr c) stream (minus-if length 1)))
				      (t
				       (write-string " . " stream)
				       (write (cdr c))
				       (write-char #\) stream)))))))
		      (write-char #\( stream)
		      (write-cons object stream *print-length*))))))
	    (integer
	     (write-integer object stream *print-base* *print-radix*))
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
					      (member c '(#\+ #\- #\% #\$ #\* #\@ #\. #\&
							  #\/ #\< #\> #\= #\_))
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
	    (bit-vector
	     (write-string "#*")
	     (dotimes (i (length object))
	       (write (aref object i) :radix nil)))
	    (vector
	     (let ((level *print-level*)
		   (length *print-length*))
	       (cond
		((and level (minusp level))
		 (write-char #\# stream))
		((or *print-array* *print-readably*)
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
		       (write (aref object i)))
		     (write-char #\) stream))))
		(t (print-unreadable-object (object stream :identity t :type t))))))
	    (standard-gf-instance
	     (print-unreadable-object (object stream)
	       (format stream "gf ~S" (funobj-name object))))
	    (macro-function
	     (print-unreadable-object (object stream)
	       (format stream "macro-function ~S" (funobj-name object))))
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
	    (ratio
	     (write-integer (ratio-numerator object) stream *print-base* *print-radix*)
	     (write-char #\/ stream)
	     (write-integer (ratio-denominator object) stream *print-base* nil))
	    (t (if (not *never-use-print-object*)
		   (print-object object stream)
		 (print-unreadable-object (object stream :identity t)
		   (cond
		    ((typep object 'std-instance)
		     (write-string "[std-instance]" stream)
		     (write (standard-instance-access (std-instance-class object) 0)))
		    ((typep object 'standard-gf-instance)
		     (write-string "[std-gf-instance]" stream))
		    (t (princ (type-of object) stream)))))))))))
  object)

(defun prin1 (object &optional stream)
  (let ((*standard-output* (output-stream-designator stream))
	(*print-escape* t))
    (write object)))

(defun princ (object &optional stream)
  (let ((*standard-output* (output-stream-designator stream))
	(*print-escape* nil)
	(*print-readably* nil))
    (write object)))

(defun print (object &optional stream)
  (let ((*standard-output* (output-stream-designator stream))
	(*print-escape* t))
    (write-char #\newline)
    (write object)
    (write-char #\Space)
    object))

(defun pprint (object &optional stream)
  (let ((*standard-output* (output-stream-designator stream))
	(*print-escape* t)
	(*print-pretty* t))
    (write object)
    (values)))

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
		     `(let ((n (memref x 0 :index ,octet :type :unsigned-byte8)))
			(when (setq z (or z (<= #x10 n)))
			  (write-digit (ldb (byte 4 4) n) stream))
			(when (setq z (or z (plusp n)))
			  (write-digit (ldb (byte 4 0) n) stream)))))
    (let ((n (memref x 0 :type :unsigned-byte8)))
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
