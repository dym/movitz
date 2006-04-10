;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      movitz.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Oct  9 20:52:58 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: movitz.lisp,v 1.11 2006/04/10 11:45:36 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defvar *i* nil)			; These hold the previous built images,
(defvar *ii* nil)			; for interactive use.

(defvar *image*)

(define-symbol-macro *movitz-nil*
    (image-nil-object *image*))

(define-unsigned lu16 2 :little-endian)
(define-unsigned lu32 4 :little-endian)

(defconstant +code-vector-word-offset+ 2)
(defconstant +code-vector-transient-word+
    (ldb (byte 32 0)
	 (- +code-vector-word-offset+)))

(defvar +movitz-multiple-values-limit+ 63)

(defvar *bq-level* 0)
(defvar *default-image-init-file* #p"losp/los0.lisp")
(defvar *default-image-file* #p"los0-image")

(defvar *movitz-host-features* *features*
  "The *features* of the host implementation.")

(defmacro with-host-environment (options &body body)
  "Execute body in a `normal' host environment."
  (declare (ignore options))
  `(let ((*features* *movitz-host-features*))
     ,@body))

(defmacro print-unreadable-movitz-object ((object stream &rest key-args) &body body)
  "Just like print-unreadable-object, just adorn output so as to
make clear it's a Movitz object, with extra <..>"
  (let ((stream-var (gensym "unreadable-movitz-stream-")))
    `(let ((,stream-var ,stream))
       (print-unreadable-object (,object ,stream-var ,@key-args)
	 (write-char #\< ,stream-var)
	 ,@body
	 (write-char #\> ,stream-var)))))

(defun movitz-syntax-sharp-dot (stream subchar arg)
  (declare (ignore arg subchar))
  (let ((form (read stream t nil t)))
    (values (unless *read-suppress*
	      (eval (muerte::translate-program form :muerte.cl :cl))))))

(defmacro with-movitz-syntax (options &body body)
  (declare (ignore options))
  `(let ((*readtable* (copy-readtable)))
     (set-dispatch-macro-character #\# #\'
				   (lambda (stream subchar arg)
				     (declare (ignore subchar arg))
				     (list 'muerte.common-lisp::function
					   (read stream t nil t))))
     (set-dispatch-macro-character #\# #\{
				   (lambda (stream subchar arg)
				     (declare (ignore subchar arg))
				     (let ((data (read-delimited-list #\} stream)))
				       (make-movitz-vector (length data)
							   :element-type 'movitz-unboxed-integer-u8
							   :initial-contents data))))
     (set-dispatch-macro-character #\# #\. (lambda (stream subchar arg)
					     (declare (ignore arg subchar))
					     (let ((form (read stream t nil t)))
					       (values (unless *read-suppress*
							 (eval (muerte::translate-program form :muerte.cl :cl)))))))
     (set-macro-character #\` (lambda (stream char)
				(declare (ignore char))
				(let ((*bq-level* (1+ *bq-level*)))
				  (list 'muerte::movitz-backquote (read stream t nil t)))))
     (set-macro-character #\, (lambda (stream char)
				(declare (ignore char))
				(assert (plusp *bq-level*) ()
				  "Comma not inside backquote.")
				(let* ((next-char (read-char stream t nil t))
				       (comma-type (case next-char
						     (#\@ 'backquote-comma-at)
						     (#\. 'backquote-comma-dot)
						     (t (unread-char next-char stream)
							'backquote-comma))))
				  (list comma-type (read stream t nil t)))))
     ,@body))

(defun un-backquote (form level)
  "Dont ask.."
  (declare (notinline un-backquote))
  (assert (not (minusp level)))
  (values
   (typecase form
     (null nil)
     (list
      (case (car form)
	(backquote-comma
	 (cadr form))
	(t (cons 'append
		 (loop for sub-form-head on form
		     as sub-form = (and (consp sub-form-head)
					(car sub-form-head))
		     collecting
		       (cond
			((atom sub-form-head)
			 (list 'quote sub-form-head))
			((atom sub-form)
			 (list 'quote (list sub-form)))
			(t (case (car sub-form)
			     (muerte::movitz-backquote
			      (list 'list
				    (list 'list (list 'quote 'muerte::movitz-backquote)
					  (un-backquote (cadr sub-form) (1+ level)))))
			     (backquote-comma
			      (cond
			       ((= 0 level)
				(list 'list (cadr sub-form)))
			       ((and (listp (cadr sub-form))
				     (eq 'backquote-comma-at (caadr sub-form)))
				(list 'append
				      (list 'mapcar
					    '(lambda (x) (list 'backquote-comma x))
					    (cadr (cadr sub-form)))))
			       (t (list 'list
					(list 'list
					      (list 'quote 'backquote-comma)
					      (un-backquote (cadr sub-form) (1- level)))))))
			     (backquote-comma-at
			      (if (= 0 level)
				  (cadr sub-form)
				(list 'list
				      (list 'list
					    (list 'quote 'backquote-comma-at)
					    (un-backquote (cadr sub-form) (1- level))))))
			     (t (list 'list (un-backquote sub-form level))))))
		     when (not (listp (cdr sub-form-head)))
		     collect (list 'quote (cdr sub-form-head)))
		 ))))
     (array
      (error "Array backquote not implemented."))
     (t (list 'quote form)))))

(defmacro muerte::movitz-backquote (form)
  (un-backquote form 0))

#+allegro
(excl:defsystem :movitz ()
  (:serial
   "movitz"
   "parse"
   "eval"
   "multiboot"
   "bootblock"
   "environment"
   "compiler-types"
   (:definitions "compiler-protocol"
       "storage-types")
   "image"
   "stream-image"
   "procfs-image"
   "assembly-syntax"
   (:definitions "compiler-protocol"
       (:parallel "compiler" "special-operators" "special-operators-cl"))))

#+allegro
(progn
  (defun muerte.common-lisp::package-name (package)
    (package-name package))
  (defun muerte.cl:find-package (name)
    (find-package name)))
