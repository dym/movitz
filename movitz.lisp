;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromsø, Norway
;;;; 
;;;; Filename:      movitz.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Oct  9 20:52:58 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: movitz.lisp,v 1.1 2004/01/13 11:04:59 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defvar *i* nil)			; These hold the previous built images,
(defvar *ii* nil)			; for interactive use.

(defvar *image*)

(define-unsigned lu16 2 :little-endian)
(define-unsigned lu32 4 :little-endian)

(defconstant +code-vector-word-offset+ 2)
(defconstant +movitz-multiple-values-limit+ 127)

(defvar *bq-level* 0)
(defvar *default-image-init-file* #p"losp/los0.lisp")
(defvar *default-image-file* #p"los0-image")

(defmacro with-movitz-syntax (() &body body)
  `(let ((*readtable* (copy-readtable)))
     (set-dispatch-macro-character #\# #\'
				   (lambda (stream subchar arg)
				     (declare (ignore subchar arg))
				     (list 'muerte.common-lisp::function
					   (read stream t nil t))))
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
			     (t (list 'list (un-backquote sub-form level)))))))))))
     (array
      (error "Array backquote not implemented."))
     (t (list 'quote form)))))

(defmacro muerte::movitz-backquote (form)
  (un-backquote form 0))

(defun f1 (x) (cons 'f1 x))
(defun f2 () (f1 'f2))
(defun f3 () (cons (f1 'f3-arg) (f2)))
(defun f4 () (values))
(defun f5 () (values 'val1 'val2 'val3 'val4))


(defconstant xx (list 'a 'b 'c))

(defun pingle (val)
  (case val
    (1 'x)
    (2 'y)))

(let ((var 'top))
  (defun s1 (val) (setf var val))
  (defun r1 ()
    var)
  (setf var 'bot)
  (defun r2 () var))

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
