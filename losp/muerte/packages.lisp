;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2002-2004
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      packages.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Aug 30 15:19:43 2001
;;;;                
;;;; $Id: packages.lisp,v 1.1 2004/01/13 11:05:05 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)

(provide :muerte/packages)

(in-package muerte)

(defvar *package*)

(defstruct (package
	    (:predicate packagep)
	    (:constructor make-package-object)
	    (:conc-name package-object-))
  name
  external-symbols
  internal-symbols
  shadowing-symbols-list
  use-list)

(defun package-name (object)
  (package-object-name (find-package object)))

(defun package-use-list (package-name)
  (package-object-use-list (find-package package-name)))

(defun find-package (name)
  (if (packagep name)
      name
    (find-package-string (string name))))

(defun find-package-string (name &optional (start 0) (end (length name)) (key 'identity))
  (values (gethash-string name start end
			  (get-global-property :packages)
			  nil key)))

(defun assert-package (name)
  (or (find-package name)
      (error "There is no package named ~S." name)))

(defun find-symbol-string (name start end key &optional (package *package*))
  (check-type name string)
  (let ((package (assert-package package)))
    (macrolet ((try (status hash-table)
		 `(multiple-value-bind (s p)
		      (gethash-string name start end ,hash-table :key key)
		    (when p (return-from symbol-search (values s ,status))))))
      (block symbol-search
	(try :internal (package-object-internal-symbols package))
	(try :external (package-object-external-symbols package))
	(dolist (used-package (package-use-list package))
	  (try :inherited (package-object-external-symbols used-package)))
	(values nil nil)))))

(defun find-symbol (name &optional (package *package*))
  (check-type name string)
  (find-symbol-string name 0 (length name) 'identity package))

(defun intern-string (name &optional (package *package*) &key (start 0) (end (length name))
							      (key 'identity))
  "intern enters a symbol named string into package. If a symbol whose
  name is the same as string is already accessible in package, it is
  returned. If no such symbol is accessible in package, a new symbol
  with the given name is created and entered into package as an
  internal symbol, or as an external symbol if the package is the
  KEYWORD package; package becomes the home package of the created symbol."
  (let ((package (assert-package package)))
    (multiple-value-bind (symbol status)
	(find-symbol-string name start end key package)
      (unless status
	(let ((name (subseq name start end)))
	  (map-into name key name)
	  (setf symbol (make-symbol name))
	  (when (eq package (find-package :keyword))
	    (setf (symbol-flags symbol)
	      #.(bt:enum-value 'movitz::movitz-symbol-flags '(:constant-variable)))
	    (setf (symbol-value symbol)
	      symbol))))
      (unless (symbol-package symbol)
	(setf-movitz-accessor (symbol movitz-symbol package) package))
      (unless status
	(if (eq package (find-package :keyword))
	    (setf (gethash (symbol-name symbol) (package-object-external-symbols package)) symbol)
	  (setf (gethash (symbol-name symbol) (package-object-internal-symbols package)) symbol)))
      (values symbol status))))

(defun intern (name &optional (package *package*))
  (intern-string name package))

(defmacro do-all-symbols ((var &optional result-form) &body declarations-and-body)
  (let ((next-package (gensym))
	(more-packages-var (gensym))
	(dummy (gensym))
	(package-var (gensym))
	(package-hash-var (gensym))
	(state-var (gensym "do-all-symbols-state-"))
	(next-symbol (gensym))
	(more-symbols-var (gensym))
	(symbol-var (gensym)))
    `(with-hash-table-iterator (,next-package (get-global-property :packages))
       (do () (nil)
	 (multiple-value-bind (,more-packages-var ,dummy ,package-var)
	     (,next-package)
	   (declare (ignore ,dummy))
	   (unless ,more-packages-var
	     (return ,result-form))
	   (do ((,state-var '(:externals :internals) (cdr ,state-var))
		(,package-hash-var (package-object-external-symbols ,package-var)
				   (package-object-internal-symbols ,package-var)))
	       ((null ,state-var))
	     (with-hash-table-iterator (,next-symbol ,package-hash-var)
	       (do () (nil)
		 (multiple-value-bind (,more-symbols-var ,dummy ,symbol-var)
		     (,next-symbol)
		   (declare (ignore ,dummy))
		   (unless ,more-symbols-var (return nil))
		   (let ((,var ,symbol-var))
		     ,@declarations-and-body))))))))))

(defmacro do-external-symbols ((var &optional (package *package*) result-form) &body declarations-and-body)
  (let ((next-var (gensym))
	(more-var (gensym))
	(key-var (gensym)))
    `(with-hash-table-iterator (,next-var (package-object-external-symbols (assert-package ,package)))
       (do () (nil)
	 (multiple-value-bind (,more-var ,key-var ,var) (,next-var)
	   (unless ,more-var (return ,result-form))
	   (let () ,@declarations-and-body))))))

(defmacro do-symbols ((var &optional (package '*package*) result-form) &body declarations-and-body)
  (let ((state-var (gensym))
	(package-object-var (gensym))
	(hash-table-var (gensym))
	(use-list-var (gensym))
	(more-var (gensym))
	(key-var (gensym))
	(next-var (gensym)))
    `(do* ((,state-var 0 (1+ ,state-var))
	   (,package-object-var (assert-package ,package))
	   (,use-list-var (package-object-use-list ,package-object-var))
	   (,hash-table-var (package-object-external-symbols ,package-object-var)
			    (case ,state-var
			      (1 (package-object-internal-symbols ,package-object-var))
			      (t (let ((x (pop ,use-list-var)))
				   (and x (package-object-external-symbols x)))))))
	 ((not ,hash-table-var) ,result-form)
       (with-hash-table-iterator (,next-var ,hash-table-var)
	 (do () (nil)
	   (multiple-value-bind (,more-var ,key-var ,var) (,next-var)
	     (declare (ignore ,key-var))
	     (if ,more-var
		 (let () ,@declarations-and-body)
	       (return))))))))


(defun apropos (string &optional package)
  (flet ((apropos-symbol (symbol string)
	   (when (search string (symbol-name symbol) :test #'char-equal)
	     (cond
	      ((keywordp symbol)
	       (format t "~&~W == keyword~%" symbol))
	      ((fboundp symbol)
	       (format t "~&~W == function arglist: ~A~%"
		       symbol (funobj-lambda-list (symbol-function symbol))))
	      ((boundp symbol)
	       (format t "~&~W == variable value: ~S~%"
		       symbol (symbol-value symbol)))
	      (t (format t "~&~W~%" symbol))))))
    (let ((string (string string)))
      (if package
	  (do-symbols (symbol package)
	    (apropos-symbol symbol string))
	(do-all-symbols (symbol)
	  (apropos-symbol symbol string)))))
  (values))
