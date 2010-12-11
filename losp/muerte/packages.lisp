;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2002-2005
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      packages.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Aug 30 15:19:43 2001
;;;;                
;;;; $Id: packages.lisp,v 1.17 2008-04-27 19:43:37 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)

(provide :muerte/packages)

(in-package muerte)

(defstruct (package
	    (:predicate packagep)
	    (:constructor make-package-object)
	    (:conc-name package-object-))
  name
  (external-symbols (make-hash-table :test #'equal))
  (internal-symbols (make-hash-table :test #'equal))
  shadowing-symbols-list
  use-list
  nicknames)

(defvar *packages*)			; Set by dump-image.

(deftype package-designator ()
  '(or package string-designator))

(defun make-package (name &key nicknames use)
  (let ((name* (string name))
        (nicknames* (mapcar #'string nicknames))
        (use* (mapcar #'find-package use)))
    (when (some #'null use*)
      (warn "Cannot use nonexisting package ~S."
            (find-if-not #'find-package use))
      (setf use* (remove nil use*)))
    (let ((existing-packages (remove-if-not #'find-package (cons name* nicknames*))))
      (when existing-packages
        (cerror "Create the package anyway."
                "There already exist package~P by the name~:P ~{~A~^ ~}."
                (length existing-packages)
                existing-packages)))
    (let ((package (make-package-object :name name*
                                        :use-list use*
                                        :nicknames nicknames*)))
      (dolist (nickname nicknames*)
        (setf (gethash nickname *packages*) package))
      (setf (gethash name* *packages*) package))))

(defun delete-package (package)
  (let ((package (find-package package)))
    (when (and (package-name package)
               (eq package (find-package (package-name package))))
      (dolist (nickname (package-nicknames package))
        (when (eq package (gethash nickname *packages*))
          (setf (gethash nickname *packages*) nil)))
      (setf (gethash (package-name package) *packages*)
            nil)
      (setf (package-object-name package) nil)
      t)))

(defun package-name (object)
  (package-object-name (find-package object)))

(defun package-nicknames (package-designator)
  (package-object-nicknames (find-package package-designator)))

(defun package-use-list (package-name)
  (package-object-use-list (find-package package-name)))

(defun find-package (name)
  (typecase name
    (package name)
    (null
     (find-package 'common-lisp))	; This can be practical..
    (string-designator
     (find-package-string (string name)))
    (t (error 'type-error
        :datum name
        :expected-type 'package-designator))))

(defun find-package-string (name &optional (start 0) (end (length name)) (key 'identity))
  (values (gethash-string name start end *packages* nil key)))

(defun assert-package (name)
  (or (find-package name)
      (error "There is no package named ~S." (string name))))

(defun list-all-packages ()
  (let (pkgs)
    (maphash (lambda (k v)
	       (declare (ignore k))
               (pushnew v pkgs))
             *packages*)
    pkgs))

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
	  (setf symbol (%create-symbol name package))
	  (when (eq package (find-package :keyword))
	    (setf (symbol-flags symbol)
	      #.(bt:enum-value 'movitz::movitz-symbol-flags '(:constant-variable)))
	    (setf (%symbol-global-value symbol)
	      symbol))))
      (unless (symbol-package symbol)
	(setf (memref symbol (movitz-type-slot-offset 'movitz-symbol 'package)) package))
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
	(next-symbol (gensym))
	(more-symbols-var (gensym))
	(symbol-var (gensym))
	(loop-tag (gensym))
	(end-tag (gensym)))
    `(with-hash-table-iterator (,next-package *packages*)
       (do () (nil)
	 (multiple-value-bind (,more-packages-var ,dummy ,package-var)
	     (,next-package)
	   (declare (ignore ,dummy))
	   (unless ,more-packages-var
	     (return ,result-form))
	   (let ((,package-hash-var (package-object-external-symbols ,package-var)))
	     (tagbody ,loop-tag
		(with-hash-table-iterator (,next-symbol ,package-hash-var)
		  (tagbody ,loop-tag
		     (multiple-value-bind (,more-symbols-var ,dummy ,symbol-var)
			 (,next-symbol)
		       (declare (ignore ,dummy))
		       (unless ,more-symbols-var (go ,end-tag))
		       (prog ((,var ,symbol-var))
			  ,@declarations-and-body))
		     (go ,loop-tag)
		     ,end-tag))
		(let ((internals (package-object-internal-symbols ,package-var)))
		  (unless (eq ,package-hash-var internals)
		    (setf ,package-hash-var internals)
		    (go ,loop-tag))))))))))

(defmacro do-external-symbols
    ((var &optional (package '*package*) result-form) &body declarations-and-body)
  (let ((next-var (gensym))
	(more-var (gensym))
	(key-var (gensym)))
    `(with-hash-table-iterator (,next-var (package-object-external-symbols (assert-package ,package)))
       (do () (nil)
	 (multiple-value-bind (,more-var ,key-var ,var) (,next-var)
	   (unless ,more-var
	     (return ,result-form))
	   (prog ()
	      ,@declarations-and-body))))))

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
       (declare (index ,state-var))
       (with-hash-table-iterator (,next-var ,hash-table-var)
	 (do () (nil)
	   (multiple-value-bind (,more-var ,key-var ,var) (,next-var)
	     (declare (ignore ,key-var))
	     (if ,more-var
		 (prog ()
		    ,@declarations-and-body)
		 (return))))))))

(defun apropos (string &optional package)
  (flet ((apropos-symbol (symbol string)
	   (when (search string (symbol-name symbol) :test #'char-equal)
	     (cond
	       ((keywordp symbol)
		(format t "~&~W == keyword~%" symbol))
	       ((fboundp symbol)
		(format t "~&~W == function ~:A~%"
			symbol (funobj-lambda-list (symbol-function symbol))))
	       ((boundp symbol)
		(format t "~&~W == variable ~S~%"
			symbol (symbol-value symbol)))
	       (t (format t "~&~W~%" symbol))))))
    (let ((string (string string)))
      (if package
	  (do-symbols (symbol package)
	    (apropos-symbol symbol string))
	  (do-all-symbols (symbol)
	    (apropos-symbol symbol string)))))
  (values))

(defun package-used-by-list (package)
  "Return a list of all packages that use package."
  (let ((package (find-package package)))
    (let ((used-by-list nil))
      (maphash (lambda (name other-package)
		 (declare (ignore name))
		 (when (member package
			       (package-object-use-list other-package)
			       :test #'eq)
		   (pushnew other-package used-by-list)))
	       *packages*)
      used-by-list)))

(defun list-all-packages ()
  (with-hash-table-iterator (p *packages*)
    (do (packages) (nil)
      (multiple-value-bind (more k v)
	  (p)
	(declare (ignore k))
	(when (not more)
	  (return packages))
	(push v packages)))))


(defmacro with-package-iterator ((name package-list-form &rest symbol-types) &body body)
  `(macrolet ((,name ()
		'(warn "with-package-iterator not implemented."
		  (values nil nil nil nil))))
     ,@body))
