;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      named-integers.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Jan  4 16:13:46 2002
;;;;                
;;;; $Id: named-integers.lisp,v 1.6 2004/12/10 12:47:22 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(require :lib/malloc-init)
(provide :lib/named-integers)

(in-package muerte.lib)

(eval-when (:compile-toplevel :load-toplevel)
  (defun name->integer (map name)
    (if (integerp name)
	name
      (or (ecase (car map)
	    (:enum (position name (cdr map)))
	    (:assoc (cdr (assoc name (cdr map))))
	    (:rassoc (car (rassoc name (cdr map)))))
	  (error "No integer named ~S in ~S." name map))))
  (defun names->integer (map &rest names)
    (declare (dynamic-extent names))
    (loop for name in names
	sum (name->integer map name))))

(defmacro with-named-integers-syntax (name-maps &body body)
  `(macrolet
       ,(mapcar (lambda (name-map)
		  (destructuring-bind (name map)
		      name-map
		    `(,name (&rest names)
			    (apply 'muerte.lib:names->integer ,map names))))
		name-maps)
     ,@body))       

(define-compile-time-variable *name-to-integer-tables*
    (make-hash-table :test 'eq))

(define-compile-time-variable *integer-to-name-tables*
    (make-hash-table :test 'eql))

(defmacro define-named-integer (type-name (&key only-constants (prefix-constants t) export-constants)
				&rest integer-names)
  (loop
      with name-to-int-variable = 
	(intern (format nil "*~A-~A*" type-name 'name-to-integer))
      with int-to-name-variable = 
	(intern (format nil "*~A-~A*" type-name 'integer-to-name))
      for (integer name) in integer-names
      as constant-name = (intern (if prefix-constants
				     (format nil "+~A-~A+"
					     (symbol-name type-name) 
					     (symbol-name name))
				   (format nil "+~A+" (symbol-name name))))
      collect
	`(defconstant ,constant-name ,integer) into constant-declarations
      when export-constants
      collect constant-name into constant-exports
      unless only-constants
      collect integer into integer-list
      and collect name into name-list
      finally
	(return
	  `(progn
	     ,@(unless only-constants
		 `((define-compile-time-variable ,name-to-int-variable (make-hash-table :test 'eq))
		   (define-compile-time-variable ,int-to-name-variable (make-hash-table :test 'eql))
		   (eval-when (:compile-toplevel)
		     (setf (gethash ',type-name *name-to-integer-tables*) ,name-to-int-variable
			   (gethash ',type-name *integer-to-name-tables*) ,int-to-name-variable)
		     (mapcar (lambda (i n)
			       (setf (gethash i ,int-to-name-variable) n)
			       (setf (gethash n ,name-to-int-variable) i))
			     ',integer-list
			     ',name-list))))
	     (eval-when (:compile-toplevel)
;;;	       ,@constant-declarations
	       (export ',constant-exports))
	     ,@constant-declarations
	     ',type-name))))

(defmacro named-integer-case (type keyform &rest cases)
  (let ((table (gethash type *name-to-integer-tables*)))
    (assert table (type) "No such named-integer type: ~S." type)
    (flet ((map-name (name)
	     (or (and (integerp name) name)
		 (gethash name table)
		 name)))
      (list* 'case keyform
	     (loop for (keys . forms) in cases
		 if (atom keys)
		 collect (cons (map-name keys) forms)
		 else collect (cons (mapcar #'map-name keys) forms))))))

(defun integer-name (type integer &optional (errorp t) (default integer))
  (let ((table (gethash type *integer-to-name-tables*)))
    (assert table (type)
      "No such named-integer type: ~S." type)
    (or (gethash integer table)
	(if errorp
	    (error "Integer ~S has no name in type ~S." integer type)
	  default))))

(defun named-integer (type name &optional (errorp t) (default name))
  (let ((table (gethash type *name-to-integer-tables*)))
    (assert table (type)
      "No such named-integer type: ~S." type)
    (or (gethash name table)
	(if errorp
	    (error "~S is not defined in named-integer type ~S." name type)
	  default))))

