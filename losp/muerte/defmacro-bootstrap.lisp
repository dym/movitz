;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Filename:      defmacro-bootstrap.lisp
;;;; Author:        Frode Vatvedt Fjeld
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: defmacro-bootstrap.lisp,v 1.5 2008-04-27 19:37:08 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/defmacro-bootstrap)

(muerte::defmacro/compile-time muerte.cl:defmacro (name lambda-list &body macro-body)
  (`(muerte::defmacro/compile-time ,name ,lambda-list ,macro-body)))

(muerte.cl:defmacro muerte.cl:in-package (name)
  (let ((movitz-package-name (movitz::movitzify-package-name name)))
    `(progn
       (eval-when (:compile-toplevel)
	 (in-package ,movitz-package-name))
       (eval-when (:execute)
	 (set '*package* (find-package ',movitz-package-name))))))

(in-package #:muerte)

(defmacro defmacro/cross-compilation (name lambda-list &body body)
  `(progn
     (defmacro/compile-time ,name ,lambda-list ,body)
     ',name))

(defmacro defmacro (name lambda-list &body body)
  `(defmacro/cross-compilation ,name ,lambda-list ,@body))

(defmacro defmacro/run-time (name lambda-list &body body)
  (multiple-value-bind (real-body declarations docstring)
      (parse-docstring-declarations-and-body body 'cl:declare)
    (multiple-value-bind (destructuring-lambda-list whole-var env-var ignore-env ignore-operator)
        (parse-macro-lambda-list lambda-list)
      (let* ((block-name (compute-function-block-name name))
             (extras (gensym "extras-"))
             (form-var (or whole-var
                           (gensym "form-"))))
        (cond
          ((and (eq whole-var form-var)
                (null (cdr destructuring-lambda-list)))
           `(make-named-function ,name
                                 (&edx edx &optional ,form-var ,env-var &rest ,extras)
                                 ((ignore ,@ignore-env))
                                 ,docstring
                                 (block ,block-name
                                   (numargs-case
                                    (2 (&edx edx &optional ,form-var ,env-var)
				       (declare (ignore ,@ignore-env))
                                       (verify-macroexpand-call edx ',name)
                                       (let ()
                                         (declare ,@declarations)
                                         ,@real-body))
                                    (t (&edx edx &optional ,form-var ,env-var &rest ,extras)
                                       (declare (ignore ,form-var ,extras ,@ignore-env))
                                       (verify-macroexpand-call edx ',name t))))
                                 :type :macro-function))
          (t `(make-named-function ,name
                                   (&edx edx &optional ,form-var ,env-var &rest ,extras)
                                   ((ignore ,@ignore-env ,extras))
                                   ,docstring
                                   (block ,block-name
                                     (numargs-case
                                      (2 (&edx edx ,form-var ,env-var)
					 (declare (ignore ,@ignore-env))
                                         (verify-macroexpand-call edx ',name)
                                         (destructuring-bind ,destructuring-lambda-list
                                             ,form-var
                                           (declare (ignore ,@ignore-operator) ,@declarations)
                                           ,@real-body))
                                      (t (&edx edx &optional ,form-var ,env-var &rest ,extras)
                                         (declare (ignore ,form-var ,extras ,@ignore-env))
                                         (verify-macroexpand-call edx ',name t))))
                                   :type :macro-function)))))))
