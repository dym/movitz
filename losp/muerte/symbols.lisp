;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      symbols.lisp
;;;; Description:   Symbol accessors.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep  4 23:55:41 2001
;;;;                
;;;; $Id: symbols.lisp,v 1.2 2004/01/19 11:23:47 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(require :muerte/basic-macros)
(require :muerte/typep)
(provide :muerte/symbols)

(in-package muerte)

(defun symbol-value (symbol)
  "Returns the dynamic value of SYMBOL."
  (etypecase symbol
    (null nil)
    (symbol
     (with-inline-assembly (:returns :eax)
       (:compile-form (:result-mode :eax) symbol)
       (:call-global-constant dynamic-load)))))

(defun (setf symbol-value) (value symbol)
  (etypecase symbol
    (null
     (error "Can't change the value of NIL."))
    (symbol
     (with-inline-assembly (:returns :ebx)
       (:compile-form (:result-mode :eax) symbol)
       (:compile-form (:result-mode :ebx) value)
       (:call-global-constant dynamic-store)))))

(defun set (symbol value)
  (setf (symbol-value symbol) value))

(defun symbol-global-value (symbol)
  (if symbol
      (let ((x (movitz-accessor symbol movitz-symbol value)))
	(if (eq x (load-global-constant unbound-value))
	    (error 'unbound-value :name symbol)
	  x))
    nil))

(defun symbol-function (symbol)
  (let ((function-value
	 (etypecase symbol
	   (null
	    (movitz-accessor symbol movitz-nil-symbol function-value))
	   (symbol
	    (movitz-accessor symbol movitz-symbol function-value)))))
    (when (eq function-value (load-global-constant movitz::unbound-function))
      (error 'undefined-function :name symbol))
    function-value))

(defun (setf symbol-function) (value symbol)
  (check-type symbol symbol)
  (check-type value compiled-function)
  (setf-movitz-accessor (symbol movitz-symbol function-value) value))

(defun symbol-name (symbol)
  (etypecase symbol
    (null
     (movitz-accessor symbol movitz-nil-symbol name))
    (symbol 
     (movitz-accessor symbol movitz-symbol name))))

(defun (setf symbol-name) (value symbol)
  (check-type value string)
  (etypecase symbol
    (null
     (error "Can't change the name of NIL."))
    (symbol
     (setf-movitz-accessor (symbol movitz-symbol name) value))))

(defun symbol-plist (symbol)
  (etypecase symbol
    (null
     (movitz-accessor symbol movitz-nil-symbol plist))
    (symbol 
     (movitz-accessor symbol movitz-symbol plist))))

(defun (setf symbol-plist) (value symbol)
  (etypecase symbol
    (null
     (error "Can't change the plist of NIL."))
    (symbol
     (setf-movitz-accessor (symbol movitz-symbol plist) value))))

(defun symbol-package (symbol)
  (etypecase symbol
    (null
     (movitz-accessor symbol movitz-nil-symbol package))
    (symbol
     (movitz-accessor symbol movitz-symbol package))))

(defun boundp (symbol)
  (etypecase symbol
    (null nil)
    (symbol
     (not (eq (movitz-accessor symbol movitz-symbol value) 'unbound)))))

(defun makunbound (symbol)
  (setf (symbol-value symbol)
    'unbound))

(defun fboundp (symbol)
  (etypecase symbol
    (null nil)
    (symbol
     (not (eq (movitz-accessor symbol movitz-symbol function-value)
	      (load-global-constant movitz::unbound-function))))))

(defun make-symbol (name)
  (let ((symbol (inline-malloc #.(bt:sizeof 'movitz::movitz-symbol) :tag :symbol)))
    (setf-movitz-accessor (symbol movitz-symbol package) nil)
    (setf-movitz-accessor (symbol movitz-symbol hash-key) (sxhash name))
    (setf (symbol-flags symbol) 0
	  (symbol-function symbol) (load-global-constant movitz::unbound-function)
	  (symbol-name symbol) name
	  (symbol-value symbol) (load-global-constant unbound-value))
    symbol))

(defun symbol-flags (symbol)
  (etypecase symbol
    (null #.(bt:enum-value 'movitz::movitz-symbol-flags '(:constant-variable)))
    (symbol
     (with-inline-assembly (:returns :untagged-fixnum-eax)
       (:compile-form (:result-mode :eax) symbol)
       (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-symbol 'movitz::flags)) :eax)))))

(defun (setf symbol-flags) (flags symbol)
  (etypecase symbol
    (null (error "Can't set NIL's flags."))
    (symbol
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) symbol)
       (:compile-form (:result-mode :untagged-fixnum-eax) flags)
       (:movw :ax (:ebx #.(bt:slot-offset 'movitz::movitz-symbol 'movitz::flags))))
     flags)))

(defun symbol-special-variable-p (symbol)
  (logbitp 0 (symbol-flags symbol)))

(defun symbol-constant-variable-p (symbol)
  (logbitp 1 (symbol-flags symbol)))

(defvar *gensym-counter* 0)

(defun gensym (&optional (x "G"))
  (etypecase x
    (integer
     (make-symbol (format nil "G~D" x)))
    (string
     (make-symbol (format nil "~A~D" x (prog1 *gensym-counter*
					 (incf *gensym-counter*)))))))

(defun get (symbol indicator &optional default)
  (getf (symbol-plist symbol) indicator default))

(defun (setf get) (value symbol indicator &optional default)
  (declare (ignore default))
  (setf (getf (symbol-plist symbol) indicator)
    value))
