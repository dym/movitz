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
;;;; $Id: symbols.lisp,v 1.20 2004/10/11 13:53:28 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(require :muerte/basic-macros)
(require :muerte/typep)
(provide :muerte/symbols)

(in-package muerte)

(define-compiler-macro get-symbol-slot (object slot &optional (type t))
  "Read a slot off a symbol (including NIL)."
  `(with-inline-assembly (:returns :eax :type ,type)
     (:compile-form (:result-mode :eax) ,object)
     (:leal (:eax ,(- (movitz:tag :null))) :ecx)
     (:andl 7 :ecx)
     (:testb 5 :cl)
     (:jnz '(:sub-program (not-a-symbol)
	     (:compile-form (:result-mode :ignore)
	      (error-not-symbol (assembly-register :eax)))))
     (:xorl 2 :ecx)
     (:movl (:eax :ecx (:offset movitz-symbol ,slot))
	    :eax)))

(defun error-not-symbol (x)
  (error 'type-error :expected-type 'symbol :datum x))

(defun symbol-value (symbol)
  "Returns the dynamic value of SYMBOL."
  (etypecase symbol
    (null nil)
    (symbol
     (with-inline-assembly (:returns :eax)
       (:compile-form (:result-mode :eax) symbol)
       (:call-local-pf dynamic-load)))))

(defun %unbounded-symbol-value (symbol)
  "Return the symbol's value without checking if it's bound or not."
  (check-type symbol symbol)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) symbol)
    (:call-local-pf dynamic-find-binding)
    (:jnc 'no-local-binding)
    (:movl (:eax) :eax)
    (:jmp 'done)
   no-local-binding
    (:movl (:eax (:offset movitz-symbol value)) :eax)
   done))

(defun (setf symbol-value) (value symbol)
  (etypecase symbol
    (null
     (error "Can't change the value of NIL."))
    (symbol
     (with-inline-assembly (:returns :ebx)
       (:compile-form (:result-mode :eax) symbol)
       (:compile-form (:result-mode :ebx) value)
       (:call-local-pf dynamic-store)))))

(defun set (symbol value)
  (setf (symbol-value symbol) value))

(define-compiler-macro %symbol-global-value (symbol)
  `(memref ,symbol ,(bt:slot-offset 'movitz:movitz-symbol 'movitz::value)))

(defun %symbol-global-value (symbol)
  (%symbol-global-value symbol))

(define-compiler-macro (setf %symbol-global-value) (value symbol)
  `(setf (memref ,symbol ,(bt:slot-offset 'movitz:movitz-symbol 'movitz::value))
     ,value))

(defun (setf %symbol-global-value) (value symbol)
  (setf (%symbol-global-value symbol) value))

(defun symbol-function (symbol)
  (let ((function-value (get-symbol-slot symbol function-value)))
    (when (eq function-value (load-global-constant movitz::unbound-function))
      (error 'undefined-function :name symbol))
    function-value))

(defun %unbounded-symbol-function (symbol)
  (check-type symbol symbol)
  (memref symbol (movitz-type-slot-offset 'movitz-symbol 'function-value)))
  ;; (movitz-accessor symbol movitz-symbol function-value))

(defun (setf symbol-function) (value symbol)
  (check-type symbol symbol)
  (check-type value compiled-function)
  (setf-movitz-accessor (symbol movitz-symbol function-value) value))

(defun symbol-name (symbol)
  (get-symbol-slot symbol name string))

(defun (setf symbol-name) (value symbol)
  (etypecase symbol
    (null
     (error "Can't change the name of NIL."))
    (symbol
     (setf (memref symbol (movitz-type-slot-offset 'movitz-symbol 'name))
       value))))

(defun symbol-plist (symbol)
  (get-symbol-slot symbol plist))

(defun (setf symbol-plist) (value symbol)
  (etypecase symbol
    (null
     (error "Can't change the plist of NIL."))
    (symbol
     (setf (memref symbol (movitz-type-slot-offset 'movitz-symbol 'plist))
       value))))

(defun symbol-package (symbol)
  (get-symbol-slot symbol package))

(defun boundp (symbol)
  (boundp symbol))

(defun makunbound (symbol)
  (setf (symbol-value symbol)
    (load-global-constant unbound-value))
  symbol)

(defun fboundp (symbol)
  (not (eq (get-symbol-slot symbol function-value)
	   (load-global-constant movitz::unbound-function))))

(defun %create-symbol (name &optional (package nil)
				      (plist nil)
				      (value (load-global-constant unbound-value))
				      (function (load-global-constant movitz::unbound-function))
				      (flags 0))
  (eval-when (:compile-toplevel)
    (assert (= 1 (- (movitz:tag :symbol) (movitz:tag :other)))))
  (let ((sxhash (sxhash name)))
    (macrolet
	((do-it ()
	   `(with-non-pointer-allocation-assembly (6 :fixed-size-p t
						     :object-register :eax)
	      (:addl ,(- (movitz:tag :symbol) (movitz:tag :other)) :eax)
	      (:load-lexical (:lexical-binding package) :ebx)
	      (:movl :ebx (:eax (:offset movitz-symbol package)))
	      (:load-lexical (:lexical-binding name) :ebx)
	      (:movl :ebx (:eax (:offset movitz-symbol name)))
	      (:load-lexical (:lexical-binding function) :ebx)
	      (:movl :ebx (:eax (:offset movitz-symbol function-value)))
	      (:load-lexical (:lexical-binding plist) :ebx)
	      (:movl :ebx (:eax (:offset movitz-symbol plist)))
	      (:load-lexical (:lexical-binding value) :ebx)
	      (:movl :ebx (:eax (:offset movitz-symbol value)))

	      (:load-lexical (:lexical-binding flags) :ecx)
	      (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
	      (:load-lexical (:lexical-binding sxhash) :ebx)
	      (:shll ,(- 16 movitz:+movitz-fixnum-shift+) :ebx)
	      (:orl :ebx :ecx)
	      (:movl :ecx (:eax (:offset movitz-symbol flags)))
	      )))
      (do-it))))

(defun make-symbol (name)
  (check-type name string "a symbol name")
  (%create-symbol name))

(defun copy-symbol (symbol &optional copy-properties) 
  "copy-symbol returns a fresh, uninterned symbol, the name of which
  is string= to and possibly the same as the name of the given
  symbol."
  (if (or (eq nil symbol)
	  (not copy-properties))
      (%create-symbol (symbol-name symbol))
    (with-allocation-assembly (6 :object-register :eax
				 :fixed-size-p t)
      (:addl 1 :eax)
      (:load-lexical (:lexical-binding symbol) :ebx)
      ;; 0
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 0) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 0))
      ;; 1
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 4) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 4))
      ;; 2
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 8) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 8))
      ;; 3
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 12) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 12))
      ;; 4
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 16) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 16))
      ;; 5
      (:movl (:ebx #.(cl:- (movitz:tag :symbol)) 20) :ecx)
      (:movl :ecx (:eax #.(cl:- (movitz:tag :symbol)) 20)))))


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
  (logbitp 3 (symbol-flags symbol)))

(defun (setf symbol-special-variable-p) (value symbol)
  (setf (ldb (byte 1 3) (symbol-flags symbol))
    (if value 1 0))
  value)

(defun symbol-constant-variable-p (symbol)
  (logbitp 4 (symbol-flags symbol)))

(defun (setf symbol-constant-variable-p) (value symbol)
  (setf (ldb (byte 1 4) (symbol-flags symbol))
    (if value 1 0))
  value)

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
