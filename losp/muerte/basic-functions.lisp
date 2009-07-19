;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      basic-functions.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep  4 18:41:57 2001
;;;;                
;;;; $Id: basic-functions.lisp,v 1.28 2009-07-19 18:32:34 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/setf)
(require :muerte/typep)
(provide :muerte/basic-functions)

(in-package muerte)

(defun eq (x y)
  "Return TRUE iff X and Y are the same."
  (eq x y))

(defun not (x)
  (not x))

(defun find-catch-tag (catch-tag)
  "Find the dynamic-env slot that matches the catch-tag, or 0 if unseen."
  (with-inline-assembly (:returns :eax)
    (:load-lexical (:lexical-binding catch-tag) :eax)
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    (:jecxz 'search-done)
   search-loop
    (:cmpl :eax (:ecx 4))		; Does tag match entry?
    (:jne 'search-next)			; if not, goto next.
    (:testl 3 (:ecx))			; Is this really a catch entry?
    (:jz 'search-done)			; if yes, we have found it.
   search-next
    (:movl (:ecx 12) :ecx)
    (:testl :ecx :ecx)
    (:jnz 'search-loop)
    ;; Search failed, ECX=0
   search-done
    (:movl :ecx :eax)))
    

(defun d-bind-veryfy-keys (args keys)
  (do ((allow-allow-p t)
       (mismatches nil))
      ((null args)
       (when mismatches
	 (error "Unexpected destructuring keys ~{~S~^, ~}, expected ~{~S~^, ~}."
		mismatches keys)))
    (let ((a (pop args))
	  (v (pop args)))
      (cond
	((eq a :allow-other-keys)
	 (when (and v allow-allow-p)
	   (return))
	 (setf allow-allow-p nil))
	((not (member a keys))
	 (pushnew a mismatches))))))

(defun d-bind-lookup-key (key list)
  (do ()
      ((endp list)
       nil)
    (unless (cdr list)
      (error "Odd number of keyword arguments."))
    (when (eq key (pop list))
      (return list))
    (setf list (cdr list))))

(defun verify-macroexpand-call (key name &optional extras-p)
  "Used by macro-expander functions to separate bona fide macro-expansions
from regular function-calls."
  (when (eq key name)
    (error 'undefined-function-call
	   :name name
	   :arguments :unknown))
  (when extras-p
    (error 'wrong-argument-count
     :function (symbol-function name)
     :argument-count nil)))

(defun call-macroexpander (form env expander)
  "Call a macro-expander for a bona fide macro-expansion."
  (with-inline-assembly (:returns :multiple-values)
    (:compile-form (:result-mode :edx) 'verify-macroexpand-call)
    (:load-lexical (:lexical-binding expander) :esi)
    (:load-lexical (:lexical-binding form) :eax)
    (:load-lexical (:lexical-binding env) :ebx)
    (:call (:esi (:offset movitz-funobj code-vector%2op)))))

(defun funcall%0ops (function)
  (with-inline-assembly (:returns :multiple-values)
    (:compile-form (:result-mode :esi) (etypecase function
					 (symbol (symbol-function function))
					 (compiled-function function)))
    (:compile-form (:result-mode :edx) function)
    (:xorl :ecx :ecx)
    (:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))))

(defun funcall (function-or-name &rest args)
  (numargs-case
   (1 (function-or-name)
      (with-inline-assembly (:returns :multiple-values)
	(:compile-form (:result-mode :esi) (etypecase function-or-name
					     (symbol (symbol-function function-or-name))
					     (compiled-function function-or-name)))
	(:compile-form (:result-mode :edx) function-or-name)
	(:xorl :ecx :ecx)
	(:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))))
   (2 (function-or-name arg0)
      (funcall%1ops function-or-name arg0))
   (3 (function-or-name arg0 arg1)
      (funcall%2ops function-or-name arg0 arg1))
   (t (function-or-name &rest args)
      (declare (dynamic-extent args))
      (let ((function (typecase function-or-name
			(symbol (symbol-function function-or-name))
			(compiled-function function-or-name)
			(t (error "Not a function: ~S" function-or-name))))
	    (x args))
	(macrolet ((next (x) `(setf ,x (cdr ,x))))
	  (with-inline-assembly (:returns :nothing)
	    (:compile-form (:result-mode :edx) function-or-name))
	  (cond
	   ((not x)			; 0 args
	    (with-inline-assembly (:returns :multiple-values)
	      (:compile-form (:result-mode :esi) function)
	      (:xorl :ecx :ecx)
	      (:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))))
	   ((not (next x))		; 1 args
	    (with-inline-assembly (:returns :multiple-values)
	      (:compile-form (:result-mode :eax) args)
	      (:movl (:eax -1) :eax)	; arg0
	      (:compile-form (:result-mode :esi) function)
	      (:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))))
	   ((not (next x))		; 2 args
	    (with-inline-assembly (:returns :multiple-values)
	      (:compile-form (:result-mode :ebx) args)
	      (:movl (:ebx -1) :eax)	; arg0
	      (:movl (:ebx 3) :ebx)	; ebx = (cdr ebx)
	      (:movl (:ebx -1) :ebx)	; ebx = (car ebx) = arg1
	      (:compile-form (:result-mode :esi) function)
	      (:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op)))))
	   ((not (next x))		; 3 args
	    (with-inline-assembly (:returns :multiple-values)
	      (:compile-form (:result-mode :edx) args)
	      (:movl (:edx -1) :eax)	; arg0
	      (:movl (:edx 3) :edx)	; edx = (cdr ebx)
	      (:movl (:edx -1) :ebx)	; edx = (car ebx) = arg1
	      (:movl (:edx 3) :edx)	; edx = (cdr ebx)
	      (:pushl (:edx -1))	; arg2
	      (:compile-form (:result-mode :edx) function-or-name)
	      (:compile-form (:result-mode :esi) function)
	      (:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op)))))
	   (t (with-inline-assembly (:returns :multiple-values)
		(:compile-form (:result-mode :eax) args)
		(:movl (:eax 3) :eax)	; eax = (cdr eax)
		(:movl (:eax 3) :eax)	; eax = (cdr eax)

		(:xorl :ecx :ecx)
		(:movb 2 :cl)

	       copy-args-loop
		(:incl :ecx)
		(:pushl (:eax -1))	; (push (car eax))
		(:movl (:eax 3) :eax)	; eax = (cdr eax)
		(:leal (:eax 7) :ebx)	; test for nil
		(:testb 7 :bl)
		(:je 'copy-args-loop)	; while (consp eax)

		(:movl :edi :ebx)
		(:compile-form (:result-mode :ebx) args)
		(:movl (:ebx -1) :eax)	; eax = (first args)
		(:movl (:ebx 3) :ebx)
		(:movl (:ebx -1) :ebx)	; ebx = (second args)

		(:cmpl #x7f :ecx)
		(:ja '(:sub-program (normalize-ecx)
		       (:shll 8 :ecx)
		       (:movb #xff :cl)
		       (:jmp 'ecx-ok)))
	       ecx-ok
		(:compile-form (:result-mode :esi) function)
		(:call (:esi #.(movitz::slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))))))))))

(defun apply (function &rest args)
  (numargs-case
   (2 (function args)
      (with-inline-assembly-case ()
	(do-case (t :multiple-values :labels (ecx-ok))
	  (:compile-two-forms (:eax :ebx) function args)
	  ;; Load (function function) into :esi
	  (:leal (:eax -7) :ecx)
	  (:andb 7 :cl)
	  (:jne 'not-symbol)
	  (:movl (:eax #.(bt:slot-offset 'movitz::movitz-symbol 'movitz::function-value))
		 :esi)
	  (:jmp 'esi-ok)
	 not-symbol
	  (:cmpb 7 :cl)
	  (:jne '(:sub-program (not-a-funobj)
		  (:compile-form (:result-mode :ignore)
		   (error "Can't apply non-function ~W." function))))
	  (:cmpb #.(movitz::tag :funobj)
		 (:eax #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::type)))
	  (:jne 'not-a-funobj)
	  (:movl :eax :esi)
	 esi-ok
	  (:leal (:ebx #.(cl:- (movitz::image-nil-word movitz::*image*))) :ecx)
	  (:jecxz 'zero-args)
	  (:testb 3 :cl)
	  (:jz 'more-than-zero-args)
	 zero-args
	  (:xorl :ecx :ecx)
	  (:compile-form (:result-mode :edx) function)
	  (:call (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))
	  (:jmp 'apply-done)
	 more-than-zero-args
	  (:movl (:ebx -1) :eax)
	  (:movl (:ebx 3) :ebx)
	  (:leal (:ebx #.(cl:- (movitz::image-nil-word movitz::*image*))) :ecx)
	  (:jecxz 'one-args)
	  (:testb 3 :cl)
	  (:jz 'more-than-one-args)
	 one-args
	  (:compile-form (:result-mode :edx) function)
	  (:call (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op)))
	  (:jmp 'apply-done)
	 more-than-one-args
	  (:movl (:ebx -1) :edx)
	  (:xchgl :ebx :edx)
	  (:movl (:edx 3) :edx)
	  (:leal (:edx #.(cl:- (movitz::image-nil-word movitz::*image*))) :ecx)
	  (:jecxz 'two-args)
	  (:testb 3 :cl)
	  (:jz 'more-than-two-args)
	 two-args
	  (:compile-form (:result-mode :edx) function)
	  (:call (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op)))
	  (:jmp 'apply-done)
	 more-than-two-args
	  (:pushl (:edx -1))
	  (:movl (:edx 3) :edx)
	  (:leal (:edx #.(cl:- (movitz::image-nil-word movitz::*image*))) :ecx)
	  (:jecxz 'three-args)
	  (:testb 3 :cl)
	  (:jz 'more-than-three-args)
	 three-args
	  (:compile-form (:result-mode :edx) function)
	  (:call (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op)))
	  (:jmp 'apply-done)
	 more-than-three-args
	  (:pushl (:edx -1))
	  (:movl (:edx 3) :edx)
	  (:leal (:edx #.(cl:- (movitz::image-nil-word movitz::*image*))) :ecx)
	  (:jecxz 'no-more-args)
	  (:testb 3 :cl)
	  (:jz 'more-than-three-args)
	 no-more-args
	  ;; Calculate numargs from (esp-ebp)..
	  (:leal (:ebp -8 8) :ecx)	; debugger also "knows" this offset..
	  (:subl :esp :ecx)
	  (:shrl 2 :ecx)
	  ;; Encode ECX
          (:testl #xffffff80 :ecx)
	  (:jz 'ecx-ok)
	  (:shll 8 :ecx)
	  (:movb #xff :cl)
	 ecx-ok
	  (:compile-form (:result-mode :edx) function)
	  (:call (:esi #.(bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector)))
	 apply-done
	  ;; Don't need to restore ESP because we'll be exiting this stack-frame
	  ;; now anyway.
	  )))
   (3 (function &rest args)
      (declare (dynamic-extent args))
      ;; spread out args, which we know is length 2.
      (setf (cdr args) (cadr args))
      (apply function args))
   (t (function &rest args)
      (declare (dynamic-extent args))
      ;; spread out args.
      (cond
       ((null args)
	(error 'program-error
	       :format-control "Too few arguments to APPLY."))
       ((null (cdr args))
	(apply function (car args)))
       (t (let* ((second-last-cons (last args 2))
		 (tail (cadr second-last-cons)))
	    (check-type tail list)
	    (setf (cdr second-last-cons) tail)
	    (apply function args)))))))

(defun values (&rest objects)
  (numargs-case
   (1 (x)
      (with-inline-assembly (:returns :multiple-values)
	(:compile-form (:result-mode :eax) x)
	(:clc)))
   (2 (x y)
      (with-inline-assembly (:returns :multiple-values)
	(:compile-two-forms (:eax :ebx) x y)
	(:movl 2 :ecx)
	(:stc)))
   (3 (x y z)
      (with-inline-assembly (:returns :multiple-values)
	(:compile-two-forms (:eax :ebx) x y)
	((:fs-override) :movl #.movitz:+movitz-fixnum-factor+
			(:edi #.(movitz::global-constant-offset 'num-values)))
	(:compile-form (:result-mode :edx) z)
	((:fs-override) :movl :edx (:edi #.(movitz::global-constant-offset 'values)))
	(:movl 3 :ecx)
	(:stc)))
   (t (&rest objects)
      (declare (without-function-prelude)
	       (ignore objects))
      (with-inline-assembly (:returns :multiple-values)
	(:cmpb #.movitz::+movitz-multiple-values-limit+ :cl)
	(:ja '(:sub-program (too-many-values)
	       (:compile-form (:result-mode :ignore)
		(error "Too many values: #x~X."
		 (with-inline-assembly (:returns :eax)
		   (:leal ((:ecx #.movitz::+movitz-fixnum-factor+)) :eax))))))
	(:andl #x7f :ecx)
	(:jz 'done)
	(:subl 2 :ecx)
	(:jc 'copy-done)
	(:leal ((:ecx #.movitz::+movitz-fixnum-factor+)) :edx)
	((:fs-override) :movl :edx (:edi #.(movitz::global-constant-offset 'num-values)))
	(:pushl :eax)
	(:xorl :eax :eax)
       copy-loop
	(:movl (:ebp (:ecx 4) 4) :edx)
	((:fs-override) :movl :edx (:edi (:eax 1) #.(movitz::global-constant-offset 'values)))
	(:addl 4 :eax)
	(:subl 1 :ecx)
	(:jnc 'copy-loop)
	(:leal (:eax #.(cl:- movitz:+movitz-fixnum-factor+)) :ecx)
	(:popl :eax)
	(:shrl #.movitz:+movitz-fixnum-shift+ :ecx)
       copy-done
	(:addl 2 :ecx)
	(:jnz 'done)
	(:movl :edi :eax)
       done
	(:stc)))))

(defun values-list (list)
  (apply #'values list))

(defun ensure-funcallable (x)
  (typecase x
    (symbol
     (symbol-function x))
    (compiled-function
     x)
    (t (error "Not a function: ~S" x))))

(define-compiler-macro object-location (object)
  "The location is the object's address divided by fixnum-factor."
  `(with-inline-assembly (:returns :register :type fixnum)
     (:compile-form (:result-mode :register) ,object)
     (:andl ,(* -2 movitz::+movitz-fixnum-factor+) (:result-register))))
  
(defun object-location (object)
  "The location is the object's address divided by fixnum-factor."
  (object-location object))

(define-compiler-macro object-tag (object)
  `(with-inline-assembly (:returns :register :type (integer 0 7))
     (:compile-form (:result-mode :register) ,object)
     (:leal (((:result-register) ,movitz::+movitz-fixnum-factor+))
	    (:result-register))
     (:andl ,(* 7 movitz::+movitz-fixnum-factor+) (:result-register))))

(defun object-tag (object)
  (object-tag object))


(define-compiler-macro location-physical-offset ()
  '(memref nil (movitz-type-slot-offset 'movitz-run-time-context
		'physical-address-offset)
    :type :lisp))

(defun location-physical-offset ()
  "The offset between physical and logical locations.
A location is an 4-aligned address (32 bits whose two lsb are zero)
interpreted as a lispval, and consequently a fixnum."
  (location-physical-offset))

(defun halt-cpu ()
  (halt-cpu))

(define-compiler-macro %word-offset (&environment env word offset)
  (if (movitz:movitz-constantp offset env)
      `(with-inline-assembly (:returns :eax)
	 (:compile-form (:result-mode :eax) ,word)
	 (:addl ,(movitz:movitz-eval offset env) :eax))
    `(with-inline-assembly (:returns :eax)
       (:compile-two-forms (:eax :ecx) ,word ,offset)
       (:sarl ,movitz::+movitz-fixnum-shift+ :ecx)
       (:addl :ecx :eax))))

(defun %word-offset (word offset)
  (%word-offset word offset))

(defun check-type-failed (value type &optional place-name type-description)
  (cond
   ((and place-name type-description)
    (error "The value of ~S, ~S, is not ~A."
	   place-name value type-description))
   (place-name
    (error "The value of ~S, ~S, is not of type ~S."
	   place-name value type))
   (t (error "~S is not of type ~S." value type))))

(defun memrange (object offset index length type)
  (ecase type
    (:unsigned-byte8
     (let ((vector (make-array length :element-type '(unsigned-byte 8))))
       (let ((i (check-the index index)))
	 (declare (index i))
	 (dotimes (j (check-the index length))
	   (declare (index j))
	   (setf (aref vector j)
	     (memref object offset :index i :type :unsigned-byte8))
	   (incf i)))
       vector))))

(defun (setf memrange) (value object offset index length type)
  (let* ((index (check-the index index))
	 (end (check-the index (+ index length))))	
    (ecase type
      (:unsigned-byte8
       (etypecase value
	 ((unsigned-byte 8)
	  (do ((i index (1+ i)))
	      ((>= i end))
	    (declare (index i))
	    (setf (memref object offset :index i :type :unsigned-byte8) value)))
	 (vector
	  (do ((i index (1+ i))
	       (j 0 (1+ j)))
	      ((or (>= i end) (>= j (length value))))
	    (declare (index i j))
	    (setf (memref object offset :index i :type :unsigned-byte8)
	      (aref value j))))))
      (:character
       (etypecase value
	 (character
	  (do ((i index (1+ i)))
	      ((>= i end))
	    (declare (index i))
	    (setf (memref object offset :index i :type :character) value)))
	 (string
	  (do ((i index (1+ i))
	       (j 0 (1+ j)))
	      ((or (>= i end) (>= j (length value))))
	    (declare (index i j))
	    (setf (memref object offset :index i :type :character)
	      (char value j))))))))
  value)

(defun xor (a b)
  "Iff b is true, complement a."
  (if b (not a) a))

(define-compiler-macro xor (a b)
  `(let ((a ,a))
     (if ,b (not a) a)))
