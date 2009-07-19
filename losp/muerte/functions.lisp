;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      functions.lisp
;;;; Description:   Misc. function-oriented functions
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Mar 12 22:58:54 2002
;;;;                
;;;; $Id: functions.lisp,v 1.32 2009-07-19 18:58:33 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/setf)
(provide :muerte/functions)

(in-package muerte)

(defvar *setf-namespace* nil
  "This hash-table is initialized by dump-image.")

(defun identity (x) x)

(defun constantly-prototype (&rest ignore)
  (declare (ignore ignore))
  'value)

(defun constantly-true (&rest ignore) 
  (declare (ignore ignore))
  t)

(defun constantly-false (&rest ignore) 
  (declare (ignore ignore))
  nil)

(define-compiler-macro constantly (&whole form value-form &environment env)
  (cond
   ((movitz:movitz-constantp value-form env)
    (let ((value (movitz:movitz-eval value-form env)))
      (case (translate-program value :muerte.cl :cl)
	((t) `(function constantly-true))
	((nil) `(function constantly-false))
	(t form))))
   (t form)))

(defun constantly (x)
  (lambda () x))

(defun complement-prototype (&rest args)
  (declare (dynamic-extent args))
  (not (apply 'function args)))

(define-compiler-macro complement (&whole form function-form &environment env)
  (cond
   ((and (listp function-form)
	 (eq 'function (first function-form))
	 (typep (movitz:movitz-eval (translate-program function-form :cl :muerte.cl) env)
		'movitz:movitz-funobj))
    `(make-prototyped-function `(complement ,(second function-form))
			       complement-prototype
			       ,(movitz:movitz-eval (translate-program function-form :cl :muerte.cl))))
   (t form)))

(defun complement (function)
  (lambda (&rest args)
    (declare (dynamic-extent args))
    (not (apply function args))))

(defun unbound-function (&edx edx &rest args)
  "This is the function that is the unbound value for function cells."
  (declare (dynamic-extent args))
  (let ((function-name (typecase edx
			 (symbol
			  edx)
			 (compiled-function
			  (funobj-name edx))
			 (t '(unknown)))))
;;     (when los0::*funbound-counter*
;;       (incf (gethash function-name los0::*funbound-counter* 0)))
    (with-simple-restart (continue "Return NIL from ~S." function-name)
      (error 'undefined-function-call
	     :name function-name
	     :arguments (copy-list args))))
  nil)

;;; funobj object

(defun funobj-type (funobj)
  (check-type funobj function)
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    (:xorl :ecx :ecx)
    (:compile-form (:result-mode :eax) funobj)
    (:movb (:eax (:offset movitz-funobj funobj-type)) :cl)))

(defun (setf funobj-type) (type funobj)
  (check-type funobj function)
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    (:compile-two-forms (:eax :untagged-fixnum-ecx) funobj type)
    (:movb :cl (:eax (:offset movitz-funobj funobj-type)))))

(defun funobj-code-vector (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'code-vector)
	  :type :code-vector))

(defun (setf funobj-code-vector) (code-vector funobj)
  (check-type funobj function)
  (check-type code-vector code-vector)
  (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'code-vector)
		:type :code-vector)
    code-vector))

(defun funobj-code-vector%1op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is
represented as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    ;; Set up atomically continuation.
    (:declare-label-set restart-jumper (retry))
    (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
    (:pushl 'restart-jumper)
    ;; ..this allows us to detect recursive atomicallies.
    (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
    (:pushl :ebp)
   retry

    (:movl (:esp) :ebp)
    (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
    ;; Now inside atomically section.
    
    (:compile-form (:result-mode :ebx) funobj)
    (:movl (:ebx (:offset movitz-funobj code-vector)) :eax) ; EAX = code-vector
    (:movl (:ebx (:offset movitz-funobj code-vector%1op)) :ecx)
    ;; determine if ECX is a pointer into EAX
    (:subl :eax :ecx)
    (:jl 'return-vector)
    (:leal ((:ecx #.movitz:+movitz-fixnum-factor+)) :ecx)
    (:cmpl (:eax (:offset movitz-basic-vector num-elements -2)) :ecx)
    (:jnc 'return-vector)
    ;; return the integer offset
    (:movl :ecx :eax)
    (:jmp 'done)
   return-vector
    (:testl 7 (:ebx (:offset movitz-funobj code-vector%1op)))
    (:jnz '(:sub-program () (:int 63)))
    (:movl #xfffffffe :eax)
    (:addl (:ebx (:offset movitz-funobj code-vector%1op)) :eax)
   done
    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
    (:leal (:esp 16) :esp)))

(defun (setf funobj-code-vector%1op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%1op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx (:offset movitz-funobj code-vector)) :eax)
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%1op)))
       (:compile-form (:result-mode :untagged-fixnum-ecx) code-vector)
       (:addl :ecx (:ebx (:offset movitz-funobj code-vector%1op))))))
  code-vector)

(defun funobj-code-vector%2op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is
represented as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    ;; Set up atomically continuation.
    (:declare-label-set restart-jumper (retry))
    (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
    (:pushl 'restart-jumper)
    ;; ..this allows us to detect recursive atomicallies.
    (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
    (:pushl :ebp)
   retry
    (:movl (:esp) :ebp)
    (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
    ;; Now inside atomically section.

    (:compile-form (:result-mode :ebx) funobj)
    (:movl (:ebx (:offset movitz-funobj code-vector)) :eax) ; EAX = code-vector
    (:movl (:ebx (:offset movitz-funobj code-vector%2op)) :ecx)
    ;; determine if ECX is a pointer into EAX
    (:subl :eax :ecx)
    (:jl 'return-vector)
    (:leal ((:ecx #.movitz:+movitz-fixnum-factor+)) :ecx)
    (:cmpl (:eax (:offset movitz-basic-vector num-elements -2)) :ecx)
    (:jnc 'return-vector)
    ;; return the integer offset EAX-EBX
    (:movl :ecx :eax)
    (:jmp 'done)
   return-vector
    (:testl 7 (:ebx (:offset movitz-funobj code-vector%2op)))
    (:jnz '(:sub-program () (:int 63)))
    (:movl #xfffffffe :eax)
    (:addl (:ebx (:offset movitz-funobj code-vector%2op)) :eax)
   done
    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
    (:leal (:esp 16) :esp)))

(defun (setf funobj-code-vector%2op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%2op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx (:offset movitz-funobj code-vector)) :eax)
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%2op)))
       (:compile-form (:result-mode :untagged-fixnum-ecx) code-vector)
       (:addl :ecx (:ebx (:offset movitz-funobj code-vector%2op))))))
  code-vector)

(defun funobj-code-vector%3op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is
represented as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    ;; Set up atomically continuation.
    (:declare-label-set restart-jumper (retry))
    (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
    (:pushl 'restart-jumper)
    ;; ..this allows us to detect recursive atomicallies.
    (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
    (:pushl :ebp)
   retry
    (:movl (:esp) :ebp)
    (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
    ;; Now inside atomically section.
    
    (:compile-form (:result-mode :ebx) funobj)
    (:movl (:ebx (:offset movitz-funobj code-vector)) :eax) ; EAX = code-vector
    (:movl (:ebx (:offset movitz-funobj code-vector%3op)) :ecx)
    ;; determine if ECX is a pointer into EAX
    (:subl :eax :ecx)
    (:jl 'return-vector)
    (:leal ((:ecx #.movitz:+movitz-fixnum-factor+)) :ecx)
    (:cmpl (:eax (:offset movitz-basic-vector num-elements -2)) :ecx)
    (:jnc 'return-vector)
    ;; return the integer offset EAX-EBX
    (:movl :ecx :eax)
    (:jmp 'done)
   return-vector
    (:testl 7 (:ebx (:offset movitz-funobj code-vector%3op)))
    (:jnz '(:sub-program () (:int 63)))
    (:movl #xfffffffe :eax)
    (:addl (:ebx (:offset movitz-funobj code-vector%3op)) :eax)
   done
    (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
    (:leal (:esp 16) :esp)))

(defun (setf funobj-code-vector%3op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%3op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx (:offset movitz-funobj code-vector)) :eax)
       (:movl :eax (:ebx (:offset movitz-funobj code-vector%3op)))
       (:compile-form (:result-mode :untagged-fixnum-ecx) code-vector)
       (:addl :ecx (:ebx (:offset movitz-funobj code-vector%3op))))))
  code-vector)

(defun funobj-name (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'name)))

(defun (setf funobj-name) (name funobj)
  (check-type funobj function)
  (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'name))
    name))

(defun funobj-lambda-list (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'lambda-list)))

(defun (setf funobj-lambda-list) (lambda-list funobj)
  (check-type funobj function)
  (check-type lambda-list list)
  (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'lambda-list))
    lambda-list))

(defun funobj-num-constants (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'num-constants)
	  :type :unsigned-byte16))

(defun (setf funobj-num-constants) (num-constants funobj)
  (check-type funobj function)
  (check-type num-constants (unsigned-byte 16))
  (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'num-constants)
		:type :unsigned-byte16)
    num-constants))

(defun funobj-num-jumpers (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'num-jumpers)
	  :type :unsigned-byte14))

(defun (setf funobj-num-jumpers) (num-jumpers funobj)
  (check-type funobj function)
  (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'num-jumpers)
		:type :unsigned-byte14)
    num-jumpers)
  #+ignore
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) num-jumpers funobj)
    (:movw :ax (:ebx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::num-jumpers)))))

(defun funobj-constant-ref (funobj index)
  (check-type funobj function)
  (assert (below index (funobj-num-constants funobj)) (index)
    "Index ~D out of range, ~S has ~D constants." index funobj (funobj-num-constants funobj))
  (if (>= index (funobj-num-jumpers funobj))
      (memref funobj (movitz-type-slot-offset 'movitz-funobj 'constant0) :index index)
    ;; For a jumper, return its offset relative to the code-vector.
    ;; This is tricky wrt. to potential GC interrupts, because we're doing
    ;; pointer arithmetics.
    (with-inline-assembly (:returns :eax)
      (:compile-two-forms (:eax :ecx) funobj index)
      (:movl #.movitz:+code-vector-transient-word+ :ebx)
      (:addl (:eax #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector))
	     :ebx)			; code-vector (word) into ebx
      (:subl (:eax :ecx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0))
	     :ebx)
      (:negl :ebx)
      (:leal ((:ebx #.movitz:+movitz-fixnum-factor+)) :eax))))

(defun (setf funobj-constant-ref) (value funobj index)
  (check-type funobj function)
  (assert (below index (funobj-num-constants funobj)) (index)
    "Index ~D out of range, ~S has ~D constants." index funobj (funobj-num-constants funobj))
  (if (>= index (funobj-num-jumpers funobj))
      (setf (memref funobj (movitz-type-slot-offset 'movitz-funobj 'constant0) :index index)
	value)
    (progn
      (assert (below value (length (funobj-code-vector funobj))) (value)
	"The jumper value ~D is invalid because the code-vector's size is ~D."
	value (length (funobj-code-vector funobj)))
      (progn ;; XXX without-gc
       (with-inline-assembly (:returns :nothing)
	 (:compile-two-forms (:eax :edx) funobj index)
	 (:compile-form (:result-mode :ecx) value)
	 (:movl #.movitz:+code-vector-transient-word+ :ebx)
	 (:addl (:eax #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:code-vector))
		:ebx)			; code-vector (word) into ebx
	 (:shrl #.movitz:+movitz-fixnum-shift+ :ecx) ; value
	 (:movl :ecx (:eax :edx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)))
	 (:addl :ebx (:eax :edx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)))))
      value)))

(defun funobj-debug-info (funobj)
  (check-type funobj function)
  (memref funobj (movitz-type-slot-offset 'movitz-funobj 'debug-info) :type :unsigned-byte16))

(defun funobj-frame-raw-locals (funobj)
  "The number of unboxed slots in this function's stack-frame(s)."
  (declare (ignore funobj))
  0)

(defun funobj-frame-headers-p (funobj)
  "Can this function place header-vals in its stack-frame?"
  (declare (ignore funobj))
  t)

(defun make-funobj (&key (name :unnamed)
			 (code-vector (funobj-code-vector #'constantly-prototype))
			 (constants nil)
			 lambda-list)
  (setf code-vector
    (etypecase code-vector
      (code-vector code-vector)
      (list
       (make-array (length code-vector)
		   :element-type 'code
		   :initial-contents code-vector))
      (vector 
       (make-array (length code-vector)
		   :element-type 'code
		   :initial-contents code-vector))))
  (let* ((num-constants (length constants))
	 (funobj (macrolet
		     ((do-it ()
			`(with-allocation-assembly ((+ num-constants
						       ,(movitz::movitz-type-word-size 'movitz-funobj))
						    :object-register :eax
						    :size-register :ecx)
			   (:movl ,(movitz:tag :funobj) (:eax ,movitz:+other-type-offset+))
			   (:load-lexical (:lexical-binding num-constants) :edx)
			   (:movl :edx :ecx)
			   (:shll ,(- 16 movitz:+movitz-fixnum-shift+) :ecx)
			   (:movl :ecx (:eax (:offset movitz-funobj num-jumpers)))
			   (:xorl :ecx :ecx)
			   (:xorl :ebx :ebx)
			   (:testl :edx :edx)
			   (:jmp 'init-done)
			   init-loop
			   (:movl :ecx (:eax :ebx ,movitz:+other-type-offset+))
			   (:addl 4 :ebx)
			   (:cmpl :ebx :edx)
			   (:ja 'init-loop)
			   init-done
			   (:leal (:edx ,(bt:sizeof 'movitz:movitz-funobj)) :ecx))))
		   (do-it))))
    (setf (funobj-name funobj) name
	  (funobj-code-vector funobj) code-vector
	  ;; revert to default trampolines for now..
	  (funobj-code-vector%1op funobj) (symbol-value 'trampoline-funcall%1op)
	  (funobj-code-vector%2op funobj) (symbol-value 'trampoline-funcall%2op)
	  (funobj-code-vector%3op funobj) (symbol-value 'trampoline-funcall%3op)
	  (funobj-lambda-list funobj) lambda-list)
    (do* ((i 0 (1+ i))
	  (p constants (cdr p))
	  (x (car p)))
	((endp p))
      (setf (funobj-constant-ref funobj i) x))
    funobj))


(defun install-function (name constants code-vector)
  (let ((funobj (make-funobj :name name :constants constants :code-vector code-vector)))
    (warn "installing ~S for ~S.." funobj name)
    (setf (symbol-function name) funobj)))

(defun replace-funobj (dst src &optional (name (funobj-name src)))
  "Copy each element of src to dst. Dst's num-constants must be initialized,
so that we can be reasonably sure of dst's size."
  (assert (= (funobj-num-constants src)
	     (funobj-num-constants dst)))
  (setf (funobj-name dst) name
	(funobj-num-jumpers dst) (funobj-num-jumpers src)
	(funobj-code-vector dst) (funobj-code-vector src)
	(funobj-code-vector%1op dst) (funobj-code-vector%1op src)
	(funobj-code-vector%2op dst) (funobj-code-vector%2op src)
	(funobj-code-vector%3op dst) (funobj-code-vector%3op src)
	(funobj-lambda-list dst) (funobj-lambda-list src))
  (dotimes (i (funobj-num-constants src))
    (setf (funobj-constant-ref dst i)
      (funobj-constant-ref src i)))
  dst)

(defun copy-funobj (old-funobj)
  (check-type old-funobj function)
  (%shallow-copy-object old-funobj
			(+ (funobj-num-constants old-funobj)
			   (movitz-type-word-size 'movitz-funobj))))

(defun install-funobj-name (name funobj)
  (setf (funobj-name funobj) name)
  funobj)

(defun fdefinition (function-name)
  (etypecase function-name
    (symbol
     (symbol-function function-name))
    ((cons (eql setf))
     (symbol-function (gethash (cadr function-name) *setf-namespace*)))))

(defun (setf fdefinition) (value function-name)
  (etypecase function-name
    (symbol
     (setf (symbol-function function-name) value))
    ((cons (eql setf))
     (let* ((setf-name (cadr function-name))
	    (setf-symbol (or (gethash setf-name *setf-namespace*)
			     (setf (gethash setf-name *setf-namespace*)
			       (make-symbol (format nil "~A-~A" 'setf 'setf-name))))))
       (setf (symbol-function setf-symbol)
	 value)))))

(defun fmakunbound (function-name)
  (setf (fdefinition function-name)
    (load-global-constant unbound-function))
  function-name)

(defun make-macro-function (expander name)
  "From a regular function, such as a (lambda (form env) ...), make a bona fide macro-function."
  (let ((macro-function (install-funobj-name name
                                             (lambda (&edx edx &optional form env (first-extra nil extras-p) &rest more-extras)
                                               (declare (ignore first-extra more-extras))
                                               (verify-macroexpand-call edx name extras-p)
                                               (funcall expander form env)))))
    (setf (funobj-type macro-function)
          #.(bt:enum-value 'movitz::movitz-funobj-type :macro-function))
    macro-function))
