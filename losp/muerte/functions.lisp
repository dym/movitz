;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      functions.lisp
;;;; Description:   Misc. function-oriented functions
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Mar 12 22:58:54 2002
;;;;                
;;;; $Id: functions.lisp,v 1.16 2004/07/15 21:06:59 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/setf)
(provide :muerte/functions)

(In-package muerte)

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
	(t `(make-prototyped-function (constantly ,value)
				      constantly-prototype
				      (value ,value))))))
   (t (error "Non-constant constantly forms not yet supported: ~S" form)
      form)))

(defun complement-prototype (&rest args)
  (declare (dynamic-extent args))
  (not (apply 'function args)))

(define-compiler-macro complement (&whole form function-form)
  (cond
   ((movitz:movitz-constantp function-form)
    (let ((function (movitz:movitz-eval function-form)))
      `(make-prototyped-function (complement ,function)
				 complement-prototype
				 (function ,function))))
   ((and (listp function-form)
	 (eq 'function (first function-form))
	 (symbolp (second function-form))
	 (typep (movitz:movitz-eval (translate-program function-form :cl :muerte.cl))
		'movitz:movitz-funobj))
    `(make-prototyped-function (complement ,function-form)
			       complement-prototype
			       (function ,(movitz:movitz-eval (translate-program function-form
									      :cl :muerte.cl)))))
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
    (:movb (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:funobj-type)) :cl)))

(defun funobj-code-vector (funobj)
  (check-type funobj function)
  (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::code-vector) 0 :code-vector))

(defun (setf funobj-code-vector) (code-vector funobj)
  (check-type funobj function)
  (check-type code-vector code-vector)
  (setf (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::code-vector) 0 :code-vector)
    code-vector))

(defun funobj-code-vector%1op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is represented
as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) funobj)
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :ebx) ; EBX = code-vector
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%1op)) :eax) ; EAX = code-vector%1op
    ;; determine if EAX is a pointer into EBX
    (:cmpl :ebx :eax)
    (:jl 'return-vector)
    (:andb #xf8 :bl)
    (:addl #x100 :ebx)
    (:cmpl :ebx :eax)
    (:jg 'return-vector)
    ;; return the integer offset EAX-EBX
    (:subl #x100 :ebx)
    (:subl :ebx :eax)
    (:shll #.movitz:+movitz-fixnum-shift+ :eax)
    (:jmp 'done)
    return-vector
    (:subl 2 :eax)
    done))				; this cell stores word+2

(defun (setf funobj-code-vector%1op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%1op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :eax)
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%1op)))
       (:compile-form (:result-mode :untagged-fixnum-eax) code-vector)
       (:addl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%1op)))
       (:xorl :eax :eax))))
  code-vector)

(defun funobj-code-vector%2op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is represented
as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) funobj)
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :ebx) ; EBX = code-vector
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%2op)) :eax) ; EAX = code-vector%1op
    ;; determine if EAX is a pointer into EBX
    (:cmpl :ebx :eax)
    (:jl 'return-vector)
    (:andb #xf8 :bl)
    (:addl #x100 :ebx)
    (:cmpl :ebx :eax)
    (:jg 'return-vector)
    ;; return the integer offset EAX-EBX
    (:subl #x100 :ebx)
    (:subl :ebx :eax)
    (:shll #.movitz:+movitz-fixnum-shift+ :eax)
    (:jmp 'done)
    return-vector
    (:subl 2 :eax)
    done))

(defun (setf funobj-code-vector%2op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%2op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :eax)
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%2op)))
       (:compile-form (:result-mode :untagged-fixnum-eax) code-vector)
       (:addl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%2op)))
       (:xorl :eax :eax))))
  code-vector)

(defun funobj-code-vector%3op (funobj)
  "This slot is not a lisp value, it is a direct address to code entry point. In practice it is either
a pointer into the regular code-vector, or it points (with offset 2) to another vector entirely.
The former is represented as a lisp integer that is the index into the code-vector, the latter is represented
as that vector."
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) funobj)
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :ebx) ; EBX = code-vector
    (:movl (:eax #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%3op)) :eax) ; EAX = code-vector%1op
    ;; determine if EAX is a pointer into EBX
    (:cmpl :ebx :eax)
    (:jl 'return-vector)
    (:andb #xf8 :bl)
    (:addl #x100 :ebx)
    (:cmpl :ebx :eax)
    (:jg 'return-vector)
    ;; return the integer offset EAX-EBX
    (:subl #x100 :ebx)
    (:subl :ebx :eax)
    (:shll #.movitz:+movitz-fixnum-shift+ :eax)
    (:jmp 'done)
    return-vector
    (:subl 2 :eax)
    done))

(defun (setf funobj-code-vector%3op) (code-vector funobj)
  (check-type funobj function)
  (etypecase code-vector
    (code-vector
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:compile-form (:result-mode :eax) code-vector)
       (:addl 2 :eax)			; this cell stores word+2
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%3op)))))
    (integer
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :ebx) funobj)
       (:movl (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector)) :eax)
       (:movl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%3op)))
       (:compile-form (:result-mode :untagged-fixnum-eax) code-vector)
       (:addl :eax (:ebx #.(bt::slot-offset 'movitz:movitz-funobj 'movitz:code-vector%3op)))
       (:xorl :eax :eax))))
  code-vector)

(defun funobj-name (funobj)
  (check-type funobj function)
  (movitz-accessor funobj movitz-funobj name))

(defun (setf funobj-name) (name funobj)
  (check-type funobj function)
  ;; (check-type name (or symbol list)
  (setf-movitz-accessor (funobj movitz-funobj name) name))

(defun funobj-lambda-list (funobj)
  (check-type funobj function)
  (movitz-accessor funobj movitz-funobj lambda-list))

(defun (setf funobj-lambda-list) (lambda-list funobj)
  (check-type funobj function)
  (check-type lambda-list list)
  (setf-movitz-accessor (funobj movitz-funobj lambda-list) lambda-list))

(defun funobj-num-constants (funobj)
  (check-type funobj function)
  (movitz-accessor-u16 funobj movitz-funobj num-constants))

(defun (setf funobj-num-constants) (num-constants funobj)
  (check-type funobj function)
  (check-type num-constants (unsigned-byte 16))
  (set-movitz-accessor-u16 funobj movitz-funobj num-constants num-constants))

(defun funobj-num-jumpers (funobj)
  (check-type funobj function)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) funobj)
    (:movzxw (:eax #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::num-jumpers)) :eax)))

(defun (setf funobj-num-jumpers) (num-jumpers funobj)
  (check-type funobj function)
  (check-type num-jumpers (unsigned-byte 14))
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) num-jumpers funobj)
    (:movw :ax (:ebx #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::num-jumpers)))))

(defun funobj-constant-ref (funobj index)
  (check-type funobj function)
  (assert (below index (funobj-num-constants funobj)) (index)
    "Index ~D out of range, ~S has ~D constants." index funobj (funobj-num-constants funobj))
  (if (>= index (funobj-num-jumpers funobj))
      (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0) index :lisp)
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
      (setf (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz::constant0)
		    index :lisp)
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
  (movitz-accessor-u16 funobj movitz-funobj debug-info))

(defun funobj-frame-num-unboxed (funobj)
  "The number of unboxed slots in this function's stack-frame(s)."
  (declare (ignore funobj))
  0)

(defun make-funobj (&key (name :unnamed)
			 (code-vector (funobj-code-vector #'constantly-prototype))
			 (constants nil)
			 ;; (num-constants (length constants))
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
  (let ((funobj (malloc-pointer-words (+ #.(cl:truncate (bt:sizeof 'movitz:movitz-funobj) 4)
					 (length constants)))))
    (setf (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:type) 0 :unsigned-byte16)
      #.(movitz:tag :funobj))
    (setf (funobj-name funobj) name
	  (funobj-code-vector funobj) code-vector
	  ;; revert to default trampolines for now..
	  (funobj-code-vector%1op funobj) (get-global-property :trampoline-funcall%1op)
	  (funobj-code-vector%2op funobj) (get-global-property :trampoline-funcall%2op)
	  (funobj-code-vector%3op funobj) (get-global-property :trampoline-funcall%3op)
	  (funobj-lambda-list funobj) lambda-list
	  (funobj-num-constants funobj) (length constants))
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

(defun copy-funobj (old-funobj &optional (name (funobj-name old-funobj)))
  (let* ((num-constants (funobj-num-constants old-funobj))
	 (funobj (malloc-pointer-words (+ #.(cl:truncate (bt:sizeof 'movitz:movitz-funobj) 4)
					  num-constants))))
    (setf (memref funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:type) 0 :unsigned-byte16)
      (memref old-funobj #.(bt:slot-offset 'movitz:movitz-funobj 'movitz:type) 0 :unsigned-byte16))
    (setf (funobj-num-constants funobj) num-constants)
    (replace-funobj funobj old-funobj name)))

(defun install-funobj-name (name funobj)
  (setf (funobj-name funobj) name)
  funobj)

(defun fdefinition (function-name)
  (etypecase function-name
    (symbol
     (symbol-function function-name))
    ((cons (eql setf))
     (symbol-function (gethash (cadr function-name)
			       (get-global-property :setf-namespace))))))

(defun (setf fdefinition) (value function-name)
  (etypecase function-name
    (symbol
     (setf (symbol-function function-name) value))
    ((cons (eql setf))
     (let* ((setf-namespace (get-global-property :setf-namespace))
	    (setf-name (cadr function-name))
	    (setf-symbol (or (gethash setf-name setf-namespace)
			     (setf (gethash setf-name setf-namespace)
			       (make-symbol (format nil "~A-~A" 'setf 'setf-name))))))
       (setf (symbol-function setf-symbol)
	 value)))))

(defun fmakunbound (function-name)
  (setf (fdefinition function-name)
    (load-global-constant unbound-function)))
