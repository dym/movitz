;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      arithmetic-macros.lisp
;;;; Description:   Transformation of arithmethic operators.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Jul 17 13:42:46 2004
;;;;                
;;;; $Id: arithmetic-macros.lisp,v 1.23 2008-04-27 19:26:14 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(provide :muerte/arithmetic-macros)

(in-package muerte)

;;;

(defun number-double-dispatch-error (x y)
  (when (not (typep x 'number))
    (error 'type-error
           :datum x
           :expected-type 'number))
  (when (not (typep y 'number))
    (error 'type-error
           :datum y
           :expected-type 'number))
  (error "Operation not implemented for numbers ~S and ~S." x y))

(defmacro number-double-dispatch ((x y) &rest clauses)
  `(let ((x ,x) (y ,y))
     (cond ,@(mapcar (lambda (clause)
		       (destructuring-bind ((x-type y-type) . then-body)
			   clause
			 `((and (typep x ',x-type) (typep y ',y-type))
			   ,@then-body)))
		     clauses)
	   (t (number-double-dispatch-error x y)))))


(define-compiler-macro evenp (x)
  `(with-inline-assembly (:returns :boolean-zf=1)
     (:compile-form (:result-mode :eax) ,x)
     (:call-global-pf unbox-u32)
     (:testb 1 :cl)))

(define-compiler-macro oddp (x)
  `(with-inline-assembly (:returns :boolean-zf=0)
     (:compile-form (:result-mode :eax) ,x)
     (:call-global-pf unbox-u32)
     (:testb 1 :cl)))

(define-compiler-macro + (&whole form &rest operands &environment env)
  (flet ((term (x) (gensym "term-")))
    (case (length operands)
      (0 0)
      (1 (first operands))
      (2 (let ((term1 (term (first operands)))
	       (term2 (term (second operands))))
	   `(let ((,term1 ,(first operands))
		  (,term2 ,(second operands)))
	      (++%2op ,term1 ,term2))))
      (t (multiple-value-bind (constant-term non-constants)
	     (loop for operand in operands
		 if (movitz:movitz-constantp operand env)
		 sum (movitz:movitz-eval operand env) into constant-term
		 else collect operand into non-constant-operands
		 finally (return (values constant-term non-constant-operands)))
	   (cond
	    ((null non-constants)
	     constant-term)
	    ((and (= 0 constant-term)
		  (not (cdr non-constants)))
	     (car non-constants))
	    ((= 0 constant-term)
	     `(+ (+ ,(first non-constants) ,(second non-constants)) ,@(cddr non-constants)))
	    (t `(+ (+ ,constant-term ,(first non-constants)) ,@(cdr non-constants)))))))))

(define-compiler-macro 1+ (number)
  `(+ 1 ,number))


(define-compiler-macro 1- (number)
  `(+ -1 ,number))

(define-modify-macro incf (&optional (delta-form 1)) +)

(define-compiler-macro - (&whole form &rest operands &environment env)
  (case (length operands)
    (0 0)
    (1 (let ((x (first operands)))
	 (if (movitz:movitz-constantp x env)
	     (- (movitz:movitz-eval x env))
	   form)))
    (2 (let ((minuend (first operands))
	     (subtrahend (second operands)))
	 (cond
	  ((movitz:movitz-constantp subtrahend env)
	   `(+ ,minuend ,(- (movitz:movitz-eval subtrahend env))))
	  (t form))))
    (t `(- ,(first operands) (+ ,@(rest operands))))))

(define-modify-macro decf (&optional (delta-form 1)) -)

(define-compiler-macro <=%3op (min x max &environment env)
  (cond
   ((and (movitz:movitz-constantp min env)
	 (movitz:movitz-constantp max env))
    (let ((min (movitz:movitz-eval min env))
	  (max (movitz:movitz-eval max env)))
      (cond
       ((movitz:movitz-constantp x env)
	(<= min (movitz:movitz-eval x env) max))
       ((< max min)
	`(progn ,x nil))
       ((= max min)
	`(= ,x ,min))
       ((minusp min)
	`(let ((x ,x))
	   (and (<= ,min x) (<= x ,max))))
       ((or (not (<= movitz:+movitz-most-negative-fixnum+
		     min
		     movitz:+movitz-most-positive-fixnum+))
	    (not (<= movitz:+movitz-most-negative-fixnum+
		     max
		     movitz:+movitz-most-positive-fixnum+)))
	`(let ((x ,x))
	   (and (<=%2op ,min x)
		(<=%2op x ,max))))
       ((= 0 min)
	`(with-inline-assembly (:returns :boolean-cf=1)
	   (:compile-form (:result-mode :eax) ,x)
	   (:testb ,movitz::+movitz-fixnum-zmask+ :al)
	   (:jnz '(:sub-program () (:int 64)))
	   (:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)))
       (t `(do-result-mode-case ()
	     (:booleans
	      (with-inline-assembly (:returns :boolean-zf=0)
		(:compile-form (:result-mode :eax) ,x)
		(:testb ,movitz::+movitz-fixnum-zmask+ :al)
		(:jnz '(:sub-program () (:int 64)))
		(:cmpl ,(* min movitz::+movitz-fixnum-factor+) :eax)
		(:sbbl :ecx :ecx)
		(:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)
		(:adcl 0 :ecx)))
	     (t (with-inline-assembly (:returns (:boolean-ecx 1 0))
		  (:compile-form (:result-mode :eax) ,x)
		  (:testb ,movitz::+movitz-fixnum-zmask+ :al)
		  (:jnz '(:sub-program () (:int 64)))
		  (:cmpl ,(* min movitz::+movitz-fixnum-factor+) :eax)
		  (:sbbl :ecx :ecx)
		  (:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)
		  (:adcl 0 :ecx))))))))   
   (t `(let ((x ,x))
	 (and (<= ,min x) (<= x ,max))))))
       
(define-compiler-macro below (&whole form x max &environment env)
  (if (movitz:movitz-constantp max env)
      `(with-inline-assembly (:returns :boolean-cf=1)
	 (:compile-form (:result-mode :eax) ,x)
	 (:testb ,movitz::+movitz-fixnum-zmask+ :al)
	 (:jnz '(:sub-program () (:int 64)))
	 (:cmpl ,(* (movitz:movitz-eval max env)
		    movitz::+movitz-fixnum-factor+)
		:eax))
    `(with-inline-assembly (:returns :boolean-cf=1)
       (:compile-two-forms (:eax :ebx) ,x ,max)
       (:testb ,movitz::+movitz-fixnum-zmask+ :al)
       (:jnz '(:sub-program () (:int 64)))
       (:testb ,movitz::+movitz-fixnum-zmask+ :bl)
       (:jnz '(:sub-program () (:movl :ebx :eax) (:int 64)))
       (:cmpl :ebx :eax))))

(define-compiler-macro zerop (number)
  `(= 0 ,number))


(define-compiler-macro plusp (number)
  `(> ,number 0))

(define-compiler-macro minusp (number)
  `(< ,number 0))

(define-compiler-macro abs (x)
  `(let ((x ,x))
     (if (>= x 0) x (- x))))

(define-compiler-macro max (&whole form first-number &rest more-numbers)
  (case (length more-numbers)
    (0 first-number)
    (1 `(let ((x ,first-number)
	      (y ,(car more-numbers)))
	  (if (>= x y) x y)))
    ((2 3 4)
     `(max ,first-number (max ,@more-numbers)))
    (t form)))

(define-compiler-macro min (&whole form first-number &rest more-numbers)
  (case (length more-numbers)
    (0 first-number)
    (1 `(let ((x ,first-number)
	      (y ,(car more-numbers)))
	  (if (<= x y) x y)))
    ((2 3 4)
     `(min ,first-number (min ,@more-numbers)))
    (t form)))

(define-compiler-macro ash (&whole form integer count &environment env)
  (if (not (movitz:movitz-constantp count env))
      form
    (let ((count (movitz:movitz-eval count env)))
      (cond
       ((movitz:movitz-constantp integer env)
	(ash (movitz::movitz-eval integer env) count))
       ((= 0 count)
	integer)
       (t form
	  #+igore
	  (let ((load-integer `((:compile-form (:result-mode :register) ,integer)
				(:testb ,movitz::+movitz-fixnum-zmask+ (:result-register-low8))
				(:jnz '(:sub-program () (:int 107) (:jmp (:pc+ -4)))))))
	    (cond
	     ((<= 1 count 4)
	      `(with-inline-assembly (:returns :register :side-effects nil)
		 ,@load-integer
		 ,@(loop repeat count
		       append `((:addl (:result-register) (:result-register))
				(:into)))))
	     ((< 0 count #.(1- movitz::+movitz-fixnum-bits+))
	      `(with-inline-assembly (:returns :register :side-effects nil :type integer)
		 ,@load-integer
		 (:cmpl ,(ash 1 (- (- 31 0) count))
			(:result-register))
		 (:jge '(:sub-program () (:int 4)))
		 (:cmpl ,(- (ash 1 (- (- 31 0) count)))
			(:result-register))
		 (:jl '(:sub-program () (:int 4)))
		 (:shll ,count (:result-register))))
	     ((= -1 count)
	      `(with-inline-assembly (:returns :register :side-effects nil :type integer)
		 ,@load-integer
		 (:andb #.(cl:logxor #xfe (cl:* 2 movitz::+movitz-fixnum-zmask+)) (:result-register-low8))
		 (:sarl 1 (:result-register))))
	     ((> 0 count #.(cl:- (cl:1- movitz::+movitz-fixnum-bits+)))
	      `(with-inline-assembly (:returns :register :side-effects nil :type integer)
		 ,@load-integer
		 (:andl ,(ldb (byte 32 0)
			      (ash movitz:+movitz-most-positive-fixnum+
				   (- movitz:+movitz-fixnum-shift+ count)))
			(:result-register))
		 (:sarl ,(- count) (:result-register))))
	     ((minusp count)
	      `(if (minusp ,integer) -1 0))
	     (t `(if (= 0 ,integer) 0 (with-inline-assembly (:returns :non-local-exit)
					(:int 4)))))))))))

(define-compiler-macro * (&whole form &rest operands &environment env)
  (case (length operands)
    (0 0)
    (1 (first operands))
    (2 (let ((factor1 (first operands))
	     (factor2 (second operands)))
	 (cond
	  ((and (movitz:movitz-constantp factor1 env)
		(movitz:movitz-constantp factor2 env))
	   (* (movitz:movitz-eval factor1 env)
	      (movitz:movitz-eval factor2 env)))
	  ((movitz:movitz-constantp factor2 env)
	   `(* ,(movitz:movitz-eval factor2 env) ,factor1))
	  ((movitz:movitz-constantp factor1 env)
	   (let ((f1 (movitz:movitz-eval factor1 env)))
	     (case f1
	       (0 `(progn ,factor2 0))
	       (1 factor2)
	       (2 `(let ((x2 ,factor2)) (+ x2 x2)))
	       (t `(no-macro-call * ,factor1 ,factor2)))))
	  (t `(no-macro-call * ,factor1 ,factor2)))))
    (t `(* (* ,(first operands) ,(second operands)) ,@(cddr operands)))))


(define-compiler-macro byte (&whole form size position &environment env)
  (cond
   ((and (movitz:movitz-constantp size env)
	 (movitz:movitz-constantp position env))
    (let ((size (movitz:movitz-eval size env))
	  (position (movitz:movitz-eval position env)))
      (check-type position (unsigned-byte 20))
      (+ position (ash size 20))))
   (t form)))

(define-compiler-macro logand (&whole form &rest integers &environment env)
  (let ((constant-folded-integers (loop for x in integers
				      with folded-constant = -1
				      if (and (movitz:movitz-constantp x env)
					      (not (= -1 (movitz:movitz-eval x env))))
				      do (setf folded-constant
					   (logand folded-constant (movitz:movitz-eval x env)))
				      else collect x into non-constants
				      finally (return (if (= -1 folded-constant)
							  non-constants
							(cons folded-constant non-constants))))))
    (cond
      ((null constant-folded-integers)
       0)
      ((null (rest constant-folded-integers))
       (first constant-folded-integers))
      ((eql 0 (first constant-folded-integers))
       `(progn ,@(rest constant-folded-integers) 0))
      ((null (cddr constant-folded-integers))
       (cond
	 ((typep (first constant-folded-integers)
		 '(unsigned-byte 32))
	  (let ((x (first constant-folded-integers)))
	    `(with-inline-assembly (:returns :untagged-fixnum-ecx
					     :type (unsigned-byte ,(integer-length x)))
	       (:compile-form (:result-mode :untagged-fixnum-ecx)
			      ,(second constant-folded-integers))
	       (:andl ,x :ecx))))
	 (t `(no-macro-call logand
			    ,(first constant-folded-integers)
			    ,(second constant-folded-integers)))))
      (t `(logand (logand ,(first constant-folded-integers)
			  ,(second constant-folded-integers))
		  ,@(cddr constant-folded-integers))))))

(define-compiler-macro logior (&whole form &rest integers &environment env)
  (let ((constant-folded-integers (loop for x in integers
				      with folded-constant = 0
				      if (and (movitz:movitz-constantp x env)
					      (not (zerop (movitz:movitz-eval x env))))
				      do (setf folded-constant
					   (logior folded-constant (movitz:movitz-eval x env)))
				      else collect x into non-constants
				      finally (return (if (= 0 folded-constant)
							  non-constants
							(cons folded-constant non-constants))))))
    (case (length constant-folded-integers)
      (0 0)
      (1 (first constant-folded-integers))
      (2 `(no-macro-call logior ,(first constant-folded-integers) ,(second constant-folded-integers)))
      (t `(logior (logior ,(first constant-folded-integers) ,(second constant-folded-integers))
		  ,@(cddr constant-folded-integers))))))

(define-compiler-macro ldb%byte (&whole form &environment env size position integer)
  "This is LDB with explicit byte-size and position parameters."
  (cond
   ((and (movitz:movitz-constantp size env)
	 (movitz:movitz-constantp position env)
	 (movitz:movitz-constantp integer env))
    (ldb (byte (movitz:movitz-eval size env)
	       (movitz:movitz-eval position env))
	 (movitz:movitz-eval integer env))) ; constant folding
   ((and (movitz:movitz-constantp size env)
	 (movitz:movitz-constantp position env))
    (let* ((size (movitz:movitz-eval size env))
	   (position (movitz:movitz-eval position env))
	   (result-type `(unsigned-byte ,size)))
      (cond
       ((or (minusp size) (minusp position))
	(error "Negative byte-spec for ldb."))
       ((= 0 size)
	`(progn ,integer 0))
       ((<= (+ size position) (- 31 movitz:+movitz-fixnum-shift+))
	`(with-inline-assembly (:returns :register
					 :type ,result-type)
	   (:compile-form (:result-mode :eax) ,integer)
	   (:call-global-pf unbox-u32)
	   (:andl ,(mask-field (byte size position) -1) :ecx)
	   ,@(unless (zerop position)
	       `((:shrl ,position :ecx)))
	   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) (:result-register))))
       ((<= (+ size position) 32)
	`(with-inline-assembly-case (:type ,result-type)
	   (do-case (t :eax :labels (nix done))
	     (:compile-form (:result-mode :eax) ,integer)
	     ,@(cond
		((and (= 0 position) (= 32 size))
		 ;; If integer is a positive bignum with one bigit, return it.
		 `((:leal (:eax ,(- (movitz:tag :other))) :ecx)
		   (:testb 7 :cl)
		   (:jnz 'nix)
		   (:cmpl ,(dpb 4 (byte 16 16) (movitz:tag :bignum 0))
			  (:eax ,movitz:+other-type-offset+))
		   (:je 'done)))
		((and (= 0 position) (<= (- 32 movitz:+movitz-fixnum-shift+) size ))
		 `((:leal (:eax ,(- (movitz:tag :other))) :ecx)
		   (:testb 7 :cl)
		   (:jnz 'nix)
		   (:cmpl ,(dpb 4 (byte 16 16) (movitz:tag :bignum 0))
			  (:eax ,movitz:+other-type-offset+))
		   (:jne 'nix)
		   (:movl (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0))
			  :ecx)
		   (:testl ,(logxor #xffffffff (mask-field (byte size 0) -1))
			   :ecx)
		   (:jz 'done)
		   (:andl ,(mask-field (byte size 0) -1)
			  :ecx)
		   (:call-local-pf box-u32-ecx)
		   (:jmp 'done))))
	    nix
	     (:call-global-pf unbox-u32)
	     ,@(unless (= 32 (- size position))
		 `((:andl ,(mask-field (byte size position) -1) :ecx)))
	     ,@(unless (zerop position)
		 `((:shrl ,position :ecx)))
	     (:call-local-pf box-u32-ecx)
	    done)))
       (t form))))
   (t form)))

(define-compiler-macro ldb (&whole form &environment env bytespec integer)
  (let ((bytespec (movitz-macroexpand bytespec env)))
    (if (not (and (consp bytespec) (eq 'byte (car bytespec))))
	form
      `(ldb%byte ,(second bytespec) ,(third bytespec) ,integer))))

(define-setf-expander ldb (bytespec int &environment env)
  "Stolen from the Hyperspec example in the define-setf-expander entry."
  (multiple-value-bind (temps vals stores store-form access-form)
      (get-setf-expansion int env)	;Get setf expansion for int.
    (let ((btemp (gensym))		;Temp var for byte specifier.
	  (store (gensym))		;Temp var for byte to store.
	  (stemp (first stores)))	;Temp var for int to store.
      (if (cdr stores) (error "Can't expand this."))
      ;; Return the setf expansion for LDB as five values.
      (values (cons btemp temps)	;Temporary variables.
	      (cons bytespec vals)	;Value forms.
	      (list store)		;Store variables.
	      `(let ((,stemp (dpb ,store ,btemp ,access-form)))
		 ,store-form
		 ,store)		;Storing form.
	      `(ldb ,btemp ,access-form) ;Accessing form.
              ))))

(define-compiler-macro expt (&whole form base-number power-number &environment env)
  (if (not (and (movitz:movitz-constantp base-number env)
		(movitz:movitz-constantp power-number env)))
      form
    (expt (movitz:movitz-eval base-number env)
	  (movitz:movitz-eval power-number env))))
    
(define-compiler-macro %bignum-compare (x y)
  "Set ZF and CF according to (:cmpl y x), disregarding sign."
  `(with-inline-assembly (:returns :nothing :labels (eax-shortest-loop
						     ebx-shortest-loop
						     equal-length-loop
						     done))
     (:compile-two-forms (:eax :ebx) ,x ,y)
     (:xorl :ecx :ecx)
     (:xorl :edx :edx)
     (:movw (:eax (:offset movitz-bignum length)) :cx)
     (:movw (:ebx (:offset movitz-bignum length)) :dx)
     (:cmpl :ecx :edx)
     (:je 'equal-length-loop)
     (:jnc 'eax-shortest-loop)
    ebx-shortest-loop
     (:cmpl 0 (:eax :ecx (:offset movitz-bignum bigit0 -4)))
     (:jne 'done)
     (:subl 4 :ecx)
     (:cmpl :edx :ecx)
     (:jne 'ebx-shortest-loop)
     (:jmp 'equal-length-loop)
    eax-shortest-loop
     (:cmpl 0 (:ebx :edx (:offset movitz-bignum bigit0 -4)))
     (:cmc)				; Complement CF
     (:jne 'done)
     (:subl 4 :edx)
     (:cmpl :edx :ecx)
     (:jne 'eax-shortest-loop)
    equal-length-loop			; Compare from EDX down
     (:subl 4 :edx)
     (:movl (:eax :edx (:offset movitz-bignum bigit0)) :ecx)
     (:cmpl (:ebx :edx (:offset movitz-bignum bigit0)) :ecx)
     (:jne 'done)
     (:testl :edx :edx)
     (:jnz 'equal-length-loop)
    done))

(define-compiler-macro %bignum< (x y)
  `(with-inline-assembly (:returns :boolean-below)
     (:compile-form (:result-mode :ignore) (%bignum-compare ,x ,y))))

(define-compiler-macro %bignum= (x y)
  `(with-inline-assembly (:returns :boolean-zf=1)
     (:compile-form (:result-mode :ignore) (%bignum-compare ,x ,y))))

(define-compiler-macro %bignum-zerop (x)
  `(with-inline-assembly (:returns :boolean-zf=1 :labels (zerop-loop zerop-loop-end))
     (:compile-form (:result-mode :eax) ,x)
     (:xorl :edx :edx)
     (:movw (:eax (:offset movitz-bignum length)) :dx)
     (:xorl :ecx :ecx)
    zerop-loop
     (:cmpl :ecx (:eax :edx (:offset movitz-bignum bigit0 -4)))
     (:jne 'zerop-loop-end)
     (:subl 4 :edx)
     (:jnz 'zerop-loop)
    zerop-loop-end))

(define-compiler-macro %bignum-negate (x)
  `(with-inline-assembly (:returns :register)
     (:compile-form (:result-mode :register) ,x)
     (:xorl #xff00 ((:result-register) (:offset movitz-bignum type)))))

(define-compiler-macro %bignum-plus-fixnum-size (x fixnum-delta)
  "Return 1 if fixnum delta can overflow x, otherwise 0."
  `(with-inline-assembly (:returns :eax :type (unsigned-byte 0 1)
				   :labels (check-hi-loop check-lsb done))
     (:compile-two-forms (:ebx :edx) ,x ,fixnum-delta)
     (:xorl :ecx :ecx)
     (:movw (:ebx (:offset movitz-bignum length)) :cx)
     (:movl :ecx :eax)
    check-hi-loop
     (:subl 4 :ecx)
     (:jz 'check-lsb)
     (:cmpl -1 (:ebx :ecx (:offset movitz-bignum bigit0)))
     (:jne 'done)
    check-lsb
     (:shrl ,movitz:+movitz-fixnum-shift+ :edx)
     (:addl (:ebx (:offset movitz-bignum bigit0)) :edx)
     (:jnc 'done)
     (:addl ,movitz:+movitz-fixnum-factor+ :eax)
    done))

(define-compiler-macro %ratio-numerator (x)
  `(memref ,x (movitz-type-slot-offset 'movitz-ratio 'numerator)))

(define-compiler-macro %ratio-denominator (x)
  `(memref ,x (movitz-type-slot-offset 'movitz-ratio 'denominator)))

;;;

(defmacro/cross-compilation define-number-relational (name 2op-name condition &key (defun-p t) 3op-name)
  `(progn
     ,(when condition
	`(define-compiler-macro ,2op-name (n1 n2 &environment env)
	   (cond
	    ((and (movitz:movitz-constantp n1 env)
		  (movitz:movitz-constantp n2 env))
             (if (funcall name (movitz:movitz-eval n1 env) (movitz:movitz-eval n2 env))
                 t nil))
            ((movitz:movitz-constantp n1 env)
	     (let ((n1 (movitz::movitz-eval n1 env)))
	       (check-type n1 number)
	       (if (typep n1 '(signed-byte 30))
		   `(with-inline-assembly (:returns ,,condition :side-effects nil)
		      (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		      (:call-global-pf fast-compare-fixnum-real))
		 `(with-inline-assembly (:returns ,,condition :side-effects nil)
		    (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		    (:call-global-pf fast-compare-two-reals)))))
	    ((movitz:movitz-constantp n2 env)
	     (let ((n2 (movitz:movitz-eval n2 env)))
	       (check-type n2 number)
	       (if (typep n2 '(signed-byte 30))
		   `(with-inline-assembly (:returns ,,condition :side-effects nil)
		      (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		      (:call-global-pf fast-compare-real-fixnum))
		 `(with-inline-assembly (:returns ,,condition :side-effects nil)
		    (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		    (:call-global-pf fast-compare-two-reals)))))
	    (t `(with-inline-assembly (:returns ,,condition :side-effects nil)
		  (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		  (:call-global-pf fast-compare-two-reals))))))

     (defun ,2op-name (n1 n2)
       (,2op-name n1 n2))

     (define-compiler-macro ,name (&whole form number &rest more-numbers)
       (case (length more-numbers)
	 (0 `(progn ,number t))
	 (1 `(,',2op-name ,number ,(first more-numbers)))
	 ,@(when 3op-name
	     `((2 `(,',3op-name ,number ,(first more-numbers) ,(second more-numbers)))))
	 (t #+ignore (when (= 2 (length more-numbers))
		       (warn "3op: ~S" form))
	  `(and (,',2op-name ,number ,(first more-numbers))
		  (,',name ,@more-numbers)))))

     ,(when defun-p
	`(defun ,name (number &rest more-numbers)
	   (declare (dynamic-extent more-numbers))
	   (cond
	    ((null more-numbers)
	     (check-type number fixnum)
	     t)
	    ((not (cdr more-numbers))
	     (,2op-name number (first more-numbers)))
	    (t (and (,2op-name number (first more-numbers))
		    (do ((p more-numbers (cdr p)))
			((not (cdr p)) t)
		      (unless (,2op-name (car p) (cadr p))
			(return nil))))))))))

(define-number-relational >= >=%2op :boolean-greater-equal)
(define-number-relational > >%2op :boolean-greater)
(define-number-relational < <%2op :boolean-less)
(define-number-relational <= <=%2op :boolean-less-equal :3op-name <=%3op)

;;; Types

(define-typep integer (x &optional (min '*) (max '*))
  (and (typep x 'integer)
       (or (eq min '*) (<= min x))
       (or (eq max '*) (<= x max))))

(deftype unsigned-byte (&optional (size '*))
  (cond
   ((eq size '*)
    '(integer 0))
   ((typep size '(integer 1 *))
    ;; The funcall is a hack not to invoke compiler machinery
    ;; that depends on the unsigned-byte type being defined.
    (list 'integer 0 (funcall '- (ash 1 size) 1)))
   (t (error "Illegal size for unsigned-byte."))))

(deftype signed-byte (&optional (size '*))
  (cond
   ((eq size '*)
    'integer)
   ((typep size '(integer 1 *))
    (list 'integer
	  (- (ash 1 (1- size)))
	  (1- (ash 1 (1- size)))))
   (t (error "Illegal size for signed-byte."))))

(define-typep rational (x &optional (lower-limit '*) (upper-limit '*))
  (and (typep x 'rational)
       (or (eq lower-limit '*)
	   (<= lower-limit x))
       (or (eq upper-limit '*)
	   (<= x upper-limit))))

(deftype real (&optional (lower-limit '*) (upper-limit '*))
  `(or (integer ,lower-limit ,upper-limit)
       (rational ,lower-limit ,upper-limit)))

(deftype number (&optional (lower-limit '*) (upper-limit '*))
  `(real ,lower-limit ,upper-limit))

(define-simple-typep (bit bitp) (x)
  (or (eq x 0) (eq x 1)))

(deftype index (&optional (step 1))
  `(integer 0 ,(- #x1fffffff step)))
