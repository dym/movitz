;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      integers.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov  8 18:44:57 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: integers.lisp,v 1.21 2004/06/06 10:24:29 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(provide :muerte/integers)

(in-package muerte)

(defconstant most-positive-fixnum #.movitz::+movitz-most-positive-fixnum+)
(defconstant most-negative-fixnum #.movitz::+movitz-most-negative-fixnum+)

(deftype positive-fixnum ()
  `(integer 0 ,movitz:+movitz-most-positive-fixnum+))

(deftype positive-bignum ()
  `(integer ,(1+ movitz:+movitz-most-positive-fixnum+) *))

(defmacro number-double-dispatch ((x y) &rest clauses)
  `(let ((x ,x) (y ,y))
     (cond ,@(loop for ((x-type y-type) . then-body) in clauses
		 collect `((and (typep x ',x-type) (typep y ',y-type))
			   ,@then-body))
	   (t (error "Not numbers: ~S or ~S." x y)))))

(defun fixnump (x)
  (typep x 'fixnum))

(defun evenp (x)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :ebx)
	    (:compile-form (:result-mode :eax) x)
	    (:movl :eax :ecx)
	    (:andl 7 :ecx)
	    (:globally (:movl (:edi (:edi-offset t-symbol)) :ebx))
	    (:cmpl ,(movitz:tag :even-fixnum) :ecx)
	    (:je 'done)
	    (:movl :edi :ebx)
	    (:cmpl ,(movitz:tag :odd-fixnum) :ecx)
	    (:je 'done)
	    (:cmpl ,(movitz:tag :other) :ecx)
	    (:jnz '(:sub-program (not-integer)
		    (:int 107)))
	    (:cmpb ,(movitz:tag :bignum) (:eax ,movitz:+other-type-offset+))
	    (:jne 'not-integer)
	    (:testb 1 (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
	    (:jnz 'done)
	    (:globally (:movl (:edi (:edi-offset t-symbol)) :ebx))
	   done)))
    (do-it)))

(defun oddp (x)
  (not (evenp x)))

;;; Addition

(define-compiler-macro + (&whole form &rest operands &environment env)
  (case (length operands)
    (0 0)
    (1 (first operands))
    (2 `(+%2op ,(first operands) ,(second operands)))
    (t (let ((operands
	      (loop for operand in operands
		  if (movitz:movitz-constantp operand env)
		  sum (movitz:movitz-eval operand env)
		  into constant-term
		  else collect operand
		  into non-constant-operands
		  finally (return (if (zerop constant-term)
				      non-constant-operands
				    (cons constant-term non-constant-operands))))))
	 `(+ (+%2op ,(first operands) ,(second operands)) ,@(cddr operands))))))

(defun + (&rest terms)
  (numargs-case
   (1 (x) x)
   (2 (x y)
      (macrolet
	  ((do-it ()
	     `(number-double-dispatch (x y)
		((fixnum fixnum)
		 (with-inline-assembly (:returns :eax)
		   (:compile-form (:result-mode :eax) x)
		   (:compile-form (:result-mode :ebx) y)
		   (:addl :ebx :eax)
		   (:jo '(:sub-program (fix-fix-overflow)
			  (:movl :eax :ecx)
			  (:jns 'fix-fix-negative)
			  (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
			  (:call-global-constant box-u32-ecx)
			  (:jmp 'fix-fix-ok)
			  fix-fix-negative
			  (:jz 'fix-double-negative)
			  (:negl :ecx)
			  (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
			  (:call-global-constant box-u32-ecx)
			  (:movl ,(dpb 1 (byte 16 16)
				   (movitz:tag :bignum #xff))
			   (:eax ,movitz:+other-type-offset+))
			  (:jmp 'fix-fix-ok)
			  fix-double-negative
			  (:compile-form (:result-mode :eax)
			   ,(* 2 movitz:+movitz-most-negative-fixnum+))
			  (:jmp 'fix-fix-ok)))
		  fix-fix-ok))
		((positive-bignum positive-fixnum)
		 (funcall '+ y x))
		((positive-fixnum positive-bignum)
		 (with-inline-assembly (:returns :eax)
		   (:compile-two-forms (:eax :ebx) y x)
		   (:testl :ebx :ebx)
		   (:jz 'pfix-pbig-done)
		   (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)) :ecx)
		   (:cmpl 1 :ecx)
		   (:jne 'not-size1)
		   (:compile-form (:result-mode :ecx) x)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:addl (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)) :ecx)
		   (:jc 'retry-not-size1)
		   (:call-global-constant box-u32-ecx)
		   (:jmp 'pfix-pbig-done)
		  retry-not-size1
		   (:compile-form (:result-mode :eax) y)
		   (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)) :ecx)
		  not-size1
		   (:declare-label-set retry-jumper (retry-not-size1))
		   (:locally (:movl :esp (:edi (:edi-offset atomically-esp))))
		   (:locally (:movl '(:funcall ,(movitz::atomically-status-jumper-fn t :esp)
				      'retry-jumper)
				    (:edi (:edi-offset atomically-status))))
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+) ,(* 2 movitz:+movitz-fixnum-factor+))
			  :eax)		; Number of words
		   (:call-global-constant get-cons-pointer)
		   (:load-lexical (:lexical-binding y) :ebx) ; bignum
		   (:movzxw (:ebx ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)) :ecx)
		   (:leal ((:ecx #.movitz:+movitz-fixnum-factor+) ,movitz:+movitz-fixnum-factor+)
			  :edx)
		   (:movl 0 (:eax :edx ,movitz:+other-type-offset+)) ; MSB
		  copy-bignum-loop
		   (:subl ,movitz:+movitz-fixnum-factor+ :edx)
		   (:movl (:ebx :edx ,movitz:+other-type-offset+) :ecx)
		   (:movl :ecx (:eax :edx ,movitz:+other-type-offset+))
		   (:jnz 'copy-bignum-loop)

		   (:load-lexical (:lexical-binding x) :ecx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :ecx)
		   (:xorl :ebx :ebx)
		   (:addl :ecx (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
		   (:jnc 'add-bignum-done)
		  add-bignum-loop
		   (:addl 4 :ebx)
		   (:addl 1 (:eax :ebx ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
		   (:jc 'add-bignum-loop)
		  add-bignum-done
		   (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::length))
			    :ecx)
		   (:leal ((:ecx ,movitz:+movitz-fixnum-factor+) ,movitz:+movitz-fixnum-factor+)
			  :ecx)
		   (:cmpl 0 (:eax :ecx ,(+ -4 (bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0))))
		   (:je 'no-expansion)
		   (:addl #x10000 (:eax ,movitz:+other-type-offset+))
		   (:addl ,movitz:+movitz-fixnum-factor+ :ecx)
		  no-expansion
		   (:call-global-constant cons-commit)
		   (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
				    (:edi (:edi-offset atomically-status))))
		   
		  pfix-pbig-done))
		)))
	(do-it)))
   (t (&rest terms)
      (declare (dynamic-extent terms))
      (if (null terms)
	  0
	(reduce #'+ terms)))))

(defun 1+ (number)
  (+ 1 number))

(define-compiler-macro 1+ (number)
  `(+ 1 ,number))

(defun 1- (number)
  (+ -1 number))

(define-compiler-macro 1- (number)
  `(+ -1 ,number))

(define-modify-macro incf (&optional (delta-form 1)) +)

;;; Subtraction

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

(defun - (minuend &rest subtrahends)
  (declare (dynamic-extent subtrahends))
  (numargs-case
   (1 (x)
      (macrolet
	  ((do-it ()
	     `(with-inline-assembly (:returns :eax)
		(:compile-form (:result-mode :eax) x)
		(:testb ,movitz:+movitz-fixnum-zmask+ :al)
		(:jnz '(:sub-program (not-fixnum)
			(:leal (:eax ,(- (movitz:tag :other))) :ecx)
			(:testb 7 :cl)
			(:jnz '(:sub-program (not-a-number)
				(:compile-form (:result-mode :ignore)
				 (error 'type-error :expected-type 'number :datum x))))
			(:movl (:eax ,movitz:+other-type-offset+) :ecx)
			(:cmpb ,(movitz:tag :bignum) :cl)
			(:jne 'not-a-number)
			(:cmpl ,(dpb 1 (byte 16 16) (movitz:tag :bignum 0)) :ecx)
			(:jne 'not-most-negative-fixnum)
			(:cmpl ,(- most-negative-fixnum)
			 (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
			(:jne 'not-most-negative-fixnum)
			(:movl ,(ldb (byte 32 0)
				 (* most-negative-fixnum movitz::+movitz-fixnum-factor+))
			 :eax)
			(:jmp 'fix-ok)
			not-most-negative-fixnum
			(:compile-form (:result-mode :eax)
			 (copy-bignum x))
			(:notb (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::sign)))
			(:jmp 'fix-ok)))
		(:negl :eax)
		(:jo '(:sub-program (fix-overflow)
		       (:compile-form (:result-mode :eax)
			,(1+ movitz:+movitz-most-positive-fixnum+))
		       (:jmp 'fix-ok)))
	       fix-ok
		)))
	(do-it)))
   (2 (minuend subtrahend)
      (cond
       ((eq 0 minuend)
	(- subtrahend))
       (t (check-type minuend fixnum)
	  (check-type subtrahend fixnum)
	  (with-inline-assembly (:returns :eax :side-effects nil)
	    (:compile-two-forms (:eax :ebx) minuend subtrahend)
	    (:subl :ebx :eax)
	    (:into)))))
   (t (minuend &rest subtrahends)
      (declare (dynamic-extent subtrahends))
      (if subtrahends
	  (reduce #'- subtrahends :initial-value minuend)
	(- 0 minuend)))))
    
(define-modify-macro decf (&optional (delta-form 1)) -)

;;; Comparison

(define-primitive-function fast-compare-two-reals (n1 n2)
  "Check that n1 and n2 are fixnums, and compare them."
  (with-inline-assembly (:returns :nothing) ; unspecified
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program ()
	    (:int 107)
	    (:jmp (:pc+ -4))))
    (:testb #.movitz::+movitz-fixnum-zmask+ :bl)
    (:jnz '(:sub-program ()
	    (:movl :ebx :eax)
	    (:int 107)
	    (:jmp (:pc+ -4))))
    (:cmpl :ebx :eax)
    (:ret)))

(define-primitive-function fast-compare-fixnum-real (n1 n2)
  "Compare (known) fixnum <n1> with real <n2>."
  (with-inline-assembly (:returns :nothing) ; unspecified
    (:testb #.movitz::+movitz-fixnum-zmask+ :bl)
    (:jnz '(:sub-program (not-integer)
	    (:movl :ebx :eax)
	    (:int 107)
	    (:jmp 'not-integer)))
    (:cmpl :ebx :eax)
    (:ret)))

(define-primitive-function fast-compare-real-fixnum (n1 n2)
  "Compare real <n1> with fixnum <n2>."
  (with-inline-assembly (:returns :nothing) ; unspecified
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz 'not-fixnum)
    (:cmpl :ebx :eax)
    (:ret)
   not-fixnum
    (:leal (:eax #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jnz '(:sub-program (not-integer)
	    (:int 107)
	    (:jmp 'not-integer)))
    (:movl (:eax #.movitz:+other-type-offset+) :ecx)
    (:cmpw #.(movitz:tag :bignum 0) :cx)
    (:jne 'not-plusbignum)
    ;; compare ebx with something bigger
    (:cmpl #x-10000000 :edi)
    (:ret)
   not-plusbignum
    (:cmpw #.(movitz:tag :bignum #xff) :cx)
    (:jne 'not-integer)
    ;; compare ebx with something bigger
    (:cmpl #x10000000 :edi)
    (:ret)))

;;;

(define-compiler-macro <=%3op (min x max &environment env)
  (cond
   ((and (movitz:movitz-constantp min env)
	 (movitz:movitz-constantp max env))
    (let ((min (movitz:movitz-eval min env))
	  (max (movitz:movitz-eval max env)))
      (check-type min fixnum)
      (check-type max fixnum)
      ;; (warn "~D -- ~D" min max)
      (cond
       ((movitz:movitz-constantp x env)
	(<= min (movitz:movitz-eval x env) max))
       ((< max min)
	nil)
       ((= max min)
	`(= ,x ,min))
       ((minusp min)
	`(let ((x ,x))
	   (and (<= ,min x) (<= x ,max))))
       ((= 0 min)
	`(with-inline-assembly (:returns :boolean-cf=1)
	   (:compile-form (:result-mode :eax) ,x)
	   (:testb ,movitz::+movitz-fixnum-zmask+ :al)
	   (:jnz '(:sub-program () (:int 107)))
	   (:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)))
       (t `(do-result-mode-case ()
	     (:booleans
	      (with-inline-assembly (:returns :boolean-zf=0)
		(:compile-form (:result-mode :eax) ,x)
		(:testb ,movitz::+movitz-fixnum-zmask+ :al)
		(:jnz '(:sub-program () (:int 107)))
		(:cmpl ,(* min movitz::+movitz-fixnum-factor+) :eax)
		(:sbbl :ecx :ecx)
		(:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)
		(:adcl 0 :ecx)))
	     (t (with-inline-assembly (:returns (:boolean-ecx 1 0))
		  (:compile-form (:result-mode :eax) ,x)
		  (:testb ,movitz::+movitz-fixnum-zmask+ :al)
		  (:jnz '(:sub-program () (:int 107)))
		  (:cmpl ,(* min movitz::+movitz-fixnum-factor+) :eax)
		  (:sbbl :ecx :ecx)
		  (:cmpl ,(* (1+ max) movitz::+movitz-fixnum-factor+) :eax)
		  (:adcl 0 :ecx))))))))
   #+ignore				; this is buggy.
   ((movitz:movitz-constantp min env)
    (let ((min (movitz:movitz-eval min env)))
      (check-type min fixnum)
      (cond
       ((minusp min)
	`(let ((x ,x))
	   (and (<= ,min x) (<= x ,max))))
       (t `(do-result-mode-case ()
	     (:booleans
	      (with-inline-assembly (:returns :boolean-zf=1)
		(:compile-two-forms (:eax :ebx) ,x ,max)
		(:movl :eax :ecx)
		(:orl :ebx :ecx)
		(:testb ,movitz::+movitz-fixnum-zmask+ :cl)
		(:jne '(:sub-program () (:int 107)))
		(:cmpl :eax :ebx)
		(:sbbl :ecx :ecx)
		,@(unless (= 0 min)
		    `((:subl ,(* min movitz::+movitz-fixnum-factor+) :ebx)))
		(:addl :ebx :ebx)
		(:adcl 0 :ecx)))
	     (t (with-inline-assembly (:returns (:boolean-ecx 0 1))
		  (:compile-two-forms (:eax :ebx) ,x ,max)
		  (:movl :eax :ecx)
		  (:orl :ebx :ecx)
		  (:testb ,movitz::+movitz-fixnum-zmask+ :cl)
		  (:jne '(:sub-program () (:int 107)))
		  (:cmpl :eax :ebx)	; if x>max, CF=1
		  (:sbbl :ecx :ecx)	; ecx = x>max ? -1 : 0
		  ,@(unless (= 0 min)
		      `((:subl ,(* min movitz::+movitz-fixnum-factor+) :ebx)))
		  (:addl :ebx :ebx)	; if x<min, CF=1
		  (:adcl 0 :ecx)	; 
		  (:andl 1 :ecx))))))))
   (t `(let ((x ,x))
	 (and (<= ,min x) (<= x ,max))))))
       

(defmacro define-number-relational (name 2op-name condition &key (defun-p t) 3op-name)
  `(progn
     ,(when condition
	`(define-compiler-macro ,2op-name (n1 n2)
	   (cond
	    ((movitz:movitz-constantp n1)
	     (let ((n1 (movitz::movitz-eval n1)))
	       (check-type n1 (signed-byte 30))
	       `(with-inline-assembly (:returns ,,condition :side-effects nil)
		  (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		  (:call-global-constant fast-compare-fixnum-real))))
	    ((movitz:movitz-constantp n2)
	     (let ((n2 (movitz::movitz-eval n2)))
	       (check-type n2 (signed-byte 30))
	       `(with-inline-assembly (:returns ,,condition :side-effects nil)
		  (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		  (:call-global-constant fast-compare-real-fixnum))))
	    (t `(with-inline-assembly (:returns ,,condition :side-effects nil)
		  (:compile-two-forms (:eax :ebx) ,n1 ,n2)
		  (:call-global-constant fast-compare-two-reals))))))

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

;;; Unsigned

(define-compiler-macro below (&whole form x max &environment env)
  (let ((below-not-integer (gensym "below-not-integer-")))
    (if (movitz:movitz-constantp max env)
	`(with-inline-assembly (:returns :boolean-cf=1)
	   (:compile-form (:result-mode :eax) ,x)
	   (:testb ,movitz::+movitz-fixnum-zmask+ :al)
	   (:jnz '(:sub-program (,below-not-integer) (:int 107)))
	   (:cmpl ,(* (movitz:movitz-eval max env)
		      movitz::+movitz-fixnum-factor+)
		  :eax))
      `(with-inline-assembly (:returns :boolean-cf=1)
	 (:compile-two-forms (:eax :ebx) ,x ,max)
	 (:movl :eax :ecx)
	 (:orl :ebx :ecx)
	 (:testb ,movitz::+movitz-fixnum-zmask+ :cl)
	 (:jnz '(:sub-program (,below-not-integer) (:int 107)))
	 (:cmpl :ebx :eax)))))

(defun below (x max)
  "Is x between 0 and max?"
  (below x max))


;;; Equality

(define-compiler-macro =%2op (n1 n2 &environment env)
  (cond
   ((movitz:movitz-constantp n1 env)
    (let ((n1 (movitz::movitz-eval n1 env)))
      (etypecase n1
	((eql 0)
	 `(do-result-mode-case ()
	    (:booleans
	     (with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	       (:compile-form (:result-mode :eax) ,n2)
	       (:testl :eax :eax)))
	    (t (with-inline-assembly (:returns :boolean-cf=1 :side-effects nil)
		 (:compile-form (:result-mode :eax) ,n2)
		 (:cmpl 1 :eax)))))
	((signed-byte 30)
	 `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	    (:compile-two-forms (:eax :ebx) ,n1 ,n2)
	    (:call-global-constant fast-compare-fixnum-real))))))
   ((movitz:movitz-constantp n2 env)
    (let ((n2 (movitz::movitz-eval n2 env)))
      (check-type n2 (signed-byte 30))
      `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	 (:compile-two-forms (:eax :ebx) ,n1 ,n2)
	 (:call-global-constant fast-compare-real-fixnum))))
   (t `(with-inline-assembly (:returns :boolean-zf=1 :side-effects nil)
	 (:compile-two-forms (:eax :ebx) ,n1 ,n2)
	 (:call-global-constant fast-compare-two-reals)))))

(define-number-relational = =%2op nil :defun-p nil)

(defun = (first-number &rest numbers)
  (declare (dynamic-extent numbers))
  (check-type first-number fixnum)
  (dolist (n numbers t)
    (unless (= first-number n)
      (return nil))))

(define-number-relational /= /=%2op :boolean-zf=0 :defun-p nil)

(defun /= (&rest numbers)
  (declare (dynamic-extent numbers))
  (do ((p (cdr numbers) (cdr p)))
      ((null p) t)
    (do ((v numbers (cdr v)))
	((eq p v))
      (when (= (car p) (car v))
	(return-from /= nil)))))

;;;

(defun zerop (number)
  (= 0 number))

(define-compiler-macro zerop (number)
  `(= 0 ,number))

(defun plusp (number)
  (> number 0))

(define-compiler-macro plusp (number)
  `(> ,number 0))

(defun minusp (number)
  (< number 0))

(define-compiler-macro minusp (number)
  `(< ,number 0))

(define-compiler-macro abs (x)
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,x)
     (:testb #.movitz::+movitz-fixnum-zmask+ :al)
     (:jnz '(:sub-program () (:int 107)))
     (:movl :eax :ecx)
     (:addl :ecx :ecx)
     (:sbbl :ecx :ecx)
     (:xorl :ecx :eax)
     (:subl :ecx :eax)))

(defun abs (x)
  (abs x))

(defun signum (x)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) x)
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program (not-fixnum) (:int 107)))
    (:cdq :eax :edx)
    (:negl :eax)
    (:adcl :edx :edx)
    (:leal ((:edx #.movitz::+movitz-fixnum-factor+)) :eax)))

;;;

(define-compiler-macro max%2op (number1 number2)
  #+ignore
  `(let ((number1 ,number1) (number2 ,number2))
     (if (< number1 number2)
	 number2 number1))
  (let ((label (gensym)))
    `(with-inline-assembly (:returns :eax :type fixnum)
       (:compile-two-forms (:eax :ebx) ,number1 ,number2)
       (:movl :ebx :ecx)
       (:orl :eax :ecx)
       (:testb ,movitz::+movitz-fixnum-zmask+ :cl)
       (:jnz '(:sub-program () (:int 107)))
       (:cmpl :eax :ebx)
       (:jl ',label)
       (:movl :ebx :eax)
       ,label)))
    

(defun max%2op (number1 number2)
  (max%2op number1 number2))

(define-compiler-macro max (&whole form first-number &rest more-numbers)
  (case (length more-numbers)
    (0 first-number)
    (1 `(max%2op ,first-number ,(car more-numbers)))
    ((2 3 4)
     `(max%2op ,first-number (max ,@more-numbers)))
    (t form)))

(defun max (number1 &rest numbers)
  (declare (dynamic-extent numbers))
  (let ((max number1))
    (dolist (x numbers max)
      (when (>= x max)
	(setq max x)))))

(define-compiler-macro min%2op (number1 number2)
  `(let ((number1 ,number1) (number2 ,number2))
     (if (< number1 number2)
	 number1 number2)))

(defun min%2op (number1 number2)
  (min%2op number1 number2))

(define-compiler-macro min (&whole form first-number &rest more-numbers)
  (case (length more-numbers)
    (0 first-number)
    (1 `(min%2op ,first-number ,(car more-numbers)))
    ((2 3 4)
     `(min%2op ,first-number (min ,@more-numbers)))
    (t form)))

(defun min (number1 &rest numbers)
  (declare (dynamic-extent numbers))
  #+ignore (reduce #'min%2op numbers :initial-value number1)
  (let ((min number1))
    (dolist (x numbers min)
      (when (< x min)
	(setq min x)))))

;; shift 

(define-compiler-macro ash (&whole form integer count &environment env)
  (if (not (movitz:movitz-constantp count env))
      form
    (let ((count (movitz::movitz-eval count env)))
      (cond
       ((movitz:movitz-constantp integer env)
	(ash (movitz::movitz-eval integer env) count))
       ((= 0 count)
	integer)
       (t (let ((load-integer `((:compile-form (:result-mode :register) ,integer)
				(:testb ,movitz::+movitz-fixnum-zmask+ (:result-register-low8))
				(:jnz '(:sub-program () (:int 107) (:jmp (:pc+ -4)))))))
	    (cond
	     ((<= 1 count 4)
	      `(with-inline-assembly (:returns :register :side-effects nil)
		 ,@load-integer
		 ,@(loop repeat count
		       append `((:addl (:result-register) (:result-register))
				(:into)))))
	     ((< 0 count #.(cl:1- movitz::+movitz-fixnum-bits+))
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
	     (t `(if (= 0 ,integer) 0 (with-inline-assembly (:returns :non-local-exit) (:int 4)))))))))))

(defun ash (integer count)
  (check-type integer fixnum)
  (check-type count fixnum)
  (cond
   ((= 0 count)
    integer)
   ((<= 1 count 29)
    (dotimes (i count integer)
      (setq integer (ash integer 1))))
   ((<= count #.(cl:- 1 movitz::+movitz-fixnum-bits+))
    (if (minusp integer) -1 0))
   ((minusp count)
    (with-inline-assembly (:returns :eax)
      (:compile-form (:result-mode :ecx) count)
      (:compile-form (:result-mode :eax) integer)
      (:negl :ecx)
      (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
      (:sarl :cl :eax)
      (:andb #.(cl:logxor #xff movitz::+movitz-fixnum-zmask+) :al)))
   (t (if (= 0 integer) 0 (error "Illegal ash count: ~D" count)))))

;;; Multiplication

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
	     (check-type f1 fixnum)
	     (case f1
	       (0 `(progn ,factor2 0))
	       (1 factor2)
	       (2 `(ash ,factor2 1))
	       (t `(with-inline-assembly (:returns :eax :type integer)
		     (:compile-form (:result-mode :eax) ,factor2)
		     (:testb #.movitz::+movitz-fixnum-zmask+ :al)
		     (:jnz '(:sub-program () (:int 107)))
		     (:imull ,f1 :eax :eax)
		     (:into))))))
	  (t `(no-macro-call * ,factor1 ,factor2)))))
    (t `(* (* ,(first operands) ,(second operands)) ,@(cddr operands)))))

(defun * (&rest factors)
  (numargs-case
   (1 (x) x)
   (2 (x y)
      (with-inline-assembly (:returns :eax)
	(:compile-form (:result-mode :eax) x)
	(:compile-form (:result-mode :ebx) y)
	(:movl :eax :ecx)
	(:orl :ebx :ecx)
	(:testb #.movitz::+movitz-fixnum-zmask+ :cl)
	(:jne '(:sub-program (not-fixnum)
		(:int 107)))
	(:movl :ebx :ecx)
	(:sarl #.movitz::+movitz-fixnum-shift+ :ecx)
	(:imull :ecx :eax :edx)
	(:into)))
   (t (&rest factors)
      (declare (dynamic-extent factors))
      (if (null factors)
	  1
	(reduce '* factors)))))

;;; Division

(define-compiler-macro truncate (&whole form number &optional (divisor 1))
  `(do-result-mode-case ()
     (:plural
      (no-macro-call ,@form))
     (t (truncate%1ret ,number ,divisor))))

(defun truncate%1ret (number divisor)
  (with-inline-assembly (:returns :multiple-values)
    (:compile-form (:result-mode :eax) number)
    (:compile-form (:result-mode :ebx) divisor)
    (:movl :eax :ecx)
    (:orl :ebx :ecx)
    (:testb #.movitz::+movitz-fixnum-zmask+ :cl)
    (:jnz '(:sub-program (not-integer) (:int 107)))
    (:cdq :eax :edx)
    (:idivl :ebx :eax :edx)
    (:shll #.movitz::+movitz-fixnum-shift+ :eax)
    (:clc)))

(define-compiler-macro truncate%1ret (&whole form &environment env number divisor)
  (cond
   ((movitz:movitz-constantp divisor env)
    (let ((d (movitz:movitz-eval divisor env)))
      (check-type d number)
      (case d
	(0 (error "Truncate by zero."))
	(1 number)
	(t `(with-inline-assembly (:returns :eax :type fixnum)
	      (:compile-form (:result-mode :eax) ,number)
	      (:compile-form (:result-mode :ebx) ,divisor)
	      (:testb #.movitz::+movitz-fixnum-zmask+ :al)
	      (:jnz '(:sub-program () (:int 66)))
	      (:cdq :eax :edx)
	      (:idivl :ebx :eax :edx)
	      (:shll #.movitz::+movitz-fixnum-shift+ :eax))))))
   (t form)))

(defun truncate (number &optional (divisor 1))
  (numargs-case
   (1 (number)
      (values number 0))
   (t (number divisor)
      (number-double-dispatch (number divisor)
	((fixnum fixnum)
	 (with-inline-assembly (:returns :multiple-values)
	   (:compile-form (:result-mode :eax) number)
	   (:compile-form (:result-mode :ebx) divisor)
	   (:std)
	   (:cdq :eax :edx)
	   (:idivl :ebx :eax :edx)
	   (:shll #.movitz::+movitz-fixnum-shift+ :eax)
	   (:cld)
	   (:movl :edx :ebx)
	   (:xorl :ecx :ecx)
	   (:movb 2 :cl)		; return values: qutient, remainder.
	   (:stc)))
	((positive-bignum positive-fixnum)
	 (macrolet
	     ((do-it ()
		`(let (r n)
		   (with-inline-assembly (:returns :multiple-values)
		     (:compile-form (:result-mode :ebx) number)
		     (:cmpw 1 (:ebx #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)))
		     (:jne 'not-size1)
		     (:compile-form (:result-mode :ecx) divisor)
		     (:shrl #.movitz:+movitz-fixnum-shift+ :ecx)
		     (:std)
		     (:movl (:ebx #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)) :eax)
		     (:xorl :edx :edx)
		     (:divl :ecx :eax :edx)
		     (:movl :eax :ecx)
		     (:shll #.movitz:+movitz-fixnum-shift+ :edx)
		     (:movl :edi :eax)
		     (:cld)
		     (:pushl :edx)
		     (:call-global-constant box-u32-ecx)
		     (:popl :ebx)
		     (:jmp 'done)
		    not-size1
		     (:compile-form (:result-mode :ebx) number)
		     (:movzxw (:ebx #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::length))
			      :ecx)
	     
		     (:declare-label-set retry-jumper (not-size1))
		     (:locally (:movl :esp (:edi (:edi-offset atomically-esp))))
		     (:locally (:movl '(:funcall ,(movitz::atomically-status-jumper-fn t :esp)
					'retry-jumper)
				      (:edi (:edi-offset atomically-status))))

		     (:leal ((:ecx #.movitz:+movitz-fixnum-factor+) #.movitz:+movitz-fixnum-factor+)
			    :eax)	; Number of words
		     (:call-global-constant get-cons-pointer) ; New bignum into EAX


		     (:store-lexical (:lexical-binding r) :eax :type bignum)
		     (:compile-form (:result-mode :ebx) number)
		     (:movl (:ebx #.movitz:+other-type-offset+) :ecx)
		     (:movl :ecx (:eax #.movitz:+other-type-offset+))
		     (:shrl 16 :ecx)
	     
		     (:xorl :edx :edx)	; edx=hi-digit=0
					; eax=lo-digit=msd(number)
		     (:std)
		     (:compile-form (:result-mode :esi) divisor)
		     (:shrl #.movitz:+movitz-fixnum-shift+ :esi)

		    divide-loop
		     (:load-lexical (:lexical-binding number) :ebx)
		     (:movl (:ebx #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)
				  -4 (:ecx 4))
			    :eax)
		     (:divl :esi :eax :edx)
		     (:load-lexical (:lexical-binding r) :ebx)
		     (:movl :eax (:ebx #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)
				       -4 (:ecx 4)))
		     (:subl 1 :ecx)
		     (:jnz 'divide-loop)
		     (:movl :edi :eax)	; safe value
		     (:leal ((:edx ,movitz:+movitz-fixnum-factor+)) :edx)
		     (:movl (:ebp -4) :esi)
		     (:cld)
		     (:movl :ebx :eax)
		     (:movl :edx :ebx)

		     (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::length))
			      :ecx)
		     (:leal ((:ecx ,movitz:+movitz-fixnum-factor+) #.movitz:+movitz-fixnum-factor+)
			    :ecx)
		     (:cmpl 0 (:eax :ecx ,(+ -8 (bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0))))
		     (:jne 'no-more-shrinkage)
		     
		     (:subw 1 (:eax #.(bt:slot-offset 'movitz::movitz-bignum 'movitz::length)))
		     (:subl ,movitz:+movitz-fixnum-factor+ :ecx)
		     (:cmpl ,(* 2 movitz:+movitz-fixnum-factor+) :ecx)
		     (:jne 'no-more-shrinkage)
		     (:cmpl ,movitz:+movitz-most-positive-fixnum+
			    (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0)))
		     (:jnc 'no-more-shrinkage)
		     (:movl (:eax ,(bt:slot-offset 'movitz::movitz-bignum 'movitz::bigit0))
			    :ecx)
		     (:leal ((:ecx ,movitz:+movitz-fixnum-factor+)) :eax)
		     (:jmp 'fixnum-result) ; don't commit the bignum
		    no-more-shrinkage
		     (:call-global-constant cons-commit)
		    fixnum-result
		     (:locally (:movl ,(bt:enum-value 'movitz::atomically-status :inactive)
				      (:edi (:edi-offset atomically-status))))	     
		    done
		     (:movl 2 :ecx)
		     (:stc)))))
	   (do-it)))
	))))

(defun round (number &optional (divisor 1))
  "Mathematical rounding."
  (multiple-value-bind (quotient remainder)
      (truncate number divisor)
    (let ((rem2 (* 2 remainder)))
      (case (+ (if (minusp number) #b10 0)
	       (if (minusp divisor) #b01 0))
	(#b00 (cond
	       ((= divisor rem2)
		(if (evenp quotient)
		    (values quotient remainder)
		  (values (1+ quotient) (- remainder divisor))))
	       ((< rem2 divisor)
		(values quotient remainder))
	       (t (values (1+ quotient) (- remainder divisor)))))
	(#b11 (cond
	       ((= divisor rem2)
		(if (evenp quotient)
		    (values quotient remainder)
		  (values (1+ quotient) (- remainder divisor))))
	       ((> rem2 divisor)
		(values quotient remainder))
	       (t (values (1+ quotient) (- remainder divisor)))))
	(#b10 (cond
	       ((= (- divisor) rem2)
		(if (evenp quotient)
		    (values quotient remainder)
		  (values (1- quotient) (- remainder))))
	       ((< rem2 divisor)
		(values quotient remainder))
	       (t (values (1+ quotient) (- remainder divisor)))))
	(#b01 (cond
	       ((= (- divisor) rem2)
		(if (evenp quotient)
		    (values quotient remainder)
		  (values (1- quotient) (- remainder))))
	       ((> rem2 divisor)
		(values quotient remainder))
	       (t (values (1- quotient) (- remainder)))))))))

(defun rem (dividend divisor)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) dividend)
    (:compile-form (:result-mode :ebx) divisor)
    (:movl :eax :ecx)
    (:orl :ebx :ecx)
    (:testb #.movitz::+movitz-fixnum-zmask+ :cl)
    (:jnz '(:sub-program (not-integer) (:int 107)))
    (:cdq :eax :edx)
    (:idivl :ebx :eax :edx)
    (:movl :edx :eax)))



(defun mod (number divisor)
  "Returns second result of FLOOR."
  (let ((rem (rem number divisor)))
    (if (and (not (zerop rem))
             (if (minusp divisor)
                 (plusp number)
                 (minusp number)))
        (+ rem divisor)
        rem)))

;;; bytes

(defun byte (size position)
  (+ (* size #x400) position))

(define-compiler-macro byte (&whole form size position)
  (cond
   ((and (integerp size)
	 (integerp position))
    (+ (* size #x400) position))
   #+ignore
   ((integerp size)
    `(+ ,position ,(* size #x400)))
   (t form)))

(defun byte-size (bytespec)
  (truncate bytespec #x400))

(defun byte-position (bytespec)
  (rem bytespec #x400))

(defun logbitp (index integer)
  (check-type integer fixnum)
  (with-inline-assembly (:returns :boolean-cf=1)
    (:compile-two-forms (:eax :ebx) index integer)
    (:testl #x80000003 :eax)
    (:jnz '(:sub-program ()
	    (:int 66)))
    (:movl :eax :ecx)
    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (:addl #.movitz::+movitz-fixnum-shift+ :ecx)
    (:btl :ecx :ebx)))

(define-compiler-macro logbitp (&whole form index integer &environment env)
  (if (not (movitz:movitz-constantp index env))
      form
    (let ((index (movitz::movitz-eval index env)))
      (check-type index (integer 0 30))
      `(with-inline-assembly (:returns :boolean-cf=1)
	 (:compile-form (:result-mode :eax) ,integer)
	 (:testb #.movitz::+movitz-fixnum-zmask+ :al)
	 (:jnz '(:sub-program () (:int 107)))
	 (:btl ,(+ index movitz::+movitz-fixnum-shift+) :eax)))))

      
(defun logand%2op (x y)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) x)
    (:compile-form (:result-mode :ebx) y)
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program () (:int 107)))
    (:testb #.movitz::+movitz-fixnum-zmask+ :bl)
    (:jnz '(:sub-program () (:movl :ebx :eax) (:int 107)))
    (:andl :ebx :eax)))

(define-compiler-macro logand%2op (&whole form x y)
  (cond
   ((and (movitz:movitz-constantp x) (movitz:movitz-constantp y))
    (logand  (movitz::movitz-eval x) (movitz::movitz-eval y)))
   (t form)))

(defun logand (&rest integers)
  (declare (dynamic-extent integers))
  (if (null integers)
      -1
    (reduce #'logand%2op integers)))

(define-compiler-macro logand (&whole form &rest integers)
  (let ((constant-folded-integers (loop for x in integers
				      with folded-constant = -1
				      if (and (movitz:movitz-constantp x)
					      (not (= -1 (movitz::movitz-eval x))))
				      do (setf folded-constant
					   (logand folded-constant (movitz::movitz-eval x)))
				      else collect x into non-constants
				      finally (return (if (= -1 folded-constant)
							  non-constants
							(cons folded-constant non-constants))))))
    (case (length constant-folded-integers)
      (0 0)
      (1 (first constant-folded-integers))
      (2 `(logand%2op ,(first constant-folded-integers) ,(second constant-folded-integers)))
      (t `(logand (logand%2op ,(first constant-folded-integers) ,(second constant-folded-integers))
		  ,@(cddr constant-folded-integers))))))

(defun logandc1 (integer1 integer2)
  (check-type integer1 fixnum)
  (check-type integer2 fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) integer1)
    (:compile-form (:result-mode :ebx) integer2)
    (:notl :eax)
    (:andl :ebx :eax)))

(defun logandc2 (integer1 integer2)
  (check-type integer1 fixnum)
  (check-type integer2 fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) integer1)
    (:compile-form (:result-mode :ebx) integer2)
    (:notl :ebx)
    (:andl :ebx :eax)))

(defun logior%2op (x y)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) x)
    (:compile-form (:result-mode :ebx) y)
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program () (:int 107)))
    (:testb #.movitz::+movitz-fixnum-zmask+ :bl)
    (:jnz '(:sub-program () (:movl :ebx :eax) (:int 107)))
    (:orl :ebx :eax)))


(define-compiler-macro logior%2op (&whole form x y)
  (cond
   ((and (movitz:movitz-constantp x) (movitz:movitz-constantp y))
    (logior  (movitz::movitz-eval x) (movitz::movitz-eval y)))
   (t form)))

(defun logior (&rest integers)
  (declare (dynamic-extent integers))
  (if (null integers)
      0
    (reduce #'logior%2op integers)))

(define-compiler-macro logior (&whole form &rest integers)
  (let ((constant-folded-integers (loop for x in integers
				      with folded-constant = 0
				      if (and (movitz:movitz-constantp x)
					      (not (zerop (movitz::movitz-eval x))))
				      do (setf folded-constant
					   (logior folded-constant (movitz::movitz-eval x)))
				      else collect x into non-constants
				      finally (return (if (= 0 folded-constant)
							  non-constants
							(cons folded-constant non-constants))))))
    (case (length constant-folded-integers)
      (0 0)
      (1 (first constant-folded-integers))
      (2 `(logior%2op ,(first constant-folded-integers) ,(second constant-folded-integers)))
      (t `(logior (logior%2op ,(first constant-folded-integers) ,(second constant-folded-integers))
		  ,@(cddr constant-folded-integers))))))

(defun logxor%2op (x y)
  (check-type x fixnum)
  (check-type y fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) x)
    (:compile-form (:result-mode :ebx) y)
    (:xorl :ebx :eax)))

(defun logxor (&rest integers)
  (declare (dynamic-extent integers))
  (if (null integers)
      0
    (reduce #'logxor%2op integers)))

(defun lognot (integer)
  (check-type integer fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) integer)
    (:xorl #.(cl:- #xffffffff movitz::+movitz-fixnum-zmask+) :eax)))

(defun ldb (bytespec integer)
  (logand (ash integer (- (byte-position bytespec)))
	  (svref #(#x0 #x1 #x3 #x7
		   #xf #x1f #x3f #x7f
		   #xff #x1ff #x3ff #x7ff
		   #xfff #x1fff #x3fff #x7fff
		   #xffff #x1ffff #x3ffff #x7ffff
		   #xfffff #x1fffff #x3fffff #x7fffff
		   #xffffff #x1ffffff #x3ffffff #x7ffffff
		   #xfffffff)
		 (byte-size bytespec))))

(define-compiler-macro ldb (&whole form &environment env bytespec integer)
  (flet ((constant-bytespec-p (bytespec)
	   (and (consp bytespec)
		(eq 'byte (first bytespec))
		(movitz:movitz-constantp (second bytespec) env)
		(movitz:movitz-constantp (third bytespec) env))))
    (cond
     ((and (constant-bytespec-p bytespec)
	   (movitz:movitz-constantp integer env))
      (ldb (byte (movitz:movitz-eval (second bytespec) env)
		 (movitz:movitz-eval (third bytespec) env))
	   (movitz:movitz-eval integer env))) ; constant folding
     ((constant-bytespec-p bytespec)
      (let ((size (movitz:movitz-eval (second bytespec) env))
	    (position (movitz:movitz-eval (third bytespec) env)))
	(assert (<= (+ size position) 30))
	`(with-inline-assembly (:returns :register :type integer)
	   (:compile-form (:result-mode :register) ,integer)
	   (:andl ,(mask-field (byte size (+ position movitz::+movitz-fixnum-shift+)) -1)
		  (:result-register))
	   ,@(unless (zerop position)
	       `((:shrl ,position (:result-register)))))))
     (t form))))

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


(defun ldb-test (bytespec integer)
  (case (byte-size bytespec)
    (0 nil)
    (1 (logbitp (byte-position bytespec) integer))
    (t (/= 0 (ldb bytespec integer)))))

(defun logtest (integer-1 integer-2)
  "=> generalized-boolean"
  (not (= 0 (logand integer-1 integer-2))))

(defun dpb (newbyte bytespec integer)
  (logior (mask-field bytespec (ash newbyte (byte-position bytespec)))
	  (logandc2 integer (mask-field bytespec -1))))


(defun mask-field (bytespec integer)
  (ash (ldb bytespec integer) (byte-position bytespec)))

(defun deposit-field (newbyte bytespec integer)
  (logior (mask-field bytespec newbyte)
	  (logandc2 integer (mask-field bytespec -1))))

;;; Types

(define-typep integer (x &optional (min '*) (max '*))
  (and (typep x 'integer)
       (or (eq min '*) (<= min x))
       (or (eq max '*) (<= x max))))

(deftype signed-byte (&optional (size '*))
  (cond
   ((eq size '*)
    'integer)
   ((typep size '(integer 1 *))
    (list 'integer
	  (- (ash 1 (1- size)))
	  (1- (ash 1 (1- size)))))
   (t (error "Illegal size for signed-byte."))))

(deftype unsigned-byte (&optional (size '*))
  (cond
   ((eq size '*)
    '(integer 0))
   ((typep size '(integer 1 *))
    (list 'integer 0 (1- (ash 1 size))))
   (t (error "Illegal size for unsigned-byte."))))

(define-simple-typep (bit bitp) (x)
  (or (eq x 0) (eq x 1)))

;;;

(defun plus-if (x y)
  (if (integerp x) (+ x y) x))

(defun minus-if (x y)
  (if (integerp x) (- x y) x))

(defun gcd (&rest numbers)
  (numargs-case
   (1 (u) u)
   (2 (u v)
      ;; Code borrowed from CMUCL.
      (do ((k 0 (1+ k))
	   (u (abs u) (ash u -1))
	   (v (abs v) (ash v -1)))
	  ((oddp (logior u v))
	   (do ((temp (if (oddp u) (- v) (ash u -1))
		      (ash temp -1)))
	       (nil)
	     (declare (fixnum temp))
	     (when (oddp temp)
	       (if (plusp temp)
		   (setq u temp)
		 (setq v (- temp)))
	       (setq temp (- u v))
	       (when (zerop temp)
		 (let ((res (ash u k)))
		   (declare (type (signed-byte 31) res)
			    (optimize (inhibit-warnings 3)))
		   (return res))))))))
   (t (&rest numbers)
      (declare (dynamic-extent numbers))
      (do ((gcd (car numbers)
		(gcd gcd (car rest)))
	   (rest (cdr numbers) (cdr rest)))
	  ((null rest) gcd)))))

(defun floor (n &optional (divisor 1))
  "This is floor written in terms of truncate."
  (numargs-case
   (1 (n) n)
   (2 (n divisor)
      (multiple-value-bind (q r)
	  (truncate n divisor)
	(cond
	 ((<= 0 q)
	  (values q r))
	 ((= 0 r)
	  (values q 0))
	 (t (values (1- q) (+ r divisor))))))
   (t (n &optional (divisor 1))
      (floor n divisor))))

(define-compiler-macro %bignum-bigits (x)
  `(with-inline-assembly (:returns :eax)
     (:compile-form (:result-mode :eax) ,x)
     (:movzxw (:eax #.(bt:slot-offset 'movitz::movitz-bignum
				      'movitz::length))
	      :ecx)
     (:leal ((:ecx #.movitz:+movitz-fixnum-factor+))
	    :eax)))

(defun %bignum-bigits (x)
  (%bignum-bigits x))

(defun copy-bignum (old)
  (check-type old bignum)
  (let* ((length (1+ (%bignum-bigits old)))
	 (new (malloc-data-words length)))
    (with-inline-assembly (:returns :eax)
      (:compile-two-forms (:eax :ebx) new old)
      (:compile-form (:result-mode :edx) length)
     copy-bignum-loop
      (:subl #.movitz:+movitz-fixnum-factor+ :edx)
      (:movl (:ebx :edx #.movitz:+other-type-offset+) :ecx)
      (:movl :ecx (:eax :edx #.movitz:+other-type-offset+))
      (:jnz 'copy-bignum-loop))))

(defun print-bignum (x)
  (check-type x bignum)
  (dotimes (i (1+ (%bignum-bigits x)))
    (format t "~8,'0X " (memref x -6 i :unsigned-byte32)))
  (terpri)
  (values))