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
;;;; $Id: integers.lisp,v 1.4 2004/04/01 02:12:22 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/typep)
(provide :muerte/integers)

(in-package muerte)

(defconstant most-positive-fixnum #.movitz::+movitz-most-positive-fixnum+)
(defconstant most-negative-fixnum #.movitz::+movitz-most-negative-fixnum+)

(defun fixnump (x)
  (typep x 'fixnum))

(defun evenp (x)
  (with-inline-assembly (:returns :ebx)
    (:compile-form (:result-mode :eax) x)
    (:globally (:movl (:edi (:edi-offset t-symbol)) :ebx))
    (:testb #.(cl:1+ (cl:* 2 movitz::+movitz-fixnum-zmask+)) :al)
    (:jz 'done)
    (:movl :edi :ebx)
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program (not-fixnum) (:int 107) (:jmp (:pc+ -4))))
    done))

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
		  sum (movitz::eval-form operand env)
		  into constant-term
		  else collect operand
		  into non-constant-operands
		  finally (return (if (zerop constant-term)
				      non-constant-operands
				    (cons constant-term non-constant-operands))))))
	 `(+ (+%2op ,(first operands) ,(second operands)) ,@(cddr operands))))))

(defun +%2op (term1 term2)
  (check-type term1 fixnum)
  (check-type term2 fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) term1)
    (:compile-form (:result-mode :ebx) term2)
    (:addl :ebx :eax)
    (:into)))

#+ignore
(define-compiler-macro +%2op (&whole form term1 term2)
  (cond
   ((and (movitz:movitz-constantp term1)	; first operand zero?
	 (zerop (movitz::eval-form term1)))
    term2)				; (+ 0 x) => x
   ((and (movitz:movitz-constantp term2)	; second operand zero?
	 (zerop (movitz::eval-form term2)))
    term1)				; (+ x 0) => x
   ((and (movitz:movitz-constantp term1)
	 (movitz:movitz-constantp term2))
    (+ (movitz::eval-form term1)
       (movitz::eval-form term2)))	; compile-time constant folding.
   ((movitz:movitz-constantp term1)
    (let ((constant-term1 (movitz::eval-form term1)))
      (check-type constant-term1 (signed-byte 30))
      `(with-inline-assembly (:returns :register :side-effects nil) ; inline
	 (:compile-form (:result-mode :register) ,term2)
	 (:addl ,(* movitz::+movitz-fixnum-factor+ constant-term1) (:result-register))
	 (:into))))
   ((movitz:movitz-constantp term2)
    (let ((constant-term2 (movitz::eval-form term2)))
      (check-type constant-term2 (signed-byte 30))
      `(with-inline-assembly (:returns :register :side-effects nil) ; inline
	 (:compile-form (:result-mode :register) ,term1)
	 (:addl ,(* movitz::+movitz-fixnum-factor+ constant-term2) (:result-register))
	 (:into))))
   (t `(with-inline-assembly (:returns :eax :side-effects nil)
	 (:compile-two-forms (:ebx :eax) ,term1 ,term2)
	 (:addl :ebx :eax)
	 (:into)))))

(defun 1+ (number)
  (+ 1 number))

(define-compiler-macro 1+ (number)
  `(+ ,number 1))

(defun 1- (number)
  (+ -1 number))

(define-compiler-macro 1- (number)
  `(- ,number 1))

(defun + (&rest terms)
  (numargs-case
   (1 (x) x)
   (2 (x y)
      (with-inline-assembly (:returns :eax)
	(:compile-form (:result-mode :eax) x)
	(:compile-form (:result-mode :ebx) y)
	(:movl :eax :ecx)
	(:orl :ebx :ecx)
	(:testb #.movitz::+movitz-fixnum-zmask+ :cl)
	(:jnz '(:sub-program (not-integer) ;
		(:int 107)))
	(:addl :ebx :eax)
	(:into)))
   (3 (x y z)
      (with-inline-assembly (:returns :eax)
	(:compile-form (:result-mode :eax) x)
	(:compile-form (:result-mode :ebx) y)
	(:movl :eax :ecx)
	(:compile-form (:result-mode :edx) z)
	(:orl :ebx :ecx)
	(:orl :edx :ecx)
	(:testb #.movitz::+movitz-fixnum-zmask+ :cl)
	(:jnz 'not-integer)
	(:addl :ebx :eax)
	(:into)
	(:addl :edx :eax)
	(:into)))
   (t (&rest terms)
      (declare (dynamic-extent terms))
      (if (null terms)
	  0
	(reduce #'+ terms)))))

;;;(defmacro incf (place &optional (delta-form 1))
;;;  `(setf ,place (+ ,place ,delta-form)))

(define-modify-macro incf (&optional (delta-form 1)) +)

;;; Subtraction

(define-compiler-macro - (&whole form &rest operands)
  (case (length operands)
    (0 0)
    (1 `(-%2op 0 ,(first operands)))
    (2 `(-%2op ,(first operands) ,(second operands)))
    (t `(- (-%2op ,(first operands) ,(second operands)) 
	   ,@(cddr operands)))))


(define-compiler-macro -%2op (&whole form minuend subtrahend)
  (cond
   ((and (movitz:movitz-constantp minuend)	; first operand zero?
	 (zerop (movitz::eval-form minuend)))
    `(with-inline-assembly (:returns :register :side-effects nil)
       (:compile-form (:result-mode :register) ,subtrahend)
       (:negl (:result-register))	; (- 0 x) => -x
       (:into)))
   ((and (movitz:movitz-constantp subtrahend) ; second operand zero?
	 (zerop (movitz::eval-form subtrahend)))
    (movitz::eval-form minuend))		; (- x 0) => x
   ((and (movitz:movitz-constantp minuend)
	 (movitz:movitz-constantp subtrahend))
    (- (movitz::eval-form minuend)
       (movitz::eval-form subtrahend)))	; compile-time constant folding.
   ((movitz:movitz-constantp minuend)
    (let ((constant-minuend (movitz::eval-form minuend)))
      (check-type constant-minuend (signed-byte 30))
      `(with-inline-assembly (:returns :register :side-effects nil) ; inline
	 (:compile-form (:result-mode :register) ,subtrahend)
	 (:subl ,(* movitz::+movitz-fixnum-factor+ constant-minuend) (:result-register))
	 ;;;;;;; NEED CHECKING HERE
	 (:into)
	 (:negl (:result-register)))))
   ((movitz:movitz-constantp subtrahend)
    (let ((constant-subtrahend (movitz::eval-form subtrahend)))
      (check-type constant-subtrahend (signed-byte 30))
      `(+%2op ,minuend ,(- constant-subtrahend))))
   (t `(with-inline-assembly (:returns :eax :side-effects nil)
	 (:compile-two-forms (:eax :ebx) ,minuend ,subtrahend)
	 (:subl :ebx :eax)
	 (:into)))))

(defun -%2op (minuend subtrahend)
  (check-type minuend fixnum)
  (check-type subtrahend fixnum)
  (-%2op minuend subtrahend))

(defun - (minuend &rest subtrahends)
  (declare (dynamic-extent subtrahends))
  (if subtrahends
      (reduce #'-%2op subtrahends :initial-value minuend)
    (-%2op 0 minuend)))
    
;;;(defmacro decf (place &optional (delta-form 1))
;;;  `(setf ,place (- ,place ,delta-form)))

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
    (:jnz '(:sub-program (not-integer)
	    (:int 107)
	    (:jmp 'not-integer)))
    (:cmpl :ebx :eax)
    (:ret)))

;;;

(define-compiler-macro <=%3op (min x max &environment env)
  (cond
   ((and (movitz:movitz-constantp min env)
	 (movitz:movitz-constantp max env))
    (let ((min (movitz::eval-form min env))
	  (max (movitz::eval-form max env)))
      (check-type min integer)
      (check-type max integer)
      ;; (warn "~D -- ~D" min max)
      (cond
       ((movitz:movitz-constantp x env)
	(<= min (movitz::eval-form x env) max))
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
    (let ((min (movitz::eval-form min env)))
      (check-type min integer)
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
	     (check-type number integer)
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
	   (:cmpl ,(* (movitz::eval-form max env)
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
    `(with-inline-assembly (:returns :eax :type integer)
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
		 (:sarl ,(- count) (:result-register))
		 (:andb #.(cl:logxor #xff movitz::+movitz-fixnum-zmask+) (:result-register-low8))))
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

(define-compiler-macro *%2op (&whole form &environment env factor1 factor2)
  (cond
   ((and (movitz:movitz-constantp factor1 env)
	 (movitz:movitz-constantp factor2 env))
    (* (movitz::eval-form factor1 env)
       (movitz::eval-form factor2 env)))
   ((movitz:movitz-constantp factor2 env)
    `(*%2op ,(movitz::eval-form factor2 env) ,factor1))
   ((movitz:movitz-constantp factor1 env)
    (let ((f1 (movitz::eval-form factor1 env)))
      (check-type f1 integer)
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
   (t form)))

(defun *%2op (factor1 factor2)
  (check-type factor1 fixnum)
  (check-type factor2 fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) factor1)
    (:compile-form (:result-mode :ebx) factor2)
    (:sarl #.movitz::+movitz-fixnum-shift+ :eax)
    (:imull :ebx :eax :edx)
    (:into)))

(define-compiler-macro * (&whole form &rest operands)
  (case (length operands)
    (0 0)
    (1 (first operands))
    (2 `(*%2op ,(first operands) ,(second operands)))
    (t `(* (*%2op ,(first operands) ,(second operands)) ,@(cddr operands)))))

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
	(:sarl #.movitz::+movitz-fixnum-shift+ :ebx)
	(:imull :ebx :eax :edx)
	(:into)))
   (t (&rest factors)
      (declare (dynamic-extent factors))
      (if (null factors)
	  1
	(reduce '*%2op factors)))))

;;; Division

(define-compiler-macro truncate (number &optional (divisor 1))
  `(do-result-mode-case ()
     (:plural
      (truncate%2ops ,number ,divisor))
     (t (truncate%2ops%1ret ,number ,divisor))))
  
(defun truncate%2ops (number divisor)
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
    (:movl :edx :ebx)
    (:xorl :ecx :ecx)
    (:movb 2 :cl)			; return values: qutient, remainder.
    (:stc)))

(defun truncate%2ops%1ret (number divisor)
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

(define-compiler-macro truncate%2ops%1ret (&whole form &environment env number divisor)
  (cond
   ((movitz:movitz-constantp divisor env)
    (let ((d (movitz::eval-form divisor env)))
      (check-type d number)
      (case d
	(0 (error "Truncate by zero."))
	(1 number)
	(t `(with-inline-assembly (:returns :eax :type integer)
	      (:compile-form (:result-mode :eax) ,number)
	      (:compile-form (:result-mode :ebx) ,divisor)
	      (:testb #.movitz::+movitz-fixnum-zmask+ :al)
	      (:jnz '(:sub-program () (:int 66)))
	      (:cdq :eax :edx)
	      (:idivl :ebx :eax :edx)
	      (:shll #.movitz::+movitz-fixnum-shift+ :eax))))))
   (t form)))

(defun truncate (number &optional (divisor 1))
  (truncate number divisor))


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
      (ldb (byte (movitz::eval-form (second bytespec) env)
		 (movitz::eval-form (third bytespec) env))
	   (movitz::eval-form integer env))) ; constant folding
     ((constant-bytespec-p bytespec)
      (let ((size (movitz::eval-form (second bytespec) env))
	    (position (movitz::eval-form (third bytespec) env)))
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
   (t (error "Illegal size for signed-byte."))))

(define-simple-typep (bit bitp) (x)
  (or (eq x 0) (eq x 1)))

;;;

(defun plus-if (x y)
  (if (integerp x) (+ x y) x))

(defun minus-if (x y)
  (if (integerp x) (- x y) x))

