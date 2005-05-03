;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      los0.lisp
;;;; Description:   Top-level initialization and testing.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Dec  1 18:08:32 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: los0.lisp,v 1.41 2005/05/03 20:13:07 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :los0 :load-priority 0)

(require :common-lisp)
(require :x86-pc/all)
(require :x86-pc/io-space)
(require :x86-pc/ne2k)
(require :x86-pc/floppy)
(require :x86-pc/serial)

(require :lib/readline)
(require :lib/toplevel)
;; (require :lib/net/ip6)
(require :lib/net/ip4)
(require :lib/repl)

(require :ll-testing)

(defpackage muerte.init
  (:nicknames #:los0)
  (:use #:common-lisp
	#:muerte
	#:muerte.lib
	#:muerte.x86-pc
	#:repl
	#:muerte.readline
	#:muerte.toplevel
	#:muerte.ethernet
;; 	#:muerte.ip6
	#:muerte.ip4
	#:muerte.mop
	#:muerte.x86-pc.serial))

(require :los0-gc)			; Must come after defpackage.

(in-package muerte.init)

(defun test0 ()
  (ash 1 -1000000000000))

(defun test1 ()
  (unwind-protect 0 (the integer 1)))

(defun x (bios32)
  (warn "X: ~S" (memref-int bios32))
  (warn "X: ~S" (= (memref-int bios32) #x5f32335f)))

(defun test2 ()
  (funcall
   (compile
    nil
    '(lambda (a) (declare (notinline > *))
      (declare (optimize (compilation-speed 0) (safety 2) (speed 2) (debug 0) (space 3)))
      (catch 'ct1 (* a (throw 'ct1 (if (> 0) a 0))))))
   5445205692802))

(defun test3 ()
  (loop for x below 2 count (not (not (typep x t)))))

(defun test4 ()
  (let ((aa 1)) (if (not (/= aa 0)) aa 0)))


(defun test-floppy ()
  (muerte.x86-pc::fd-start-disk)	; to initialize the controller and spin the drive up.
  (muerte.x86-pc::fd-cmd-seek 70)	; to seek to track 70.
  (setf (muerte.x86-pc::fd-motor) nil))	; to turn the drive and controller off.


(defun alist-get-expand (alist key)
  (let (cons)
    (tagbody
     loop
      (setq cons (car alist))
      (cond ((eq alist nil) (go end))
	    ((eq cons nil))
	    ((eq key (car cons)) (go end)))
      (setq alist (cdr alist))
      (go loop)
     end)
    (cdr cons)))

;;;(defun test-irq ()
;;;  (with-inline-assembly (:returns :multiple-values)
;;;    (:compile-form (:result-mode :multiple-values) (values 0 1 2 3 4 5))
;;;    (:int 42)))
;;;
;;;(defun koo ()
;;;  (prog1 (make-values)
;;;    (format t "hello: ~S" (values 'a 'b 'c 'd))))
;;;
;;;(defun test-complement (&rest args)
;;;  (declare (dynamic-extent args))
;;;  (apply (complement #'symbolp) args))
;;;
;;;(defun test-constantly (&rest args)
;;;  (declare (dynamic-extent args))
;;;  (apply (constantly 'test-value) args))

(defun test-closure (x z)
  (flet ((closure (y) (= x (1+ y))))
    (declare (dynamic-extent (function closure)))
    (closure z)
    #+ignore (funcall (lambda (y) (= x (1+ y)))
		      z)))

(defun test-stack-cons (x y)
  (muerte::with-dynamic-extent-scope (zap)
    (let ((foo (muerte::with-dynamic-extent-allocation (zap)
		 (cons x (lambda () y)))))
      (format t "~Z: ~S, ~S" foo foo (funcall (cdr foo))))))

(defun test-handler (x)
  (let ((foo x))
    (handler-bind
	((error (lambda (c)
		  (format t "error: ~S ~S" c x))))
      (error "This is an error. ~S" foo))))

(defun fooo (v w)
  (tagbody
    (print (block blurgh
	     (progv (list v) (list w)
	       (format t "Uh: ~S" (symbol-value v))
	       (if (symbol-value v)
		   (return-from blurgh 1)
		 (go zap)))))
   zap)
  t)


(defun test-break ()
  (with-inline-assembly (:returns :multiple-values)
    (:movl 10 :ecx)
    (:movl :esi :eax)			; This function should return itself!
    (:clc)
    (:break)))

(defun test-upload (x)
  ;; (warn "Test-upload blab la bla!!")
  (setf x (cdr x))
  x)

;;;(defun zzz (x)
;;;  (multiple-value-bind (symbol status)
;;;      (values-list x)
;;;    (warn "sym: ~S, stat: ~S" symbol status)))
;;;

#+ignore
(defun test-loop (x)
  (format t "test-loop: ~S~%"
	  (loop for i from 0 to 10 collect x)))
	      
#+ignore
(defun delay (time)
  (dotimes (i time)
    (with-inline-assembly (:returns :nothing)
      (:nop)
      (:nop))))
;;;
;;;(defun test-consp (x)
;;;  (with-inline-assembly (:returns :boolean-cf=1)
;;;    (:compile-form (:result-mode :ecx) x)
;;;    (:leal (:edi -4) :eax)
;;;    (:rorb :cl :al)))


#+ignore
(defun test-block (x)
  (block nil
    (let ((*print-base* (if x (return 3) 8)))
      (jumbo 2 2 (and x 2) (+ 3 3 (or x 4)) (if x 2 (return nil)))))
  #+ignore (+ x 2))

#+ignore
(defun jumbo (a b c &rest x)
  (declare (dynamic-extent x))
  (print a) (print b) (print c)
  (print x)
  'jumbo)

(defun jumbo2 (a b &rest x)
  (declare (dynamic-extent x))
  (print a) (print b)
  (print x)
  'jumbo)

(defun jumbo3 (a &rest x)
  (declare (dynamic-extent x))
  (print a)
  (print x)
  'jumbo)

(defun jumbo4 (&rest x)
  (declare (dynamic-extent x))
  (print x)
  'jumbo)

#+ignore
(defun tagbodyxx (x)
  (tagbody
    (print 'hello)
   haha
    (unwind-protect
	(when x (go hoho))
      (warn "unwind.."))
    (print 'world)
   hoho
    (print 'blrugh)))

#+ignore
(defun tagbodyxx (x)
  (tagbody
    (print 'hello)
   haha
    (unwind-protect
	(funcall (lambda ()
		   (when x (go hoho))))
      (warn "unwind.."))
    (print 'world)
   hoho
    (print 'blrugh)))

#+ignore
(defun kumbo (&key a b (c (jumbo 1 2 3)) d)
  (print a)
  (print b)
  (print c)
  (print d))
  
#+ignore
(defun lumbo (a &optional (b 'zap))
  (print a)
  (print b))

(defmacro do-check-esp (&body body)
  `(let ((before (with-inline-assembly (:returns :eax) (:movl :esp :eax))))
     (with-inline-assembly (:returns :nothing)
       (:compile-form (:result-mode :multiple-values) (progn ,@body)))
     (unless (eq before
		 (with-inline-assembly (:returns :eax) (:movl :esp :eax)))
       (error "ESP before body: ~S, after: ~S"
	      (with-inline-assembly (:returns :eax) (:movl :esp :eax))))))

#+ignore
(defun test-m-v-call ()
  (do-check-esp
      (multiple-value-call #'format t "~@{ ~D~}~%"
			   'a (values) 'b (test-loop 1) (make-values)
			   'c 'd  'e (make-no-values) 'f)))

(defun test-m-v-call2 ()
  (multiple-value-call #'format t "~@{ ~D~}~%"
		       'a 'b (values 1 2 3) 'c 'd 'e 'f))

(defun make-values ()
  (values 0 1 2 3 4 5))

(defun xfuncall (&rest args)
  (declare (dynamic-extent args))
  (break "xfuncall:~{ ~S~^,~}" args)
  (values))

(defun xfoo (f) 
  (do-check-esp
      (multiple-value-bind (a b c d)
	  (multiple-value-prog1 (make-values)
	    (format t "hello world"))
	(format t "~&a: ~S, b: ~S, c: ~S, d: ~S ~S" a b c d f))))


#+ignore
(defun make-no-values ()
  (values))

#+ignore
(defun test-nth-values ()
  (nth-value 2 (make-values)))

#+ignore
(defun test-values2 ()
  (multiple-value-bind (a b c d e f g h)
      (make-values)
    (format t "test-values2: A: ~S, B: ~S, C: ~S, D: ~S, E: ~S, F: ~S G: ~S, H: ~S~%"
	    a b c d e f g h)))

#+ignore
(defun test-flet (zap)
  (flet ((pingo (z y x)
	   (declare (ignore y z))
	   (format t "This is pingo: ~S with zap: ~W~%" x  zap)))
    ;; (declare (dynamic-extent pingo))
    (pingo 100 200 300)))

#+ignore
(defun test-flet2 (zap)
  (flet ((pingo (z y x)
	   (declare (ignore y z))
	   (format t "This is pingo: ~S with zap: ~W~%" x  zap)))
    ;; (declare (dynamic-extent pingo))
    (lambda (x)
      (pingo 100 200 300))))

(defun test-boo ()
  (let ((real-cmuc #'test-flet2))
    (let ((plongo (lambda (x)
		    (warn "~S real-cmuc: ~S" x real-cmuc)
		    (funcall real-cmuc x))))
      (funcall plongo 'zooom))))

(defun test-labels ()
  (labels ((pingo (x)
	     (format t "~&This is pingo: ~S~%" x)
	     (when (plusp x)
	       (pingo (1- x)))))
    (pingo 5)))

#+ignore
(defun foo-type (length start1 sequence-1)
  (do* ((i 0 #+ignore (+ start1 length -1) (1- i)))
      ((< i start1) sequence-1)
    (declare (type muerte::index i length))
    (setf (sequence-1-ref i)
      'foo)))

(defun plus (a b)
  (+ b a))

#+ignore
(defun test-values ()
  (multiple-value-bind (a b c d e f g h i j)
      (multiple-value-prog1
	  (make-values)
;;;	    (format t "this is the resulting form.~%")
	(format t "this is the first ignorable form.~%" 1 2 3)
	(format t "this is the second ignorable form.~%"))
;;;    (format t "test-values num: ~D~%" (capture-reg8 :cl))
    (format t "test-values: A: ~Z, B: ~Z, C: ~Z, D: ~Z  ~Z ~Z ~Z ~Z ~Z ~Z~%" a b c d e f g h i j)))


#+ignore
(defun test-keywords (&key a b (c 100) ((:d x) 5 x-p))
  (format t "test-keywords: a: ~S, b: ~S, c: ~S, x: ~S, x-p: ~S~%"
	  a b c x x-p))

#+ignore
(defun test-k1 (a b &key x)
  (declare (ignore a b))
  (warn "x: ~S" x))

(defun test-funcall (&rest args)
  (declare (dynamic-extent args))
  (format t "~&test-funcall args: ~S~%" args))

#+ignore
(defun test-rest (&optional (a0 nil a0-p) a1 a3 &rest args)
  (declare (dynamic-extent args))
  (when a0-p
    (format t "args: ~S, ~S, ~S: ~S~%" a0 a1 a3 args)))


(defun test-return ()
  (print (block nil
	   (values 'x 'y (if (foo) (return 'foo) (return-from test-return 'not-foo)) 'bar)))
  5)

#+ignore
(defun test-lexthrow (x)
  (apply (lambda (a b)
	   (unwind-protect
	       (if (plusp a) 0 (return-from test-lexthrow (+ a b)))
	     (warn "To serve and protect!")))
	 x))

#+ignore
(defun test-lexgo (x)
  (let ((*print-base* 2))
    (return-from test-lexgo (print 123))))

#+ignore
(defun test-xgo (c x)
  (tagbody
   loop
    (warn "c: ~S" c)
    (apply (lambda (a)
	     (decf c)
	     (if (plusp a) (go exit) (go loop))
	     (warn "juhu, a or x: ~S, c: ~S" a c))
	   x)
   exit
    (warn "exited: ~S" c)))


(defun test-bignum ()
  123456789123456)

(defun fe32 ()
  #xfffffffe)

(defun fe64 ()
  #xfffffffffffffffe)

(defun fe96 ()
  #xfffffffffffffffffffffffe)

(defun one32 ()
  #x100000000)

(defun z (op x y)
  (let ((foo (cons 1 2))
	(result (funcall op x y))
	(bar (cons 3 4)))
    (if (not (typep result 'pointer))
	(warn "foo: ~Z result: ~Z, bar: ~Z, diff foo-bar: ~D."
	      foo result bar
	      (- (object-location bar) (object-location foo)))
      (warn "foo: ~Z result: ~Z, bar: ~Z, diff: ~D, ~D."
	    foo result bar
	    (- (object-location result) (object-location foo))
	    (- (object-location bar) (object-location result))))
    (values foo result bar)))

(defun modx (x)
  (lambda ()
    (print x)))

(defun mod30 (x)
  (ldb (Byte 30 0) x))

(defun mod32-4 (x)
  (ldb (byte 28 4) x))

(defun mod24-4 (x)
  (ldb (Byte 24 4) x))

(defun zz (op x y)
  (let ((foo (vector 1 2))
	(result (funcall op x y))
	(bar (vector 3 4)))
    (if (not (typep result 'pointer))
	(warn "foo: ~Z result: ~Z, bar: ~Z, diff foo-bar: ~D."
	      foo result bar
	      (- (object-location bar) (object-location foo)))
      (warn "foo: ~Z result: ~Z, bar: ~Z, diff: ~D, ~D."
	    foo result bar
	    (- (object-location result) (object-location foo))
	    (- (object-location bar) (object-location result))))
    (values foo result bar)))

(defun testb ()
  #(1 2 3 4))

(defun gt5 (x)
  (<= x 5))

(defun xplus (x)
  (typep x '(integer 0 *)))

(defstruct (xxx :constructor (:constructor boa-make-xxx (x y z)))
  x y (z 'init-z))

(defun test-struct ()
  (format t "make-xxx: ~S~%" (let ((s (make-xxx))) s))
  (format t "make-xxx: ~S~%" (xxx-z (make-xxx))))

(defun test-dynamic ()
  #+ignore
  (let ((x 100))
    (let ((y x))
      (let ((z y))
	(format t "y: ~S, x: ~S, z: ~S~%" y x z))))
  #+ignore
  (format t "~D ~D ~D~%" 0 1
	  (let ((*x* 100))
	    (declare (special *x*))
	    (format t "*x*: ~S~%" *x*)
	    (symbol-value '*x*)))
  #+ignore
  (format t "~D ~D ~D~%" 0 1
	  (progv '(*x*) '(101)
	    (format t "*x*: ~S~%" (symbol-value '*x*))
	    (symbol-value '*x*)))
  (let ((*x* 200))
    (declare (special *x*))
    (format t "*x*: ~S~%" *x*)
    #+ignore
    (let ((*x* 300))
      (declare (special *x*))
      (format t "*x*: ~S~%" *x*))
    *x*))

#+ignore
(defun test-dynamic-formal (*print-base*)
  (print *print-base*))

#+ignore
(defun verify-throw ()
  "CLHS speaketh:
The following prints ``The inner catch returns :SECOND-THROW'' and then returns :outer-catch."
  (catch 'foo
    (format t "The inner catch returns ~s.~%"
	    (catch 'foo
	      (unwind-protect (throw 'foo :first-throw)
		(throw 'foo :second-throw))))
    :outer-catch))

#+ignore
(defun do-throw ()
  (unwind-protect (print 'hello)
    (throw 'foo :second-throw)))


#+ignore
(defun bloo (x)
  #'bloo
  (multiple-value-prog1
      (sloo x (1+ x))
    (print 'hello)))

#+ignore
(defun sloo (&rest x)
  (declare (dynamic-extent x))
  (let ((y (car x)))
    (sloo y)))

#+ignore
(defun test-throw (tag)
  (unwind-protect
      (warn "throw: ~Z" (throw tag (values 'throw1 (make-values) 'throw2)))
    (warn "Something happened: ~W" (make-values))
    #+ignore (return-from test-throw 'interrupted-value))
  (error "Huh?"))

#+ignore
(defun test-catch (x)
  (catch 'test-tag
    (test-throw x 'test-tag)
    (format t "Hello world")))

(defun test-throw (x tag)
  (when x
    (warn "Throwing ~S.." tag)
    (throw tag (values-list x))))

#+ignore
(defun test-up-catch ()
  (catch 'test-tag
    (test-up 'test-tag)
    (format t "Hello world")))

#+ignore
(defun test-up (tag)
 (unwind-protect
      (test-throw tag)
   (print 'hello-cleanup)))

(defun test-cons (x)
  (let ((cc (cons x x)))
    (cdr cc)))

(defun xx (x)
  (eql nil x))

(defun test-fixed (x y z)
  (warn "x: ~W, y: ~W, z: ~W" x y z))

(defun test-let-closure ()
  (tagbody
    (let ((*print-base* 10)
	  (x (go zz))
	  (*print-radix* nil))
      (warn "lending x: ~W" x)
      (values (lambda ()
		(warn "borrowed x: ~W" x)
		(* x 2))
	      #+ignore
	      (lambda (y)
		(setf x y))))
   zz
    (warn "zz")))

(defun test-not (x)
  (if (not x) 0 100))

(defun test-pingo (z)
  (block zzz
    (warn "hello world")
    (let ((zingo (+ z 23)))
      (return-from zzz
	(let ((x (* z zingo)))
	  (print (* x 2)))))
    (warn "not this")))


;;;(defclass test-class ()
;;;  (s1 s2))
;;;
(defun show-hash (x)
  (loop for y being the hash-keys of x
      do (format t "~&key: ~W [~W]" y (symbol-package y)))
  (values))
;;;
;;;
;;;(defclass c () (s1 s2))
;;;
;;;(defgeneric m (x))
;;;(defmethod m ((x c))
;;;  (declare (ignore x))
;;;  (warn "more m's: ~{~W~}" (when (next-method-p)
;;;			     (list (call-next-method))))
;;;  #'call-next-method)
;;;
;;;(defmethod m ((x standard-object))
;;;  (declare (ignore x))
;;;  'this-is-m-on-standard-object)
;;;
;;;(defmethod m ((x fixnum))
;;;  (declare (ignore x))
;;;  'this-is-m-on-fixnum)

(defun test-nested-extent ()
  ;; Check that the compiler doesn't suffer from the let nested-extent problem.
  ;; identity is used so the compiler won't shortcut the bindings.
  (let ((foo (identity 'foo-value))
	(bar (let ((zot (identity 'test-nested-extent)))
	       (setq zot 'zot-value)
	       (identity zot))))
    (if (eq foo 'foo-value)
	(format t "~&Success: foo is ~W, bar is ~W" foo bar)
      (format t "~&Failure! foo is ~W, bar is ~W" foo bar))))

(defun bar (x)
  (multiple-value-prog1
      (values 0 1 2)
    (format t "blungolo: ~S" x)))



#+ignore
(defun test-ncase (x y z)
  (numargs-case
   (1 (x) (values x 'one))
   (2 (x y) (values (+ x y) 'one 'two))
   (3 (x y z) (values (+ x y z) 'one 'two 'three))
   (t (args) (declare (ignore args)) 27)))

#+ignore
(defun xbar ()
  (print-dynamic-context :terse t)
  (block handler-case-block
    (let (handler-case-var)
      (tagbody
	(handler-bind
	    ((error (lambda (handler-case-temp-var)
		      (setq handler-case-var handler-case-temp-var)
		      (go handler-case-clause-tag))))
	    (print-dynamic-context :terse t)
	    (return-from handler-case-block
	      (signal "hello world")))
       handler-case-clause-tag
	(return-from handler-case-block
	  (let ((|c| handler-case-var))
	    (format t "got an error: ~s" |c|))))))
  (print-dynamic-context :terse t))

#+ignore
(defun plingu (&optional v)
  (let ((x (1+ *print-base*)))
    (print "foo")
    (print "foo")
    (print x)
    (print v)))

#+ignore
(defun (setf dingu) (x y)
  (when (> x y)
    (return-from dingu 'fooob))
  (+ x y))


(defun foo (&edx edx x &optional (y nil yp))
  (format t "~@{ ~A~}" x y yp edx))

(defun wefwe (&rest args)
  (declare (dynamic-extent args))
  (do ((p args (cdr p)))
      ((endp p))
    (let ((x (car p)))
      (print x))))

(defun mubmo ()
  (let ((x (muerte::copy-funobj #'format))
	(y (cons 1 2)))
    (warn "x: ~Z, y: ~Z" x y)))

;;;;;

(defclass food () ())

(defgeneric cook (food))

;;;(defmethod cook :before ((f food))
;;;  (declare (ignore f))
;;;  (print "A food is about to be cooked."))
;;;
;;;(defmethod cook :after ((f food))
;;;  (declare (ignore f))
;;;  (print "A food has been cooked."))

(defmethod cook ((f food))
  (declare (ignore f))
  (print "Cooking some food."))

(defun test-pie (n pie)
  (dotimes (i n)
    (pie-filling pie)))

(defun test-inc (n)
  (dotimes (i n)
    (warn "foo: ~S" (lambda ()
		      (setf i 5)))))

(defun test-id (n x)
  (dotimes (i n)
    (identity x)))

(defun test-inc2 (x)
  (print (prog1 x (incf x)))
  (print x))

(defclass pie (food)
  ((filling :accessor pie-filling 
	    :initarg :filling
	    :initform 'apple))
  #+ignore (:default-initargs :filling (if (foo) 'apple 'banana)))

(defclass pie2 (food)
  ((filling :accessor pie-filling 
	    :initarg :filling
	    )))

(defmethod cook ((p (eql 'pie)))
  (warn "Won't really cook a symbolic pie!")
  (values))

(defmethod cook ((p (eql 'pudding)))
  'cooked-pudding)

(defmethod slot-value-using-class :after (class (pie pie2) slot)
  (warn "HEy, don't poke inside my pie2!"))

(defmethod cook :after ((p symbol))
  (warn "A symbol may or may not have been cooked."))

(defmethod cook ((p pie))
  (cond
   ((eq 'banana (pie-filling p))
    (print "Won't cook a banana-pie, trying next.")
    (call-next-method))
   (t (print "Cooking a pie.")
      (setf (pie-filling p) (list 'cooked (pie-filling p))))))

(defmethod cook :before ((p pie))
  (declare (ignore p))
  (print "A pie is about to be cooked."))

(defmethod cook :after ((p pie))
  (declare (ignore p))
  (print "A pie has been cooked."))

(defun assess-cpu-frequency ()
  "Assess the CPU's frequency in units of 1024 Hz."
  (assert (cpu-featurep :tsc) ()
    "This function requires a CPU with the time-stamp-counter feature.")
  (let ((s0 (loop with x = (rtc-register :second)
		for s0 = (rtc-register :second)
		while (= x s0)
		finally (return s0))))
    (multiple-value-bind (c0-lo c0-hi)
	(read-time-stamp-counter)
      (loop while (= s0 (rtc-register :second)))
      (multiple-value-bind (c1-lo c1-hi)
	  (read-time-stamp-counter)
	(+ (ash (- c1-hi c0-hi) 19)
	   (ash (+ 512 (- c1-lo c0-lo)) -10))))))

(defun report-cpu-frequency ()
  (multiple-value-bind (mhz khz)
      (truncate (assess-cpu-frequency) 976)
    (format t "~&CPU frequency: ~D.~2,'0D MHz.~%" mhz (round khz 10)))
  (values))

(defvar *a* #(#x1 #x2 #x3 #x4 #x5 #x6 #x7 #x8))
(defvar *b* #(#x5 #xa #xf #x14 #x19 #x1e #x23 #x28 #x1400 #x1e00 #x2800 #x3200
	      #x3c00 #x4600 #x5000 #xa00 #x50 #x64 #x78 #x8c #xa0 #x14 #x28 #x3c
	      #xc800 #xf001 #x1801 #x4000 #x2800 #x5000 #x7800 #xa000 #x230 #x280
	      #x50 #xa0 #xf0 #x140 #x190 #x1e0 #x0 #xa001 #x4001 #xe002 #x8003
	      #x2003 #xc004 #x6005 #x280 #x3c0 #x500 #x640))

(defvar *cpu-frequency-mhz*)

(defun init-nano-sleep ()
  (setf *cpu-frequency-mhz*
    (truncate (assess-cpu-frequency) 976)))

(defun nano-sleep (nano-seconds)
  (let* ((t0 (read-time-stamp-counter))
	 (t1 (+ t0 (truncate (* nano-seconds (%symbol-global-value '*cpu-frequency-mhz*))
			     10000))))
    (when (< t1 t0)
      (loop until (< (read-time-stamp-counter) t0))) ; wait for wrap-around
    (loop until (>= (read-time-stamp-counter) t1))))

(defun test-nano-sleep (x)
  (time (nano-sleep x)))

;;;;;

;;;;;;;;;;;;;;; CL

(defun install-internal-time (&optional (minimum-frequency 100))
  "Figure out this CPU's internal-time-unit. Warning: This process takes about 1.5 seconds."
  (let ((s0 (loop with x = (rtc-register :second)
		for s0 = (rtc-register :second)
		while (= x s0)
		finally (return s0))))
    (multiple-value-bind (c0-lo c0-hi)
	(read-time-stamp-counter)
      (loop while (= s0 (rtc-register :second)))
      (multiple-value-bind (c1-lo c1-hi)
	  (read-time-stamp-counter)
	(let ((res (+ (ash (ldb (byte 22 0) (- c1-hi c0-hi)) 7)
		      (ash (- c1-lo c0-lo) -22))))
	  (cond
	   ((> res minimum-frequency)
	    (setf (symbol-function 'get-internal-run-time)
	      (lambda ()
		(multiple-value-bind (lo hi)
		    (read-time-stamp-counter)
		  (+ (ash lo -22)
		     (ash (ldb (byte 22 0) hi) 7)))))
	    (setf internal-time-units-per-second res))
	   (t ;; This is for really slow machines, like bochs..
	    (let ((res (+ (ash (- c1-hi c0-hi) 13)
			  (ash (- c1-lo c0-lo) -16))))
	      (setf (symbol-function 'get-internal-run-time)
		(lambda ()
		  (multiple-value-bind (lo hi)
		      (read-time-stamp-counter)
		    (+ (ash (ldb (byte 16 0) hi) 13) 
		       (ash lo -16)))))
	      (setf internal-time-units-per-second res))))))))
  (setf (symbol-function 'sleep)
    (lambda (seconds)
      ;; A stupid busy-waiting sleeper.
      (check-type seconds (real 0 *))
      (let ((start-time (get-internal-run-time)))
	(loop with start-time = (get-internal-run-time)
	    with end-time = (+ start-time (* seconds internal-time-units-per-second))
	    while (< (get-internal-run-time) end-time)))))
  (values))


;;;(defun get-internal-run-time ()
;;;  (multiple-value-bind (lo mid hi)
;;;      (read-time-stamp-counter)
;;;    (declare (ignore lo))
;;;    (dpb hi (byte 5 24) mid)))
;;;
;;;(defun get-internal-real-time ()
;;;  (get-internal-run-time))


(defun y-or-n-p (&optional control &rest arguments)
  "=> generalized-boolean"
  (declare (dynamic-extent arguments))
  (when control
    (fresh-line *query-io*)
    (apply #'format *query-io* control arguments))
  (write-string " (y/n) " *query-io*)
  (let ((response (contextual-readline *repl-readline-context*)))
    (and (> (length response) 0)
	 (char-equal #\y (char response 0)))))


;;;;;;;;;;;;;; Top-level commands..

(define-toplevel-command :cls ()
  (clear-console *terminal-io*)
  (setf (cursor-x *terminal-io*) 0
	(cursor-y *terminal-io*) 0)
  (values))

(define-toplevel-command :bt (&rest args)
  (declare (dynamic-extent args))
  (apply #'backtrace (mapcar #'eval args)))

(define-toplevel-command :cpu-reset ()
  (when (y-or-n-p "Really reset CPU?")
    (muerte.x86-pc.keyboard:cpu-reset))
  (values))

(define-toplevel-command :decimal (&optional x-list)
  (flet ((do-print (x)
	   (typecase x
	     (number
	      (case *print-base*
		(16 (format t "~&~W = ~D" x x))
		(10 (format t "~&~W = #x~X" x x))
		(t (format t "~&~W = ~D. = #x~X" x x x)))
	      (when (typep x 'ratio)
		(format t " ~~ ~,3F" x)))
	     (pointer
	      (format t "~&~Z = ~W" x x))
	     (t (fresh-line)
		(write x :radix nil :base (case *print-base* (10 16) (t 10)))))
	   x))
    (if x-list
	(do-print (eval x-list))
      (dolist (x cl:/ (values-list cl:/))
	(do-print x)))))

(define-toplevel-command :z (&optional x-list)
  (flet ((do-print (x)
	   (format t "~&~Z" x)
	   x))
    (if x-list
	(do-print (eval x-list))
      (dolist (x cl:/ (values-list cl:/))
	(do-print x)))))

(defmacro with-paging (options &body body)
  (declare (ignore options))
  `(block paging
     (let ((paging-offset 2))
       (handler-bind
	   ((newline (lambda (condition)
		       (declare (ignore condition))
		       (when (and paging-offset
				  (>= (incf paging-offset)
				      muerte.x86-pc::*screen-height*))
			 (format t "~&more? (y/n/a) ")
			 (prog ()
			  loop
			   (case (muerte.x86-pc.keyboard:poll-char)
			     ((#\escape)
			      (break "Console pager"))
			     ((#\n #\N)	; No more
			      (return-from paging (values)))
			     ((#\a #\A)	; Quit paging
			      (setf paging-offset nil))
			     ((#\newline #\x)
			      (setf paging-offset
				(1- muerte.x86-pc::*screen-height*)))
			     ((#\y #\Y #\space) ; One more page
			      (setf paging-offset 1))
			     (t (go loop))))
			 (write-char #\return)
			 (clear-line *standard-output* 0 (cursor-y *standard-output*))
			 ))))
	 ,@body))))

(defun tp (x) (dotimes (i x) (print i)))

(define-toplevel-command :more (form)
  (with-paging ()
    (multiple-value-call #'format t "~@{~&~W~}"
			 (eval form))))
	 
(define-toplevel-command :pop ()
  (when *debugger-dynamic-context*
    (let ((r (find-restart-from-context 'abort *debugger-dynamic-context*)))
      (if r
	  (invoke-restart r)
	(warn "No abort restart found."))))
  (values))

(define-toplevel-command :trace (&rest args)
  (declare (dynamic-extent args))
  (cond
   ((null args)
    (mapcar #'car muerte::*trace-map*))
   (t (apply #'do-trace args)
      (values))))

(define-toplevel-command :untrace (&rest function-names)
  (declare (dynamic-extent function-names))
  (cond
   ((null function-names)
    (do () ((null muerte::*trace-map*))
      (do-untrace (caar muerte::*trace-map*))))
   (t (map nil #'do-untrace function-names)
      (values))))


(defvar *debugger-printing-restarts* nil)

(define-toplevel-command :error ()
  (if (not (and (boundp '*debugger-condition*)
		*debugger-condition*))
      (fresh-line)
    (let ((condition *debugger-condition*)
	  (*print-safely* t))
      (cond
       ((consp condition)
	(fresh-line)
	(write-string (case (car condition)
			((simple-error error) "Error: ")
			(break "Break: ")
			(t (write (car condition)))))
	(if (stringp (cadr condition))
	    (apply 'format t (cadr condition) (cddr condition))
	  (write (cdr condition))))
       (t (format t "~&Error: ~A" condition)))
      (if *debugger-printing-restarts*
	  (progn (format t "~&[restarts suppressed]")
		 (halt-cpu))
	(let ((*debugger-printing-restarts* t))
	  (map-active-restarts (lambda (restart index)
				 (format t "~&~2D: ~A~%" index restart))
			       (or *debugger-dynamic-context*
				   (muerte::current-dynamic-context)))))))
  (values))

(define-toplevel-command :restart (&optional (r 0) &rest args)
  (declare (dynamic-extent args))
  (let* ((context (or *debugger-dynamic-context*
		      (current-dynamic-context)))
	 (restart (typecase r
		    (integer
		     (find-restart-by-index r context))
		    (symbol
		     (find-restart-from-context r context)))))
    (cond
     ((not restart)
      (format t "~&There is no restart like that."))
     (args
      (apply 'invoke-restart restart args))
     (t (invoke-restart-interactively restart)))))

(define-toplevel-command :package (package-name)
  (let ((p (find-package (string package-name))))
    (if (packagep p)
	(setf *package* p)
      (format t "~&No package named \"~A\"." package-name)))
  (values))

(define-toplevel-command :help (&optional (x (or (and (boundp '*debugger-condition*)
						      *debugger-condition*)
						 :help)))
  (fresh-line)
  (cond
   ((eq :help x)
    (format t "Toplevel commands:")
    (maphash (lambda (k v)
	       (declare (ignore v))
	       (format t " :~A" k))
	     *toplevel-commands*))
   ((and (keywordp x) (gethash x *toplevel-commands*))
    (describe (gethash x *toplevel-commands*)))
   (t (describe x)))
  (values))

(muerte.toplevel:define-toplevel-command :bochs-trace (form)
  (muerte::with-bochs-tracing ()
    (eval form)))

(muerte.toplevel:define-toplevel-command :mapkey (code-char-form)
  (let* ((code-char (eval code-char-form))
	 (char (etypecase code-char
		(character code-char)
		(integer (code-char code-char)))))
    (format t "~&Hit the (single) key you want to map to ~S..." char)
    (loop
      (loop until (muerte.x86-pc.keyboard::lowlevel-event-p))
      (multiple-value-bind (key-code release-p)
	  (muerte.x86-pc.keyboard::lowlevel-read)
	(when (and key-code (not release-p))
	  (case key-code
	    (#x1c (format t "~&Will not replace Enter key!"))
	    (t (format t "~&Setting scan-code ~S to ~S...~%" key-code char)
	       (setf (aref muerte.x86-pc.keyboard::*scan-codes* key-code) char)))
	  (return (values)))))))

(defun los0-debugger (condition)
  (without-interrupts
    (let ((*debugger-dynamic-context* (current-dynamic-context))
	  (*standard-output* *debug-io*)
	  (*standard-input* *debug-io*)
	  (*debugger-condition* condition)
	  (*package* (or (and (packagep *package*) *package*)
			 (find-package "INIT")
			 (find-package "USER")
			 (find-package "COMMON-LISP")
			 (error "Unable to find any package!")))
	  (*repl-prompt-context* #\d)
	  (*repl-readline-context* (or *repl-readline-context*
				       (make-readline-context :history-size 16))))
      (let ((*print-safely* t))
	(invoke-toplevel-command :error))
      (loop
	(with-simple-restart (abort "Abort to command level ~D." (1+ *repl-level*))
	  (read-eval-print))))))

(defun xwrite (object)
  (with-inline-assembly (:returns :nothing)
    (:locally (:movl (:edi (:edi-offset muerte::dynamic-env)) :eax))
    (:movl :eax (#x1000000))
    (:movl :ebp (#x1000004))
    (:movl :esi (#x1000008)))
  (block handler-case-block-1431896
    (let (handler-case-var-1431897)
      (tagbody
	(handler-bind
	    ((serious-condition
	      (lambda (handler-case-temp-var-1431898)
		(setq handler-case-var-1431897 handler-case-temp-var-1431898)
		(go handler-case-clause-tag-1431899))))
	  (return-from handler-case-block-1431896
	    (muerte::internal-write object)))
       handler-case-clause-tag-1431899
	(return-from handler-case-block-1431896
	  (let ((c handler-case-var-1431897))
	    (print-unreadable-object (c *standard-output* :type t :identity t)
	      (format t " while printing ~z" object))))))))

(defun ub (x)
  `(hello world ,x or . what))

(defun random (limit)
  (etypecase limit
    (fixnum
     (mod (read-time-stamp-counter) limit))
    (muerte::positive-bignum
     (let ((x (muerte::copy-bignum limit)))
       (dotimes (i (1- (muerte::%bignum-bigits x)))
	 (setf (memref x 2 :index i :type :unsigned-byte32)
	   (muerte::read-time-stamp-counter)))
       (setf x (muerte::bignum-canonicalize x))
       (loop while (>= x limit)
	   do (setf x (truncate x 2)))
       x))))

(define-primitive-function test-irq-pf ()
  ""
  (with-inline-assembly (:returns :nothing)
    (:int 113)
    (:ret)))

(defun test-irq (&optional eax ebx ecx edx)
  (multiple-value-bind (p1 p2)
      (with-inline-assembly (:returns :multiple-values)
	(:load-lexical (:lexical-binding eax) :eax)
	(:load-lexical (:lexical-binding ebx) :ebx)
	(:load-lexical (:lexical-binding ecx) :ecx)
	(:load-lexical (:lexical-binding edx) :edx)
	(:pushl :eax)
	(:pushl :ebx)
	(:jecxz 'dont-call)
	(:globally (:call (:edi (:edi-offset values) 80)))
       dont-call
	(:store-lexical (:lexical-binding eax) :eax :type t)
	(:store-lexical (:lexical-binding ebx) :ebx :type t)
	(:store-lexical (:lexical-binding ecx) :ecx :type t)
	(:store-lexical (:lexical-binding edx) :edx :type t)
	(:popl :ebx)
	(:popl :eax)
	(:movl 2 :ecx)
	(:stc))
    (values eax ebx ecx edx p1 p2)))

(defun null-primitive-function (x)
  "This function is just like identity, except it also calls a null primitive function.
Can be used to measure the overhead of primitive function."
  (with-inline-assembly (:returns :eax)
    (:load-lexical (:lexical-binding x) :eax)
    (% bytes 8 #xff #x97)		; (:call-local-pf ret-trampoline)
    (% bytes 32 #.(bt:slot-offset 'movitz::movitz-run-time-context 'movitz::ret-trampoline))))

(defun my-test-labels (x)
  (labels (#+ignore (p () (print x))
		    (q (y) (list x y)))
    (declare (ignore q))
    (1+ x)))

(defparameter *timer-stack* nil)
(defparameter *timer-prevstack* nil)
(defparameter *timer-esi* nil)
(defparameter *timer-frame* #100(nil))
(defparameter *timer-base* 2)
(defparameter *timer-variation* 1000)

(defun test-format (&optional timeout (x #xab))
  (let ((fasit (format nil "~2,'0X" x)))
    (test-timer timeout)
    (format t "~&Fasit: ~S" fasit)
    (loop
      (let ((x (format nil "~2,'0X" x)))
	(assert (string= fasit x) ()
	  "Failed tesT. Fasit: ~S, X: ~S" fasit x)))))

(defun test-clc (&optional timeout no-timer)
  (unless no-timer
    (test-timer timeout))
  (loop
    (funcall (find-symbol (string :test-clc) :clc))))

(defun test-timer (&optional timeout (base *timer-base*) (variation *timer-variation*))
  (setf (exception-handler 32)
    (lambda (exception-vector exception-frame)
      (declare (ignore exception-vector exception-frame))
;;;      (loop with f = *timer-frame*
;;;	  for o from 20 downto -36 by 4 as i upfrom 0
;;;	  do (setf (aref f i) (memref exception-frame o 0 :lisp)))
;;;      (let ((ts *timer-stack*))
;;;	(setf (fill-pointer ts) 0)
;;;	(loop for stack-frame = exception-frame then (stack-frame-uplink stack-frame)
;;;	    while (plusp stack-frame)
;;;	    do (multiple-value-bind (offset code-vector funobj)
;;;		   (stack-frame-call-site stack-frame)
;;;		 (vector-push funobj ts)
;;;		 (vector-push offset ts)
;;;		 (vector-push code-vector ts))))
;;;      (muerte::cli)
      (pic8259-end-of-interrupt 0)
      (when (eql #\esc (muerte.x86-pc.keyboard:poll-char))
	(break "Test-timer keyboard break."))
      (with-inline-assembly (:returns :nothing)
	(:compile-form (:result-mode :ecx) muerte.x86-pc::*screen*)
	(:shrl 2 :ecx)
	((:gs-override) :addb 1 (:ecx 158))
	((:gs-override) :movb #x40 (:ecx 159)))
      (do ((frame (stack-frame-uplink nil (current-stack-frame))
		  (stack-frame-uplink nil frame)))
	  ((plusp frame))
	(when (eq (with-inline-assembly (:returns :eax) (:movl :esi :eax))
		  (stack-frame-funobj nil frame))
	  (error "Double interrupt.")))
;;;      (dolist (range muerte::%memory-map-roots%)
;;;	(map-header-vals (lambda (x type)
;;;			   (declare (ignore type))
;;;			   x)
;;;			 (car range) (cdr range)))
      (map-stack-vector (lambda (x foo)
			  (declare (ignore foo))
			  x)
			nil
			(current-stack-frame))
      (with-inline-assembly (:returns :nothing)
	(:compile-form (:result-mode :ecx) muerte.x86-pc::*screen*)
	(:shrl 2 :ecx)
	((:gs-override) :movb #x20 (:ecx 159)))
      #+ignore (setf *timer-prevstack* *timer-stack*
		     *timer-stack* (muerte::copy-current-control-stack))
      (setf (pit8253-timer-mode 0) +pit8253-mode-single-timeout+
	    (pit8253-timer-count 0) (or timeout (+ base (random variation))))
;;;      (muerte::sti)
      ))
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :ecx) muerte.x86-pc::*screen*)
    (:shrl 2 :ecx)
    ((:gs-override) :movw #x4646 (:ecx 158)))
  (setf (pit8253-timer-mode 0) +pit8253-mode-single-timeout+
	(pit8253-timer-count 0) (or timeout (+ base (random variation))))
  (setf (pic8259-irq-mask) #xfffe)
  (pic8259-end-of-interrupt 0)
  (with-inline-assembly (:returns :nothing) (:sti)))

(defun wetweg (x)
  (memref-int (memref x 2 :type :unsigned-byte32) :physicalp nil :type :unsigned-byte8))

(defun test-throwing (&optional (x #xffff))
  (when x
    (test-timer x))
  (loop
    (catch 'foo
      (unwind-protect 
	  (funcall (lambda ()
		     (unwind-protect
			 (progn
;;;			   (unless (logbitp 9 (eflags))
;;;			     (break "Someone switched off interrupts!"))
;;;			   (incf (memref-int muerte.x86-pc::*screen* :type :unsigned-byte16))
			   (throw 'foo 'inner-peace))
		       (incf (memref-int muerte.x86-pc::*screen* :index 80 :type :unsigned-byte16)))))
	(incf (memref-int muerte.x86-pc::*screen* :index 160 :type :unsigned-byte16))))))

(defun fvf-textmode-screendump ()
  (muerte.ip4::ip4-init)
  (let* ((w muerte.x86-pc::*screen-width*)
	 (h muerte.x86-pc::*screen-height*)
	 (data (make-array (* w h)
			   :element-type 'character
			   :fill-pointer 0)))
    (loop for y below h
	do (loop for x below w
	       do (vector-push (code-char
				(ldb (byte 8 0)
				     (memref-int muerte.x86-pc::*screen*
						 :index (+ x (* y muerte.x86-pc::*screen-stride*))
						 :type :unsigned-byte16)))
			       data)))
    (muerte.ip4:tftp/ethernet-write :129.242.19.132 "movitz-screendump.txt" data
				    :quiet t
				    :mac (muerte.ip4::polling-arp
					  muerte.ip4::*ip4-router*
					  (lambda ()
					    (eql #\escape (muerte.x86-pc.keyboard:poll-char)))))))

(defvar *segment-descriptor-table*)


(defun genesis ()
  ;; (install-shallow-binding)
  (let ((extended-memsize 0))
    ;;  Find out how much extended memory we have 
    (setf (io-port #x70 :unsigned-byte8) #x18)
    (setf extended-memsize (* 256 (io-port #x71 :unsigned-byte8)))
    (setf (io-port #x70 :unsigned-byte8) #x17)
    (incf extended-memsize (io-port #x71 :unsigned-byte8))
    (format t "Extended memory: ~D KB~%" extended-memsize)

    (idt-init)

    (setf *segment-descriptor-table*	; Ensure we have a GDT with 16 entries, in static-space.
      (muerte::install-global-segment-table
       (muerte::dump-global-segment-table :entries 16)))
    
    (install-los0-consing :kb-size 500)
    #+ignore
    (install-los0-consing :kb-size (max 50 (truncate (- extended-memsize 2048) 2))))

  (setf *debugger-function* #'los0-debugger)
  (clos-bootstrap)
  (setf *package* (find-package "INIT"))
  ;; (install-shallow-binding)
  (let ((*repl-readline-context* (make-readline-context :history-size 16))
	#+ignore (*backtrace-stack-frame-barrier* (stack-frame-uplink (current-stack-frame)))
	#+ignore (*error-no-condition-for-debugger* t)
	#+ignore (*debugger-function* #'los0-debugger)
	(*package* *package*))
    (with-simple-restart (abort "Skip Los0 boot-up initialization.")
      (setf *cpu-features*
	(find-cpu-features))
      (format t "~&CPU features:~:[ none~;~{ ~A~#[~; and~:;,~]~}~].~%"
	      *cpu-features* *cpu-features*)
      ;; (muerte:asm :int 49)

      (setf *package* (find-package "INIT"))
      (when muerte::*multiboot-data*
	(set-textmode +vga-state-90x30+))
      
      (cond
       ((not (cpu-featurep :tsc))
	(warn "This CPU has no time-stamp-counter. Timer-related functions will not work."))
       (t (install-internal-time)
	  (warn "Internal-time will wrap in ~D days."
		(truncate most-positive-fixnum
			  (* internal-time-units-per-second 60 60 24)))))
      ;; (muerte.toplevel:invoke-toplevel-command :mapkey #\newline)
      #+ignore (let ((s (make-instance 'muerte.x86-pc:vga-text-console)))
		 (setf *standard-output* s
		       *standard-input* s
		       *terminal-io* s
		       *debug-io* s)))
;;;    (ignore-errors
;;;     (setf (symbol-function 'write-char)
;;;       (muerte.x86-pc.serial::make-serial-write-char :baudrate 38400))
;;;     (format t "~&Installed serial-port write-char."))
    (let ((* nil) (** nil) (*** nil)
	  (/ nil) (// nil) (/// nil)
	  (+ nil) (++ nil) (+++ nil)
	  (*readline-signal-keypresses* t))
      (format t "~&Movitz image Los0 build ~D." *build-number*)
      (handler-bind 
	  ((readline-keypress
	    (lambda (c)
	      (let ((key (readline-keypress-key c)))
		(when (eq :f12 key)
		  (fvf-textmode-screendump)
		  (format *query-io* "~&Dumped console contents by TFTP."))))))
	(loop
	  (catch :top-level-repl	; If restarts don't work, you can throw this..
	    (with-simple-restart (abort "Abort to the top command level.")
	      (read-eval-print)))))))

  (error "What's up? [~S]" 'hey))

(defun read (&optional input-stream eof-error-p eof-value recursive-p)
  (declare (ignore input-stream recursive-p))
  (let ((string (muerte.readline:contextual-readline *repl-readline-context*)))
    (simple-read-from-string string eof-error-p eof-value)))


#+ignore
(defun ztstring (physical-address)
  (let ((s (make-string (loop for i upfrom 0
			    until (= 0 (memref-int physical-address :index i :type :unsigned-byte8))
			    finally (return i)))))
    (loop for i from 0 below (length s)
	do (setf (char s i)
	     (code-char (memref-int physical-address :index i :type :unsigned-byte8))))
    s))

(defmacro do-default ((var &rest error-spec) &body init-forms)
  `(or (and (boundp ',var)
	    (symbol-value ',var))
       (setf (symbol-value ',var)
	 (progn ,@init-forms))
       ,(when error-spec
	  `(error ,@error-spec))))

#+ignore
(defun bridge (&optional (inside (do-default (*inside* "No inside NIC.")
				   (muerte.x86-pc.ne2k:ne2k-probe #x300)))
			 (outside (do-default (*outside* "No outside NIC.")
				    (muerte.x86-pc.ne2k:ne2k-probe #x280))))
  (let ((buffer (make-array +max-ethernet-frame-size+
			    :element-type '(unsigned-byte 8)
			    :fill-pointer t)))
    (loop 
      (ignore-errors
       (reset-device inside)
       (reset-device outside)
       (setf (promiscuous-p inside) t
	     (promiscuous-p outside) t)
       (loop
	 (when (receive inside buffer)
	   (transmit outside buffer))
	 (when (receive outside buffer)
	   (transmit inside buffer))
	 (case (muerte.x86-pc.keyboard:poll-char)
	   (#\escape (break "Under the bridge."))
	   (#\e (error "this is an error!"))))))))


(defparameter *write-barrier* nil)

(defun show-writes ()
  (loop with num = (length *write-barrier*)
      for i from 0 below num by 4
      initially (format t "~&Number of writes: ~D" (truncate num 4))
      do (format t "~&~D ~S: [~Z] Write to ~S: ~S."
		 i (aref *write-barrier* (+ i 3))
		 (aref *write-barrier* i)
		 (aref *write-barrier* i) (aref *write-barrier* (+ i 2))))
  (values))

(defun es-test (&optional (barrier-size 1000))
  (setf *write-barrier* (or *write-barrier*
			    (make-array (* 4 barrier-size) :fill-pointer 0))
	(fill-pointer *write-barrier*) 0
	(exception-handler 13) #'general-protection-handler
	(segment-register :es) 0)
  (values))

(defun general-protection-handler (vector dit-frame)
  (assert (= vector 13))
  (let ((eip (dit-frame-ref nil dit-frame :eip :unsigned-byte32)))
    (assert (= #x26 (memref-int eip :offset 0 :type :unsigned-byte8 :physicalp nil))) ; ES override prefix?
    (let ((opcode (memref-int eip :offset 1 :type :unsigned-byte8 :physicalp nil))
	  (mod/rm (memref-int eip :offset 2 :type :unsigned-byte8 :physicalp nil)))
      (if (not (= #x89 opcode))
	  (interrupt-default-handler vector dit-frame)
	(let ((value (ecase (ldb (byte 3 3) mod/rm)
		       (0 (dit-frame-ref nil dit-frame :eax :lisp))
		       (3 (dit-frame-ref nil dit-frame :ebx :lisp)))))
	  ;; If we return, don't execute with the ES override prefix:
	  (setf (dit-frame-ref nil dit-frame :eip :unsigned-byte32) (1+ eip))
	  ;; If value isn't a pointer, we don't care..
	  (when (typep value 'pointer)
	    (multiple-value-bind (object offset)
		(case (logand mod/rm #xc7)
		  (#x40			; (:movl <value> (:eax <disp8>))
		   (values (dit-frame-ref nil dit-frame :eax)
			   (memref-int eip :offset 3 :type :signed-byte8 :physicalp nil)))
		  (#x43			; (:movl <value> (:ebx <disp8>))
		   (values (dit-frame-ref nil dit-frame :ebx)
			   (memref-int eip :offset 3 :type :signed-byte8 :physicalp nil)))
		  (#x44			; the disp8/SIB case
		   (let ((sib (memref-int eip :offset 3 :type :unsigned-byte8 :physicalp nil)))
		     (case sib
		       ((#x19 #x0b)
			(values (dit-frame-ref nil dit-frame :ebx)
				(+ (dit-frame-ref nil dit-frame :ecx :unsigned-byte8)
				   (memref-int eip :offset 4 :type :signed-byte8 :physicalp nil))))
		       ((#x1a)
			(values (dit-frame-ref nil dit-frame :ebx)
				(+ (dit-frame-ref nil dit-frame :edx :unsigned-byte8)
				   (memref-int eip :offset 4 :type :signed-byte8 :physicalp nil))))))))
	      (when (not object)
		(setf (segment-register :es) (segment-register :ds))
		(break "[~S] With value ~S, unknown movl at ~S: ~S ~S ~S ~S"
		       dit-frame value eip
		       (memref-int eip :offset 1 :type :unsigned-byte8 :physicalp nil)
		       (memref-int eip :offset 2 :type :unsigned-byte8 :physicalp nil)
		       (memref-int eip :offset 3 :type :unsigned-byte8 :physicalp nil)
		       (memref-int eip :offset 4 :type :unsigned-byte8 :physicalp nil)))
	      (check-type object pointer)
	      (check-type offset fixnum)
	      (let ((write-barrier *write-barrier*)
		    (location (object-location object)))
		(assert (not (location-in-object-p
			      (los0::space-other (%run-time-context-slot 'nursery-space))
			      location)) ()
		  "Write ~S to old-space at ~S." value location)
		(unless (or (eq object write-barrier)
			    #+ignore
			    (location-in-object-p (%run-time-context-slot 'nursery-space)
						  location)
			    (location-in-object-p (%run-time-context-slot 'stack-vector)
						  location))
		  (if (location-in-object-p (%run-time-context-slot 'nursery-space)
					    location)
		      (vector-push 'stack-actually write-barrier)		      
		    (vector-push object write-barrier))
		  (vector-push offset write-barrier)
		  (vector-push value write-barrier)
		  (unless (vector-push eip write-barrier)
		    (setf (segment-register :es) (segment-register :ds))
		    (break "Write-barrier is full: ~D" (length write-barrier))))))))))))

;;;;;;;;;;;;;;;;;; Shallow binding

(define-primitive-function dynamic-variable-install-shallow ()
  "Install each dynamic binding entry between that in ESP
 (offset by 4 due to the call to this primitive-function!)
and current dynamic-env. Preserve EDX."
  (with-inline-assembly (:returns :nothing)
    (:leal (:esp 4) :ecx)		; first entry
   install-loop
    (:locally
      (:cmpl :ecx (:edi (:edi-offset dynamic-env))))
    (:je 'install-completed)
    (:movl (:ecx 0) :eax)		; binding's name
    (:movl (:eax (:offset movitz-symbol value))
	   :ebx)			; old value into EBX
    (:movl :ebx (:ecx 4))		; save old value in scratch
    (:movl (:ecx 8) :ebx)		; new value..
    (:movl :ebx				; ..into symbol's value slot
	   (:eax (:offset movitz-symbol value)))
    (:movl (:ecx 12) :ecx)		; iterate next binding
    (:jmp 'install-loop)
   install-completed
    (:ret)))

(define-primitive-function dynamic-variable-uninstall-shallow (dynamic-env)
  "Uninstall each dynamic binding between 'here' (i.e. the current 
dynamic environment pointer) and the dynamic-env pointer provided in EDX.
This must be done without affecting 'current values'! (i.e. eax, ebx, ecx, or CF),
and also EDX must be preserved."
  (with-inline-assembly (:returns :nothing)
    (:jc 'ecx-ok)
    (:movl 1 :ecx)
   ecx-ok
    (:locally (:movl :ecx (:edi (:edi-offset raw-scratch0))))
    (:locally (:movl :eax (:edi (:edi-offset scratch1))))
    (:locally (:movl :ebx (:edi (:edi-offset scratch2))))
    
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
   uninstall-loop
    (:cmpl :edx :ecx)
    (:je 'uninstall-completed)
    (:movl (:ecx 0) :eax)		; symbol
    (:movl (:ecx 4) :ebx)		; old value
    (:movl :ebx (:eax (:offset movitz-symbol value))) ; reload old value
    (:movl (:ecx 12) :ecx)
    (:jmp 'uninstall-loop)
   uninstall-completed

    (:locally (:movl (:edi (:edi-offset raw-scratch0)) :ecx))
    (:locally (:movl (:edi (:edi-offset scratch1)) :eax))
    (:locally (:movl (:edi (:edi-offset scratch2)) :ebx))
    (:stc)
    (:ret)))

(define-primitive-function dynamic-unwind-next-shallow (dynamic-env)
  "Locate the next unwind-protect entry between here and dynamic-env/EAX.
If no such entry is found, return (same) dynamic-env in EAX and CF=0.
Otherwise return the unwind-protect entry in EAX and CF=1. Preserve EDX.
Point is: Return the 'next step' in unwinding towards dynamic-env.
Note that it's an error if dynamic-env isn't in the current dynamic environment,
it's supposed to have been found by e.g. dynamic-locate-catch-tag."
  ;; XXX: Not really sure if there's any point in the CF return value,
  ;;      because I don't think there's ever any need to know whether
  ;;      the returned entry is an unwind-protect or the actual target.
  (with-inline-assembly (:returns :nothing)
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :eax))
    (:locally (:movl :eax (:edi (:edi-offset scratch2)))) ; Free up EAX
    ;; (:globally (:movl (:edi (:edi-offset unwind-protect-tag)) :ebx))
    (:locally (:movl (:edi (:edi-offset dynamic-env)) :ecx))
    
   search-loop
    (:jecxz '(:sub-program () (:int 63)))
    (:locally (:bound (:edi (:edi-offset stack-bottom)) :ecx))

    (:locally (:cmpl :ecx (:edi (:edi-offset scratch2))))
    (:je 'found-dynamic-env)

    (:movl (:ecx 4) :ebx)
    (:globally (:cmpl :ebx (:edi (:edi-offset unwind-protect-tag))))
    (:je 'found-unwind-protect)

    ;; If this entry is a dynamic variable binding, uninstall it.
    (:movl (:ecx) :eax)			; symbol?
    (:testb 3 :al)			;
    (:jz 'not-variable-binding)		; not symbol?
    (:movl :ebx (:eax (:offset movitz-symbol value))) ; uninstall.
   not-variable-binding
    (:movl (:ecx 12) :ecx)		; proceed search
    (:jmp 'search-loop)
   found-unwind-protect
    (:stc)
   found-dynamic-env
    (:movl :ecx :eax)
    (:ret)))

(define-primitive-function dynamic-variable-lookup-shallow (symbol)
  "Load the dynamic value of SYMBOL into EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:movl (:ebx (:offset movitz-symbol value)) :eax)
    (:ret)))

(define-primitive-function dynamic-variable-store-shallow (symbol value)
  "Store VALUE (ebx) in the dynamic binding of SYMBOL (eax).
   Preserves EBX and EAX."
  (with-inline-assembly (:returns :multiple-values)
    (:movl :ebx (:eax (:offset movitz-symbol value)))
    (:ret)))

(defun install-shallow-binding (&key quiet)
  (unless quiet
    (warn "Installing shallow-binding strategy.."))
  (without-interrupts
    (macrolet ((install (slot function)
		 `(setf (%run-time-context-slot ',slot) (symbol-value ',function))))
      (install muerte:dynamic-variable-install dynamic-variable-install-shallow)
      (install muerte:dynamic-variable-uninstall dynamic-variable-uninstall-shallow)
      (install muerte::dynamic-unwind-next dynamic-unwind-next-shallow)
      (install muerte::dynamic-variable-store dynamic-variable-store-shallow)
      (install muerte::dynamic-variable-lookup dynamic-variable-lookup-shallow))
    (labels ((install-shallow-env (env)
	       "We use this local function in order to install dynamic-env slots
                    in reverse order, by depth-first recursion."
	       (unless (eq 0 env)
		 (install-shallow-env (memref env 12))
		 (let ((name (memref env 0)))
		   (when (symbolp name)
		     (setf (memref env 4)
		       (%symbol-global-value name))
		     (setf (%symbol-global-value name)
		       (memref env 8)))))))
      (install-shallow-env (load-global-constant dynamic-env :thread-local t))))
  (values))

(defun deinstall-shallow-binding (&key quiet)
  (unless quiet
    (warn "Deinstalling shallow-binding strategy.."))
  (without-interrupts
    (macrolet ((install (slot)
		 `(setf (%run-time-context-slot ',slot) (symbol-value ',slot))))
      (install muerte:dynamic-variable-install)
      (install muerte:dynamic-variable-uninstall)
      (install muerte::dynamic-unwind-next)
      (install muerte::dynamic-variable-store)
      (install muerte::dynamic-variable-lookup))
    (loop for env = (load-global-constant dynamic-env :thread-local t)
	then (memref env 12)
	while (plusp env)
	do (let ((name (memref env 0)))
	     (when (symbolp name)
	       (setf (%symbol-global-value name)
		 (memref env 4)))))
    (values)))

(genesis)

