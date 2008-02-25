;;;;------------------ -*- movitz-mode: t -*--------------------------
;;;; 
;;;;    Copyright (C) 2007, Frode Vatvedt Fjeld
;;;; 
;;;; Filename:      scratch.lisp
;;;; Description:   Misc. testing code etc.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: scratch.lisp,v 1.3 2008/02/23 22:28:55 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :scratch)

(in-package los0)

#+ignore
(defun set.2 ()
  (let ((*var-used-in-set-tests* 'a)
	(var '*var-used-in-set-tests*))
    (declare (special *var-used-in-set-tests*))
    (values
     (let ((*var-used-in-set-tests* 'c))
       (list (set var 'b) *var-used-in-set-tests* (symbol-value var)))
     *var-used-in-set-tests*)))
;;   (b c b)
;;   b)

#+ignore
(defun test-lend-constant ()
  (let ((symbols '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
	(table (make-hash-table :test #'eq)))
    (loop for sym in symbols
	  for i from 1
	  do (setf (gethash sym table) i))
    (let ((sum 0))
      (values (maphash #'(lambda (k v)
                           (assert (eq (elt symbols (1- v)) k))
                           (incf sum v))
                       table)
              sum))))

#+ignore
(defun test-aux (x y &aux (sum (+ x y)))
  sum)

#+ignore
(defun mapc.error.3 ()
  (mapc #'append))

#+ignore
(defun with-hash-table-iterator.12 ()
  (block done
    (let ((x :bad))
      (declare (special x))
      (let ((x :good))
	(with-hash-table-iterator (m (return-from done x))
          (declare (special x))))))
  :good)

#+ignore
(defun string.15 ()
  (when (> char-code-limit 65536)
    (loop for i = (random char-code-limit)
        for c = (code-char i)
        for s = (and c (string c))
        repeat 2000
        when (and c
                  (or (not (stringp s))
                      (not (= (length s) 1))
                      (not (eql c (char s 0)))))
        collect (list i c s)))
  nil)

(defun x (bios32)
  (warn "X: ~S" (memref-int bios32))
  (warn "X: ~S" (= (memref-int bios32) #x5f32335f)))

(defun setfint (x o)
  (setf (memref x o :type :unsigned-byte32) 0))

(defun fint (x)
  (memref-int x :type :unsigned-byte32 :physicalp t))

(defun good ()
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    ((:gs-override) :movl (#x1000000) :ecx)))

(defun (setf good) (x)
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    (:compile-form (:result-mode :untagged-fixnum-ecx) x)
    ((:gs-override) :movl :ecx (#x1000000))))

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

(defun display-hash (x)
  (loop for k being the hash-keys of x using (hash-value v)
      do (format t "~&~S => ~S" k v))
  (values))

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

(defmethod cook :after ((f food))
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
    (:% :bytes 8 #xff #x97)		; (:call-local-pf ret-trampoline)
    (:% :bytes 32 #.(bt:slot-offset 'movitz::movitz-run-time-context 'movitz::ret-trampoline))))

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

(defun test-clc (&optional (timeout #xfffe) no-timer)
  (unless no-timer
    (test-timer timeout))
  (loop
    (funcall (find-symbol (string :test-clc) :clc))))

(defun test-timer (function
                   &key (base *timer-base*)
                   (variation *timer-variation*)
                   (timeout (+ base (random variation))))
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
          (when (eql #\esc (muerte.x86-pc.keyboard:poll-char))
            (break "Test-timer keyboard break."))
          (with-inline-assembly (:returns :nothing)
            (:compile-form (:result-mode :ecx) muerte.x86-pc::*screen*)
            (:shrl 2 :ecx)
            ((:gs-override) :addb 1 (:ecx 158))
            ((:gs-override) :movb #x40 (:ecx 159)))
          (do ((frame (muerte::stack-frame-uplink nil (muerte::current-stack-frame))
                      (muerte::stack-frame-uplink nil frame)))
              ((plusp frame))
            (when (eq (with-inline-assembly (:returns :eax) (:movl :esi :eax))
                      (muerte::stack-frame-funobj nil frame))
              (error "Double interrupt.")))
;;;      (dolist (range muerte::%memory-map-roots%)
;;;	(map-header-vals (lambda (x type)
;;;			   (declare (ignore type))
;;;			   x)
;;;			 (car range) (cdr range)))
          (map-stack-vector #'muerte::identity* nil (muerte::current-stack-frame))
          (with-inline-assembly (:returns :nothing)
            (:compile-form (:result-mode :ecx) muerte.x86-pc::*screen*)
            (:shrl 2 :ecx)
            ((:gs-override) :movb #x20 (:ecx 159)))
          #+ignore (setf *timer-prevstack* *timer-stack*
                         *timer-stack* (muerte::copy-current-control-stack))
          (pic8259-end-of-interrupt 0)
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
  (with-inline-assembly (:returns :nothing) (:sti))
  (unwind-protect
       (when function
         (funcall function))
    (muerte::cli)
    (setf (pic8259-irq-mask) #xffff)))

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

#+ignore
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


(defun memdump (start length)
  (loop for addr upfrom start repeat length
      collect (memref-int addr :type :unsigned-byte8)))

(defun plus (a b)
  (+ (muerte::check-the fixnum a)
     (muerte::check-the fixnum b)))

(defun vector-non-dups (vector)
  "Count the number of unique elements in vector."
  (loop for i from 1 to (length vector)
      for x across vector
      count (not (find x vector :start i))))

(defun blit (buffer)
  (loop for i from 0 below 16000
      do (setf (memref-int #xa0000 :index i :type :unsigned-byte32)
               (memref buffer 2 :index i :type :unsigned-byte32))))

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
			      (los0::space-other (%run-time-context-slot nil 'nursery-space))
			      location)) ()
		  "Write ~S to old-space at ~S." value location)
		(unless (or (eq object write-barrier)
			    #+ignore
			    (location-in-object-p (%run-time-context-slot nil 'nursery-space)
						  location)
			    (location-in-object-p (%run-time-context-slot nil 'stack-vector)
						  location))
		  (if (location-in-object-p (%run-time-context-slot nil 'nursery-space)
					    location)
		      (vector-push 'stack-actually write-barrier)		      
		    (vector-push object write-barrier))
		  (vector-push offset write-barrier)
		  (vector-push value write-barrier)
		  (unless (vector-push eip write-barrier)
		    (setf (segment-register :es) (segment-register :ds))
		    (break "Write-barrier is full: ~D" (length write-barrier))))))))))))
