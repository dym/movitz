;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001,2000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      los0.lisp
;;;; Description:   Top-level initialization file.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Dec  1 18:08:32 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: los0.lisp,v 1.2 2004/01/19 11:23:43 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :los0 :load-priority 0)

(require :common-lisp)
(require :x86-pc/all)
(require :x86-pc/io-space)
(require :x86-pc/ne2k)
(require :x86-pc/floppy)

(require :lib/readline)
(require :lib/toplevel)
(require :lib/net/ip6)
(require :lib/net/ip4)
(require :lib/repl)

(defpackage muerte.init
  (:use muerte.cl muerte muerte.lib muerte.x86-pc muerte.readline muerte.toplevel
	muerte.ethernet
	muerte.ip6
	muerte.ip4
	muerte.mop
	muerte.debug
	#+ignore muerte.x86-pc.serial))
	
(in-package muerte.init)

(declaim (special muerte::*multiboot-data*))

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

(defun test-upload (x)
  ;; (warn "Test-upload blab la bla!!")
  (setf x (cdr x))
  x)

;;;(defun zzz (x)
;;;  (multiple-value-bind (symbol status)
;;;      (values-list x)
;;;    (warn "sym: ~S, stat: ~S" symbol status)))
;;;
;;;(defun test-loop (x)
;;;  (format t "test-loop: ~S~%"
;;;	  (loop for i from 0 to 10 collect x)))
;;;	      
;;;(defun delay (time)
;;;  (dotimes (i time)
;;;    (with-inline-assembly (:returns :nothing)
;;;      (:nop)
;;;      (:nop))))
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

#+ignore
(defun test-m-v-call ()
  (multiple-value-call #'format t "~@{ ~D~}~%"
		       'a (values) 'b (test-loop 1) (make-values)
		       'c 'd  'e (make-no-values) 'f))

(defun make-values ()
  (values 0 1 2 3 4 5))

(defun xx ()
  (format t "wefewf")
  (with-inline-assembly (:returns :untagged-fixnum-ecx)
    (:sbbl :edx :edx)
    (:andl :edx :ecx)
    (:leal (:edx :ecx 1) :ecx)))

(defun xfoo (f) 
  (multiple-value-bind (a b c d)
      (multiple-value-prog1 (make-values)
	(format t "hello world"))
    (format t "~&a: ~S, b: ~S, c: ~S, d: ~S" a b c d f)))


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
(defun test-rest (&optional a0 a1 a3 &rest args)
  (declare (dynamic-extent args))
  (format t "args: ~S, ~S, ~S: ~S~%" a0 a1 a3 args))


(defun test-return ()
  (print (block nil
	   (values 'x 'y (if (foo) (return 'foo) (return-from test-return 'not-foo)) 'bar)))
  5)

#+ignore
(defun test-lexthrow (x)
  (apply (lambda (a b)
	   (if (plusp a) 0 (return-from test-lexthrow (+ a b))))
	 x))

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


(defstruct xxx
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
(defun sloo (x y)
  'sllooo)

#+ignore
(defun test-throw (tag)
  (unwind-protect
      (warn "throw: ~Z" (throw tag (values 'throw1 (make-values) 'throw2)))
    (warn "Something happened: ~W" (make-values))
    #+ignore (return-from test-throw 'interrupted-value))
  (error "Huh?"))

#+ignore
(defun test-catch ()
  (catch 'test-tag
    (test-throw 'test-tag)
    (format t "Hello world")))

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

(defun test-fixed (x y z)
  (warn "x: ~W, y: ~W, z: ~W" x y z))

(defun test-closure (x)
  (warn "lending x: ~W" x)
  (values (lambda ()
	    (warn "borrowed x: ~W" x)
	    (* x 2))
	  (lambda (y)
	    (setq x y))))

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
   (t (&rest args) (declare (ignore args)) 27)))

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

(defun foo (x)
  (funcall (cdr x) 'abba))

(defun test-pie (n pie)
  (dotimes (i n)
    (pie-filling pie)))

(defclass pie (food)
  ((filling :accessor pie-filling 
	    :initarg :filling
	    :initform 'apple))
  #+ignore (:default-initargs :filling (if (foo) 'apple 'banana)))

#+ignore
(defclass pie2 (food)
  ((filling :accessor pie-filling 
	    :initarg :filling
	    :initform nil)))

;;;(defmethod cook ((p (eql 'pie)))
;;;  (warn "Won't really cook a symbolic pie!")
;;;  (values))
;;;
;;;(defmethod cook ((p (eql 'pudding)))
;;;  'cooked-pudding)

;;;(defmethod slot-value-using-class :after (class (pie pie2) slot)
;;;  (warn "HEy, don't poke inside my pie2!"))

;;;(defmethod cook :after ((p symbol))
;;;  (warn "A symbol may or may not have been cooked."))

;;;(defmethod cook ((p pie))
;;;  (cond
;;;   ((eq 'banana (pie-filling p))
;;;    (print "Won't cook a banana-pie, trying next.")
;;;    (call-next-method))
;;;   (t (print "Cooking a pie.")
;;;      (setf (pie-filling p) (list 'cooked (pie-filling p))))))

;;;(defmethod cook :before ((p pie))
;;;  (declare (ignore p))
;;;  (print "A pie is about to be cooked."))
;;;
;;;(defmethod cook :after ((p pie))
;;;  (declare (ignore p))
;;;  (print "A pie has been cooked."))

(defun assess-cpu-frequency ()
  "Assess the CPU's frequency in units of 1024 Hz."
  (assert (cpu-featurep :tsc) ()
    "This function requires a CPU with the time-stamp-counter feature.")
  (let ((s0 (loop with x = (rtc-register :second)
		for s0 = (rtc-register :second)
		while (= x s0)
		finally (return s0))))
    (multiple-value-bind (c0-lo c0-mid c0-hi)
	(read-time-stamp-counter)
      (loop while (= s0 (rtc-register :second)))
      (multiple-value-bind (c1-lo c1-mid c1-hi)
	  (read-time-stamp-counter)
	(+ (ash (- c1-hi c0-hi) 38)
	   (ash (- c1-mid c0-mid) 14)
	   (ash (+ 512 (- c1-lo c0-lo)) -10))))))

(defun report-cpu-frequency ()
  (multiple-value-bind (mhz khz)
      (truncate (assess-cpu-frequency) 976)
    (format t "~&CPU frequency: ~D.~2,'0D MHz.~%" mhz (round khz 10)))
  (values))

(defun mvtest ()
  (multiple-value-call #'list (round 5 2))
  (list (memref-int #x1000000 0 0 :unsigned-byte8)
	(memref-int #x1000004 0 0 :unsigned-byte8)))





;;;;;

;;;;;;;;;;;;;;; CL

(defun install-internal-time ()
  "Figure out this CPU's internal-time-unit. Warning: This process takes about 1.5 seconds."
  (if (not (cpu-featurep :tsc))
      (warn "This CPU has no time-stamp-counter. Timer-related functions will not work.")
    (let ((s0 (loop with x = (rtc-register :second)
		  for s0 = (rtc-register :second)
		  while (= x s0)
		  finally (return s0))))
      (multiple-value-bind (c0-lo c0-mid c0-hi)
	  (read-time-stamp-counter)
	(loop while (= s0 (rtc-register :second)))
	(multiple-value-bind (c1-lo c1-mid c1-hi)
	    (read-time-stamp-counter)
	  (let ((lo-res (+ (ash (- c1-hi c0-hi) 24)
			   (- c1-mid c0-mid))))
	    (cond
	     ((> lo-res 100)
	      (setf (symbol-function 'get-internal-run-time)
		(lambda ()
		  (multiple-value-bind (lo mid hi)
		      (read-time-stamp-counter)
		    (declare (ignore lo))
		    (dpb hi (byte 5 24) mid))))
	      (setf internal-time-units-per-second lo-res))
	     (t ;; This is for really slow machines, like bochs..
	      (setf (symbol-function 'get-internal-run-time)
		(lambda ()
		  (multiple-value-bind (lo mid hi)
		      (read-time-stamp-counter)
		    (declare (ignore hi))
		    (dpb mid
			 (byte 19 10)
			 (ldb (byte 10 14) lo)))))
	      (setf internal-time-units-per-second
		(+ (ash (ldb (byte 19 0) (- c1-mid c0-mid)) 10)
		   (ldb (byte 10 14) (- c1-lo c0-lo))))))))))))

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
  (apply #'backtrace args))

(define-toplevel-command :cpu-reset ()
  (when (y-or-n-p "Really reset CPU?")
    (muerte.x86-pc.keyboard:cpu-reset))
  (values))

(define-toplevel-command :decimal (&optional x-list)
  (flet ((do-print (x)
	   (typecase x
	     #+ignore
	     (float
	      (format t "~&~W ~~ ~,3F" x x))
	     (number
	      (case *print-base*
		(16 (format t "~&~W = ~D" x x))
		(10 (format t "~&~W = #x~X" x x))
		(t (format t "~&~W = ~D. = #x~X" x x x)))
	      #+ignore
	      (when (typep x 'ratio)
		(format t " ~~ ~,3F" x)))
	     (t (fresh-line)
		(write x :radix nil :base (case *print-base* (10 16) (t 10)))))
	   x))
    (if x-list
	(do-print (eval x-list))
      (dolist (x cl:/ (values-list cl:/))
	(do-print x))))
  (values))

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
    (let ((condition *debugger-condition*))
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
	  (format t "~&[restarts suppressed]")
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

(muerte.toplevel:define-toplevel-command :mapkey (code-char)
  (let ((char (etypecase code-char
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
    (invoke-toplevel-command :error)
    (loop
      (with-simple-restart (abort "Abort to command level ~D." (1+ *repl-level*))
	(read-eval-print)))))

(defun genesis ()
  #+ignore
  (let ((extended-memsize 0))
    ;;  Find out how much extended memory we have 
    (setf (io-port #x70 :unsigned-byte8) #x18)
    (setf extended-memsize (* 256 (io-port #x71 :unsigned-byte8)))
    (setf (io-port #x70 :unsigned-byte8) #x17)
    (incf extended-memsize (io-port #x71 :unsigned-byte8))
    (format t "Extended memory: ~D KB" extended-memsize))

  (let ((*repl-readline-context* (make-readline-context :history-size 16))
	(*backtrace-stack-frame-barrier* (stack-frame-uplink (current-stack-frame)))
	#+ignore (*error-no-condition-for-debugger* t)
	(*debugger-function* #'los0-debugger))

    (with-simple-restart (continue "Abort LOS0 boot-up initialization.")
      (setf *cpu-features*
	(find-cpu-features))
      (format t "~&CPU features:~:[ none~;~{ ~A~#[~; and~:;,~]~}~].~%"
	      *cpu-features* *cpu-features*)
      (install-internal-time)
      (funcall #'idt-init)
      ;; (muerte:asm :int 49)

      (setf *package* (find-package "INIT"))
      (clos-bootstrap)
      ;; (muerte.toplevel:invoke-toplevel-command :mapkey #\newline)
      #+ignore (let ((s (make-instance 'muerte.x86-pc:vga-text-console)))
		 (setf *standard-output* s
		       *standard-input* s
		       *terminal-io* s
		       *debug-io* s)))
    (loop 
      (catch 'top-level-repl		; If restarts don't work, you can throw this..
	(with-simple-restart (abort "Abort to the top command level.")
	  (read-eval-print)))))
  
  (error "What's up? [~S]" 'hey))

(defun handle-warning (condition)
  (format t "Handle-warning: ~S" condition)
  (throw :debugger nil))

(defun zoo (x)
  (cond
   (x (warn "foo"))
   (t nil))
  nil)

#+ignore
(defun progntest ()
  (unwind-protect
      (progn (print 'x) 'foo 'bar)
    (print 'y)))

#+ignore
(defun test-restart (x)
  (with-simple-restart (test "It's just a test, so ignore ~S." x)
    (check-type x symbol)))

#+ignore
(defun condtest ()
  (format t "You have two attempts..")
  (handler-bind
      ((error #'(lambda (c) (print 'x) (warn "An error occurred..")))
       (warning #'handle-warning)
       (t #'invoke-debugger))
    (read-eval-print)
    (read-eval-print)))

#+ignore
(defun ztstring (physical-address)
  (let ((s (make-string (loop for i upfrom 0
			    until (= 0 (memref-int physical-address 0 i :unsigned-byte8 t))
			    finally (return i)))))
    (loop for i from 0 below (length s)
	do (setf (char s i)
	     (code-char (memref-int physical-address 0 i :unsigned-byte8 t))))
    s))

(defmacro do-default ((var &rest error-spec) &body init-forms)
  `(or (and (boundp ',var)
	    (symbol-value ',var))
       (setf (symbol-value ',var)
	 (progn ,@init-forms))
       ,(when error-spec
	  `(error ,@error-spec))))

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
	   (#\esc (break "Under the bridge."))
	   (#\e (error "this is an error!"))))))))

    
(genesis)
