;;;;------------------ -*- movitz-mode: t -*--------------------------
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
;;;; $Id: los0.lisp,v 1.52 2008-04-17 19:31:13 ffjeld Exp $
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
(require :lib/net/dhcp)
(require :lib/repl)

(require :lib/threading)

;; (require :lice-0.1/all)

(defpackage los0
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
	#:muerte.x86-pc.serial
	#:threading))

(require :lib/shallow-binding)
(require :los0-gc)			; Must come after defpackage.
;; (require :asteroids)
(require :scratch)

(in-package los0)

;; (defun load-ansi-tests ()
;;   (load "ansi-tests.lisp"))

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
      (loop with start-time = (get-internal-run-time)
	  with end-time = (+ start-time (* seconds internal-time-units-per-second))
	  while (< (get-internal-run-time) end-time))))
  (values))


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
		      (muerte::current-dynamic-context)))
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

;;;(muerte.toplevel:define-toplevel-command :bochs-trace (form)
;;;  (muerte::with-bochs-tracing ()
;;;    (eval form)))

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
  (let ((*debugger-dynamic-context* (muerte::current-dynamic-context))
        (*standard-output* *debug-io*)
        (*standard-input* *debug-io*)
        (*debugger-condition* condition)
        (*package* (or (and (packagep *package*) *package*)
                       (find-package "LOS0")
                       (find-package "USER")
                       (find-package "COMMON-LISP")
                       (error "Unable to find any package!")))
        (*repl-prompt-context* #\d)
        #+ignore (*repl-readline-context* (or *repl-readline-context*
                                              (make-readline-context :history-size 16))))
    (let ((*print-safely* t))
      (invoke-toplevel-command :error))
    (loop
       (with-simple-restart (abort "Abort to command level ~D." (1+ *repl-level*))
         (read-eval-print)))))


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



(defvar *segment-descriptor-table*)

(defun format-segment-table (table &key (start 0) (end (truncate (length table) 2)))
  (loop for i from start below end
      as selector = (* i 8)
      do (format t "~&~3X: base: #x~8,'0X, limit: #x~5,'0X, type-s-dpl-p: ~8,'0b, avl-x-db-g: ~4,'0b~%"
		 selector
		 (* 4 (segment-descriptor-base-location table selector))
		 (segment-descriptor-limit table selector)
		 (segment-descriptor-type-s-dpl-p table selector)
		 (segment-descriptor-avl-x-db-g table selector)))
  (values))


(defun genesis ()
  ;; (install-shallow-binding)
  (setf *debugger-function* #'los0-debugger)
  (let ((extended-memsize 0))
    ;;  Find out how much extended memory we have 
    (setf (io-port #x70 :unsigned-byte8) #x18)
    (setf extended-memsize (* 256 (io-port #x71 :unsigned-byte8)))
    (setf (io-port #x70 :unsigned-byte8) #x17)
    (incf extended-memsize (io-port #x71 :unsigned-byte8))
    ;; (format t "Extended memory: ~D KB~%" extended-memsize)

    (idt-init)

    (setf *segment-descriptor-table*	; Ensure we have a GDT with 16 entries, in static-space.
      (setf (global-segment-descriptor-table)
	(muerte::dump-global-segment-table :entries 16)))

    #+ignore (install-los0-consing :kb-size (* 2 1024))
    (let* ((buf (check-the fixnum (%run-time-context-slot nil 'muerte::nursery-space)))
           (current (check-the fixnum (memref buf 4)))
           (end (check-the fixnum (memref buf 0)))
           (free-kb (1- (truncate (- end current 32) 256))))
      (cond
        ((< free-kb 1)
         (warn "Not enough memory to install GC (~D bytes)." (- end buf 16)))
        (t (format t "~&Installing los0-GC with ~D KB.~%" free-kb)
           (install-los0-consing :kb-size (truncate free-kb 2))))))

  #+ignore
  (loop
     (catch :top-level-repl ; If restarts don't work, you can throw this..
       (with-simple-restart (abort "Abort to the top command level.")
         (read-eval-print))))

  (set-textmode +vga-state-90x30+)
  (let ((muerte::*error-no-condition-for-debugger* t))
    (clos-bootstrap))

  (setf *package* (find-package "LOS0"))

  ;; (install-shallow-binding)
  (let ((*repl-readline-context* (make-readline-context :history-size 16))
	#+ignore (*backtrace-stack-frame-barrier* (stack-frame-uplink (current-stack-frame)))
	#+ignore (*error-no-condition-for-debugger* t)
	#+ignore (*debugger-function* #'los0-debugger)
	#+ignore (*package* *package*))
    (with-simple-restart (abort "Skip Los0 boot-up initialization.")
      (setf *cpu-features*
	(find-cpu-features))
      (format t "~&CPU features:~:[ none~;~{ ~A~#[~; and~:;,~]~}~].~%"
	      *cpu-features* *cpu-features*)
      ;; (muerte:asm :int 49)

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
    (when (fboundp 'muerte::make-ansi-loop-universe)
      (setf muerte::*loop-ansi-universe*
	    (muerte::make-ansi-loop-universe nil)))
    (setf threading:*segment-descriptor-table-manager*
      (make-instance 'threading:segment-descriptor-table-manager))
    
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



(genesis)

