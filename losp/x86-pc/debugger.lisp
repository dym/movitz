;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of TromsÅ¯, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      debugger.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov 22 10:09:18 2002
;;;;                
;;;; $Id: debugger.lisp,v 1.1 2004/01/13 11:05:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :x86-pc/debugger)

(defpackage muerte.debug
  (:use muerte.cl muerte muerte.x86-pc)
  (:export *debugger-function*
	   *debugger-condition*
	   *backtrace-conflate-names*
	   *backtrace-do-conflate*
	   *backtrace-max-frames*
	   *backtrace-max-args*
	   *backtrace-on-error*
	   *backtrace-stack-frame-barrier*
	   *backtrace-do-fresh-lines*
	   *backtrace-be-spartan-p*
	   *backtrace-print-length*
	   *backtrace-print-level*
	   backtrace
	   ))

(in-package muerte.debug)

(defparameter *backtrace-be-spartan-p* nil)

(defparameter *backtrace-conflate-names*
    '(nil funcall
      apply
      backtrace

      muerte::funcall%0ops
      muerte::funcall%1op
      muerte::funcall%2op
      muerte::funcall%3op
      muerte::interrupt-default-handler
      muerte::eval-cons
      muerte::eval-funcall
      muerte::eval-form
      muerte::slow-method-lookup
      muerte::do-slow-method-lookup
      muerte::initial-discriminating-function
      muerte::discriminating-function-max
      muerte::discriminating-function-max-step2))

(defconstant +backtrace-gf-discriminatior-functions+
    '(muerte::discriminating-function-max
      muerte::discriminating-function-max%1op
      muerte::discriminating-function-max%1op%no-eqls
      muerte::discriminating-function-max%2op%no-eqls))

(defvar *backtrace-do-conflate* t)
(defvar *backtrace-length* 14)
(defvar *backtrace-max-args* 10)
(defvar *backtrace-stack-frame-barrier* nil)
(defvar *backtrace-do-fresh-lines* t)
(defvar *backtrace-print-length* 3)
(defvar *backtrace-print-level* 2)

(defun pointer-in-range (x)
  (with-inline-assembly (:returns :boolean-cf=1)
    (:compile-form (:result-mode :eax) x)
    ;; (:subl #x100000 :eax)
    (:cmpl #x1000000 :eax)))

    
(defun code-vector-offset (code-vector address)
  "If address points somewhere inside code-vector, return the offset."
  (check-type code-vector vector)
  (when (> (truncate address #.movitz::+movitz-fixnum-factor+)
	   (object-location code-vector))
    (let ((delta (- address 8 (* #.movitz::+movitz-fixnum-factor+
				 (object-location code-vector)))))
      (when (<= 0 delta (length code-vector))
	delta))))


#+ignore	  
(defun print-dynamic-context (&key terse symbol)
  (loop for dynamic-context = (current-dynamic-context)
      then (dynamic-context-uplink dynamic-context)
      while (stack-ref-p dynamic-context)
      do (let ((tag (dynamic-context-tag dynamic-context)))
	   (cond
	    ((eq tag (load-global-constant unbound-value))
	     (let ((name (stack-ref dynamic-context 0 0 :lisp)))
	       (when (or (not symbol) (eq symbol name))
		 (format t (if terse
			       "|  #x~X: n: ~S, v: ~Z.  |"
			     "~&#x~X: name: ~A~%        value: ~A")
			 dynamic-context name
			 (stack-ref dynamic-context 8 0 :lisp)))))
	    ((not symbol)
	     (format t (if terse
			   "|  #x~X: t: ~Z.  |"
			 "~&#x~X:  tag: ~S")
		     dynamic-context
		     tag))))
      finally (format t "~&Last uplink: #x~X~%" dynamic-context)
	      (return (values))))

(defun funobj-name-or-nil (x)
  (typecase x
    (compiled-function
     (funobj-name x))
    (t nil)))

(defparameter +call-site-numargs-maps+
    '((1 . (#xff #x56
		 #.(cl:ldb (cl:byte 8 0)
			   (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%1op))))
      (2 . (#xff #x56
	    #.(cl:ldb (cl:byte 8 0)
	       (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%2op))))
      (3 . (#xff #x56
	    #.(cl:ldb (cl:byte 8 0)
	       (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector%3op))))
      (0 . (#x33 #xc9 #xff #x56		; xorl :ecx :ecx
	    #.(cl:ldb (cl:byte 8 0)
	       (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector))))
      (0 . (#xb1 #x00 #xff #x56		; movb 0 :cl
	    #.(cl:ldb (cl:byte 8 0)
	       (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector))))
      (:ecx . (#xff #x56 #.(cl:ldb (cl:byte 8 0)
			    (bt:slot-offset 'movitz::movitz-funobj 'movitz::code-vector))))))

(defun stack-frame-numargs (stack-frame)
  "Try to determine how many arguments was presented to the stack-frame."
  (multiple-value-bind (call-site code)
      (stack-frame-call-site stack-frame)
    (when (and call-site code)
      (dolist (map +call-site-numargs-maps+
		(warn "no match at ~D for ~S."
		      call-site
		      (stack-frame-funobj (stack-frame-uplink stack-frame))))
	(when (not (mismatch code (cdr map)
			     :start1 (- call-site (length (cdr map)))
			     :end1 call-site))
	  (return
	    (cond
	     ((integerp (car map))
	      (car map))
	     ((eq :ecx (car map))
	      (cond
	       ((= #xb1 (aref code (- call-site 5)))
		;; Assume it's a (:movb x :cl) instruction
		(aref code (- call-site 4)))
	       (t ;; now we should search further for where ecx may be set..
		nil))))))))))

(defun signed8-index (s8)
  "Convert a 8-bit twos-complement signed integer bitpattern to
its natural value divided by 4."
  (assert (= 0 (ldb (byte 2 0) s8)))
  (values (if (> s8 #x7f)
	      (truncate (- s8 #x100) 4)
	    (truncate s8 4))))

(defun match-code-pattern (pattern code-vector start-ip &optional register)
  "Return success-p, result-register, result-position, ip.
It is quite possible to return success without having found the result-{register,position}."
  (do (result-register
       result-position
       (ip start-ip)
       (pattern pattern (cdr pattern)))
      ((endp pattern)
       (values t result-register result-position ip))
    (let ((p (car pattern)))
      (cond
       ((not (below ip (length code-vector)))
	;; mismatch because code-vector is shorter than pattern
	(return nil))
       ((listp p)
	(case (car p)
	  (:set-result
	   (setf result-register (second p)
		 result-position (third p)))
	  (:or
	   (dolist (sub-pattern (cdr p) (return nil))
	     (multiple-value-bind (success-p sub-result-register sub-result-position new-ip)
		 (match-code-pattern sub-pattern code-vector ip register)
	       (when success-p
		 (when sub-result-register
		   (setf result-register sub-result-register
			 result-position sub-result-position))
		 (setf ip new-ip)
		 (return)))))
	  (:* (let ((max-times (second p)) ; (:kleene-star <max-times> <sub-pattern>)
		    (sub-pattern (third p)))
		(dotimes (i max-times)
		  (multiple-value-bind (success-p sub-result-register sub-result-position new-ip)
		      (match-code-pattern sub-pattern code-vector ip register)
		    (unless success-p
		      (return))
		    (when sub-result-register
		      (setf result-register sub-result-register
			    result-position sub-result-position))
		    (setf ip new-ip)))))
	  (:constant
	   (when (eq (second p) register)
	     (setf result-register :constant
		   result-position (third p))))
	  (t (when (and register
			(eq (car p) register))
	       (setf result-register (second p)
		     result-position (or (third p) (aref code-vector ip))))
	     (incf ip))))
       (t (unless (= p (aref code-vector ip))
	    ;; mismatch
	    (return nil))
	  (incf ip))))))
	    
(defparameter *call-site-patterns*
    '(((6 22 . ((:* 4 ((:or (#x8b #x44 #x24 (:eax :esp)) ; #<asm MOVL [#x8+%ESP] => %EAX>
			    (#x8b #x5c #x24 (:ebx :esp)) ; #<asm MOVL [#x4+%ESP] => %EBX>
			    (#x8b #x45 (:eax :ebp)) ; (:movl (:ebp x) :eax)
			    (#x8b #x46 (:eax :esi)) ; (:movl (:esi x) :eax)
			    (#x8b #x5d (:ebx :ebp)) ; (:movl (:ebp x) :ebx)
			    (#x8b #x5e (:ebx :esi)) ; (:movl (:esi x) :ebx)
			    (#x33 #xdb (:constant :ebx 0))
			    )))
		(:or ((:or (#x8b #x56 (:edx :esi)) ;     (:movl (:esi x) :edx)
			   (#x8b #x54 #x37 (:edx :esi+edi))) ;#<asm MOVL [#x39+%EDI+%ESI] => %EDX>
		      #x8b #x72 #xfd)	;     (:movl (:edx -3) :esi)
		     (#x8b #x74 #x7e (:any-offset))) ; #<asm MOVL [#x28+%ESI+%EDI*2] => %ESI>
		(:* 1 ((:or (#xb1 (:cl-numargs))))) ; (:movb x :cl)
		(:* 1 ((:or (#x8b #x55 (:edx :ebp))
			    (#x8b #x56 (:edx :esi)))))
		#xff #x56 (:code-vector)))) ; (:call (:esi x))
      ;; APPLY 3 args
      ((20 20 . (#x8b #x5d (:ebx :ebp)	; #<asm MOVL [#x-c+%EBP] => %EBX>
		 #x8d #x4b #xff		; #<asm LEAL [#x-1+%EBX] %ECX>
		 #xf6 #xc1 #x07		; #<asm TESTB #x7 %CL>
		 #x75 #x15		; #<asm JNE %PC+#x15> ; branch to #:|sub-prg-label-#?317| at 258
		 #x89 #x43 #x03		; #<asm MOVL %EAX => [#x3+%EBX]>
		 #x8b #x45 (:eax :ebp)	; #<asm MOVL [#x-8+%EBP] => %EAX>
		 #xff #x56 (:code-vector)))) ; #<asm CALL [#x6+%ESI]>
      ;; Typical FUNCALL
      ((28 38 . ((:* 1 (#x8b #x45 (:eax :ebp))) ; #<asm MOVL [#x-18+%EBP] => %EAX>
		 (:* 1 (#x8b #x5d (:ebx :ebp))) ; #<asm MOVL [#x-14+%EBP] => %EBX>
		 (:or (#x8b #x55 (:edx :ebp)) ; #<asm MOVL [#x-1c+%EBP] => %EDX>
		      (#x5a)		; #<asm POPL %EDX>
		      ())
		 #x8d #x4a (:or (#x01) (#xf9)) ; #<asm LEAL [#x1+%EDX] %ECX>
		 (:or (#xf6 #xc1 #x07)	; #<asm TESTB #x7 %CL>
		      (#x80 #xe1 #x07))	; #<asm ANDB #x7 %CL>
		 #x75 (:any-label)	; #<asm JNE %PC+#x5> ; branch to #:|NOT-SYMBOL-#?909| at 284
		 #x8b #x72 #xfd		; #<asm MOVL [#x-3+%EDX] => %ESI>
		 #xeb (:any-label)	; #<asm JMP %PC+#xe> ; branch to #:|FUNOBJ-OK-#?911| at 298
					; #:|NOT-SYMBOL-#?909| 
		 (:or (#x41		; #<asm INCL %ECX>
		       #xf6 #xc1 #x07)	; #<asm TESTB #x7 %CL>
		      (#x80 #xf9 #x07)	; #<asm CMPB #x7 %CL>
		      (#x8d #x4a #xfa	; #<asm LEAL [#x-6+%EDX] %ECX>
			    #xf6 #xc1 #x07)) ; #<asm TESTB #x7 %CL>
		 #x75 (:any-label)	; #<asm JNE %PC+#xd> ; branch to #:|NOT-FUNOBJ-#?910| at 303
		 #x80 #x7a #xfe #x10	; #<asm CMPB #x10 [#x-2+%EDX]> ; #x4
		 #x75 (:any-label)	; #<asm JNE %PC+#x7> ; branch to #:|NOT-FUNOBJ-#?910| at 303
		 (:or (#x89 #xd6)	; #<asm MOVL %EDX => %ESI>
		      (#x8b #xf2))	; #<asm MOVL %EDX => %ESI>
					; #:|FUNOBJ-OK-#?911| 
		 #xff #x56 (:code-vector)))) ; #<asm CALL [#x6+%ESI]>
      ))

(defun call-site-find (stack-frame register)
  "Based on call-site's code, figure out where eax and ebx might be
located in the caller's stack-frame or funobj-constants."
  (macrolet ((success (result)
	       `(return-from call-site-find (values ,result t))))
    (multiple-value-bind (call-site-ip code-vector funobj)
	(stack-frame-call-site stack-frame)
      (when (eq funobj #'apply)
	(let ((apply-frame (stack-frame-uplink stack-frame)))
	  (when (eq 2 (stack-frame-numargs apply-frame))
	    (let ((applied (call-site-find apply-frame :ebx)))
	      ;; (warn "reg: ~S, applied: ~S" register applied)
	      (case register
		(:eax (success (first applied)))
		(:ebx (success (second applied))))))))
      (when (and call-site-ip code-vector)
	(loop for ((pattern-min-length pattern-max-length . pattern)) in *call-site-patterns*
	    do (loop for pattern-length from pattern-max-length downto pattern-min-length
		   do (multiple-value-bind (success-p result-register result-position match-ip)
			  (match-code-pattern pattern code-vector (- call-site-ip pattern-length) register)
			(when (and success-p (= call-site-ip match-ip))
			  (case result-register
			    (:constant
			     (success result-position))
			    (:ebp
			     (success (stack-frame-ref (stack-frame-uplink stack-frame)
						       (signed8-index result-position))))
			    (:esi
			     (when funobj
			       (success (funobj-constant-ref
					 funobj
					 (signed8-index (- result-position
							   #.(bt:slot-offset 'movitz::movitz-funobj
									     'movitz::constant0)))))))
			    (:esp
			     (success (stack-frame-ref stack-frame
						       (+ 2 (signed8-index result-position))))))))))))))

(defparameter *stack-frame-setup-patterns*
    '(((:* 1 (#x64 #x62 #x67 #xe7))	; #<asm (FS-OVERRIDE) BOUND [#x-19+%EDI] %ESP>
       (:* 1 (#x55 #x8b #xec #x56))	; pushl ebp, movl esp
       (:* 2 (#x80 #xf9 (cmpargs)
		   (:or (#x72 (label))
			(#x77 (label))
			(#x0f #x82 (label) (label) (label) (label))
			(#x0f #x87 (label) (label) (label) (label)))))
       (:* 1 (#x84 #xc9			; #<asm TESTB %CL %CL>
		   (:or (#x78 (label))	; #<asm JS %PC+#xed>
			(#x0f #x88 (label) (label) (label) (label)))
		   #x83 #xe2 #x7f))	; #<asm ANDL #x7f %ECX>
       (:* 1 (#x89 #x55 (:edx :ebp)))
       (:or (#x50 #x53 #x52 (:set-result (-4 -2 -3)))
	    (#x50 #x53 (:set-result (nil -2 -3)))
	    (#x50 #x52 (:set-result (-3 -2)))
	    (#x50 (:set-result (nil -2)))
	    (#x53 (:set-result (nil nil -2)))
	    (#x52 (:set-result (-2)))))))

(defun funobj-stack-frame-map (funobj &optional numargs)
  "Try funobj's stack-frame map, which is a list that says
what the stack-frame contains at that position. Some funobjs' map
depend on the number of arguments presented to it, so numargs can
be provided for those cases."
  (multiple-value-bind (code-vector start-ip)
      (let ((x (case numargs
		 (1 (funobj-code-vector%1op funobj))
		 (2 (funobj-code-vector%2op funobj))
		 (3 (funobj-code-vector%3op funobj))
		 (t (let ((setup-start (ldb (byte 5 0)
					    (funobj-debug-info funobj))))
		      (if (= setup-start 31) 0 setup-start))))))
	(cond
	 ((integerp x)
	  (values (funobj-code-vector funobj) x))
	 ((or (eq x (symbol-value 'muerte::trampoline-funcall%1op))
	      (eq x (symbol-value 'muerte::trampoline-funcall%2op))
	      (eq x (symbol-value 'muerte::trampoline-funcall%3op)))
	  (values (funobj-code-vector funobj) 0))
	 (t (values x 0))))
    (multiple-value-bind (successp map)
	(match-code-pattern (car *stack-frame-setup-patterns*) code-vector start-ip)
      (if successp
	  map
	#+ignore
	(multiple-value-bind (successp result-register result-position)
	    (match-code-pattern (car *stack-frame-setup-patterns*)
				code-vector start-ip :edx)
	  (when (and successp (eq :ebp result-register))
	    (list (signed8-index result-position))))))

    #+ignore
    (cdr (dolist (pattern-map *stack-frame-setup-patterns*)
	   (when (match-code-pattern (car pattern-map) code-vector setup-start)
	     (return pattern-map))))))


(defun print-stack-frame-arglist (stack-frame stack-frame-map
				  &key (numargs (stack-frame-numargs stack-frame))
				       (edx-p nil))
  (flet ((stack-frame-register-value (register stack-frame stack-map-pos)
	   (multiple-value-bind (val success-p)
	       (call-site-find stack-frame register)
	     (cond
	      (success-p
	       (values val t))
	      (stack-map-pos
	       (values (stack-frame-ref stack-frame stack-map-pos)
		       t))
	      (t (values nil nil)))))
	 (debug-write (x)
	   (if *backtrace-be-spartan-p*
	       (print-word x t)
	     (typecase x
	       (muerte::tag3
		(format t "{tag3 ~Z}" x))
	       ((and (not null) muerte::tag5)
		(format t "{tag5 ~Z}" x))
	       ((and (not character) (not restart) muerte::tag2)
		(format t "{tag2 ~Z}" x))
	       ((or null integer character)
		(write x))
	       (t (if (pointer-in-range x)
		      (write x)
		    (format t "{out-of-range ~Z}" x)))))))
    (if (not numargs)
	(write-string " ...")
      (prog () ;; (numargs (min numargs *backtrace-max-args*)))
	(multiple-value-bind (edx foundp)
	    (stack-frame-register-value :edx stack-frame (pop stack-frame-map))
	  (when edx-p
	    (write-string " {edx: ")
	    (if foundp
		(debug-write edx)
	      (write-string "unknown"))
	    (write-string "}")))
	(when (zerop numargs)
	  (return))
	(write-char #\space)
	(if (first stack-frame-map)
	    (debug-write (stack-frame-ref stack-frame (first stack-frame-map)))
	  (multiple-value-bind (eax eax-p)
	      (call-site-find stack-frame :eax)
	    (if eax-p
		(debug-write eax)
	      (write-string "{eax unknown}"))))
	(when (> 2 numargs)
	  (return))
	(write-char #\space)
	(if (second stack-frame-map)
	    (debug-write (stack-frame-ref stack-frame (second stack-frame-map)))
	  (multiple-value-bind (ebx ebx-p)
	      (call-site-find stack-frame :ebx)
	    (if ebx-p
		(debug-write ebx)
	      (write-string "{ebx unknown}"))))
	(loop for i downfrom (1- numargs) to 2
	    as printed-args upfrom 2
	    do (when (> printed-args *backtrace-max-args*)
		 (write-string " ...")
		 (return))
	       (write-char #\space)
	       (debug-write (stack-frame-ref stack-frame i))))))
  (values))

(defun backtrace (&key ((:frame initial-stack-frame)
			(or *debugger-invoked-stack-frame*
			    (current-stack-frame)))
		       ((:spartan *backtrace-be-spartan-p*))
		       (conflate *backtrace-do-conflate*)
		       (length *backtrace-length*)
		       print-frames)
  (let ((*standard-output* *debug-io*)
	(*print-length* *backtrace-print-length*)
	(*print-level* *backtrace-print-level*))
    (loop with conflate-count = 0 with count = 0
	for stack-frame = initial-stack-frame then (stack-frame-uplink stack-frame)
	as funobj = (stack-frame-funobj stack-frame t)
	do (flet ((print-leadin (count conflate-count)
		    (when *backtrace-do-fresh-lines*
		      (fresh-line))
		    (cond
		     ((plusp count)
		      (write-string " <")
		      (if (plusp conflate-count)
			  (write conflate-count :base 10 :radix nil)
			(write-string "="))
		      (write-char #\space))
		     (t (format t "~& |= ")))
		    (when print-frames
		       (format t "#x~X " stack-frame))))
	     (typecase funobj
	       (integer
		(let* ((int-frame funobj)
		       (funobj (int-frame-ref int-frame :esi :lisp)))
		  (if (and conflate
			   ;; When the interrupted function has a stack-frame, conflate it.
			   (typep funobj 'function)
			   (= 1 (ldb (byte 1 5) (funobj-debug-info funobj))))
		      (incf conflate-count)
		    (progn
		      (incf count)
		      (print-leadin count conflate-count)
		      (setf conflate-count 0)
		      (let ((exception (int-frame-ref int-frame :exception :unsigned-byte32))
			    (eip (int-frame-ref int-frame :eip :unsigned-byte32)))
			(typecase funobj
			  (function
			   (let ((delta (code-vector-offset (funobj-code-vector funobj) eip)))
			     (if delta
				 (format t "{Interrupt ~D in ~W at offset ~D. [#x~X]}"
					 exception (funobj-name funobj) delta int-frame)
			       (format t "{Interrupt ~D in ~W at EIP=#x~X. [#x~X]}"
				       exception (funobj-name funobj) eip int-frame))))
			  (t (format t "{Interrupt ~D with ESI=#x~Z and EIP=#x~X. [#x~X]}"
				     exception funobj eip int-frame))))))))
	       (function
		(let ((name (funobj-name funobj)))
		  (cond
		   ((and conflate (member name *backtrace-conflate-names* :test #'equal))
		    (incf conflate-count))
		   (t (incf count)
		      (when (and *backtrace-stack-frame-barrier*
				 (<= *backtrace-stack-frame-barrier* stack-frame))
			(write-string " --|")
			(return))
		      (unless (or (not (integerp length))
				  (< count length))
			(write-string " ...")
			(return))
		      (print-leadin count conflate-count)
		      (setf conflate-count 0)
		      (write-char #\()
		      (let* ((numargs (stack-frame-numargs stack-frame))
			     (map (and funobj (funobj-stack-frame-map funobj numargs))))
			(cond
			 ((and (car map) (eq name 'unbound-function))
			  (let ((real-name (stack-frame-ref stack-frame (car map))))
			    (format t "{unbound ~S}" real-name)))
			 ((and (car map)
			       (member name +backtrace-gf-discriminatior-functions+))
			  (let ((gf (stack-frame-ref stack-frame (car map))))
			    (cond
			     ((typep gf 'muerte::standard-gf-instance)
			      (format t "{gf ~S}" (funobj-name gf)))
			     (t (write-string "[not a gf??]")))
			    (print-stack-frame-arglist stack-frame map :numargs numargs)))
			 (t (write name)
			    (print-stack-frame-arglist stack-frame map
						       :numargs numargs
						       :edx-p (eq 'muerte::&edx
								  (car (funobj-lambda-list funobj)))))))
		      (write-char #\))
		      (when (and (symbolp name)
				 (string= name 'toplevel-function))
			(write-char #\.)
			(return))))))
	       (t (format t "~&?: ~Z" funobj))))))
  (values))

(defun fixnum-word (fixnum)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) fixnum)
    (:shrl #.movitz::+movitz-fixnum-shift+ :eax)))
