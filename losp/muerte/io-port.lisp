;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      io-port.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Mar 21 22:14:08 2001
;;;;                
;;;; $Id: io-port.lisp,v 1.6 2004/02/01 22:16:26 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/setf)
(require :muerte/loop)
(require :muerte/equalp)
(provide :muerte/io-port)

(in-package muerte)

(define-compiler-macro io-port (&whole form port type &environment env)
  (if (not (movitz:movitz-constantp type env))
      form
    (ecase (movitz::eval-form type env)
      (:unsigned-byte8
       `(with-inline-assembly (:returns :untagged-fixnum-eax)
	  (:compile-form (:result-mode :edx) ,port)
	  (:andl ,(ash #xffff movitz::+movitz-fixnum-shift+) :edx)
	  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	  (:xorl :eax :eax)
	  (:inb :dx :al)))
      (:unsigned-byte16
       `(with-inline-assembly (:returns :untagged-fixnum-eax)
	  (:compile-form (:result-mode :edx) ,port)
	  (:andl ,(ash #xffff movitz::+movitz-fixnum-shift+) :edx)
	  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	  (:xorl :eax :eax)
	  (:inw :dx :ax)))
      (:character
       `(with-inline-assembly (:returns :eax)
	  (:compile-form (:result-mode :edx) ,port)
	  (:andl ,(ash #xffff movitz::+movitz-fixnum-shift+) :edx)
	  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	  (:xorl :eax :eax)
	  (:inb :dx :al)
	  (:shll 8 :eax)
	  (:movb ,(movitz::tag :character) :al))))))

(defun io-port (port type)
  (ecase type
    (:unsigned-byte8
     (io-port port :unsigned-byte8))
    (:unsigned-byte16
     (io-port port :unsigned-byte16))
    (:character
     (io-port port :character))))

(define-compiler-macro (setf io-port) (&whole form value port type)
  (let ((value-code (if (not (movitz:movitz-constantp value))
			`((:compile-form (:result-mode :untagged-fixnum-eax) ,value))
		      (let ((port-value (movitz::eval-form value)))
			(check-type port-value (unsigned-byte 16))
			(movitz::make-immediate-move port-value :eax)))))
    ;; value-code will put VALUE in eax.
    (cond
     ((and (movitz:movitz-constantp type)
	   (movitz:movitz-constantp port))
      (let ((the-port (movitz::eval-form port))
	    (the-type (movitz::eval-form type)))
	(etypecase the-port
	  ((unsigned-byte 8)		; short form of outb can be used
	   (ecase the-type
	     (:unsigned-byte8
	      `(with-inline-assembly (:returns :untagged-fixnum-eax)
		 ,@value-code
		 (:outb :al ,the-port)))
	     (:unsigned-byte16
	      `(with-inline-assembly (:returns :untagged-fixnum-eax)
		 ,@value-code
		 (:outw :ax ,the-port)))))
	  ((unsigned-byte 16)		; indirect (by DX) form of outb must be used
	   (ecase the-type
	     (:unsigned-byte8
	      `(with-inline-assembly (:returns :untagged-fixnum-eax)
		 ,@value-code
		 ,@(movitz::make-immediate-move the-port :edx)
		 (:outb :al :dx)))
	     (:unsigned-byte16
	      `(with-inline-assembly (:returns :untagged-fixnum-eax)
		 ,@value-code
		 ,@(movitz::make-immediate-move the-port :edx)
		 (:outw :ax :dx))))))))
     ((movitz:movitz-constantp type)
      (ecase (movitz::eval-form type)
	(:unsigned-byte8
	 `(with-inline-assembly (:returns :untagged-fixnum-eax)
	    (:compile-form (:result-mode :push) ,port)
	    ,@value-code
	    (:popl :edx)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	    (:outb :al :dx)))
	(:unsigned-byte16
	 `(with-inline-assembly (:returns :untagged-fixnum-eax)
	    (:compile-form (:result-mode :push) ,port)
	    ,@value-code
	    (:popl :edx)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	    (:outw :ax :dx)))
	(:character
	 `(with-inline-assembly (:returns :eax)
	    (:compile-form (:result-mode :push) ,port)
	    (:compile-form (:result-mode :eax) ,value)
	    (:cmpb #.(movitz::tag :character) :al)
	    (:jne '(:sub-program (not-a-character) (:int 60)))
	    (:popl :edx)
	    (:shrl 8 :eax)
	    (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	    (:outb :al :dx)
	    (:shll 8 :eax)
	    (:movb 2 :al)))))
     (t form))))

(defun (setf io-port) (value port type)
  (ecase type
    (:unsigned-byte8
     (setf (io-port port :unsigned-byte8) value))
    (:unsigned-byte16
     (setf (io-port port :unsigned-byte8) value))
    (:character
     (setf (io-port port :character) value))))

;;; The io-registerX functions are just syntactic sugar that matches the
;;; most frequent use of io-port.

(define-compiler-macro io-register8 (io-base io-offset)
  `(io-port (+ ,io-base ,io-offset) :unsigned-byte8))

(defun io-register8 (io-base io-offset)
  "Read from single-octet IO-port io-base + io-offset."
  (io-register8 io-base io-offset))

(define-compiler-macro (setf io-register8) (value io-base io-offset)
  `(setf (io-port (+ ,io-base ,io-offset) :unsigned-byte8) ,value))

(defun (setf io-register8) (value io-base io-offset)
  "Write to single-octet IO-port io-base + io-offset."
  (setf (io-register8 io-base io-offset) value))

(defmacro with-io-register-syntax ((name io-base-form) &body body)
  "Syntax for easy access to IO registers. <name> is installed as a local macro
that reads from <io-base-form> plus some offset."
  (let ((io-var (gensym "io-base-")))
    `(let ((,io-var ,io-base-form))
       ;; (check-type ,io-var (unsigned-byte 16))
       (symbol-macrolet ((,name ,io-var))
	 (macrolet ((,name (offset) `(io-register8 ,',io-var ,offset)))
	   ,@body)))))

(define-compiler-macro io-register8x2 (io-base offset-hi offset-lo)
  `(let ((io-base ,io-base))
     (dpb (io-register8 io-base ,offset-hi)
	  (byte 8 8)
	  (io-register8 io-base ,offset-lo))))

(defun io-register8x2 (io-base offset-hi offset-lo)
  (io-register8x2 io-base offset-hi offset-lo))

(define-compiler-macro (setf io-register8x2) (&environment env value io-base offset-hi offset-lo)
  `(let ((value ,value))
     (setf (io-register8 ,io-base ,offset-hi) (ldb (byte 8 8) value)
	   (io-register8 ,io-base ,offset-lo) (ldb (byte 8 0) value))
     value))

(defun (setf io-register8x2) (value io-base offset-hi offset-lo)
  (setf (io-register8x2 io-base offset-hi offset-lo) value))

;;;

(defun io-delay (&optional (x 1000))
  (dotimes (i x)
    (with-inline-assembly (:returns :nothing) (:nop))))

(define-compiler-macro %io-port-read-succession (&whole form port object offset start end byte-size
						 &environment env)
  (if (not (movitz:movitz-constantp byte-size env))
      form
    (let ((byte-size (movitz:movitz-eval byte-size env)))
      (cond
       ((and (movitz:movitz-constantp offset env)
	     (movitz:movitz-constantp start env)
	     (movitz:movitz-constantp end env))
	(let* ((offset (movitz:movitz-eval offset env))
	       (start (movitz:movitz-eval start env))
	       (end (movitz:movitz-eval end env))
	       (count (- end start)))
	  (check-type count (integer 0 #x10000))
	  (case byte-size
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     (if (<= 1 count 20)
		 `(with-inline-assembly-case ()
		    (do-case (t :eax)
		      (:compile-two-forms (:edx :ebx) ,port ,object)
		      (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      ,@(loop for i from start below end
			    appending
			      `((:inl :dx :eax)
				(:movl :eax (:ebx ,(+ offset (* 4 i))))))
		      (:movl :ebx :eax)))
	       `(with-inline-assembly-case ()
		  (do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		    (:compile-two-forms (:edx :ebx) ,port ,object)
		    (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:pushl ,(cl:* movitz::+movitz-fixnum-factor+ end)) ; keep end in (:esp)
		    (:movl ,(cl:* movitz::+movitz-fixnum-factor+ start) :ecx)
		   io-read-loop
		    (:cmpl :ecx (:esp))
		    (:jbe 'end-io-read-loop)
		    (:addl 4 :ecx)
		    (:inl :dx :eax)
		    (:movl :eax (:ebx ,(+ offset -4) :ecx))
		    (:jmp 'io-read-loop)
		    (:popl :eax)	; increment :esp, and put a lispval in :eax.
		   end-io-read-loop))))
	    (:16-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     (if (and t (<= 1 count 20))
		 `(with-inline-assembly-case ()
		    (do-case (t :ebx)
		      (:compile-two-forms (:edx :ebx) ,port ,object)
		      (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      (:xorl :eax :eax)
		      ,@(loop for i from start below end
			    appending
			      `((:inw :dx :ax)
				(:movw :ax (:ebx ,(+ offset (* 2 i))))))))
	       `(with-inline-assembly-case ()
		  (do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		    (:compile-two-forms (:edx :ebx) ,port ,object)
		    (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    ;; (:pushl ,(cl:* movitz::+movitz-fixnum-factor+ end)) ; keep end in (:esp)
		    (:movl ,(cl:* 1 start) :ecx)
		    (:xorl :eax :eax)
		   io-read-loop
		    (:cmpl ,end :ecx)
		    (:ja 'end-io-read-loop)
		    (:addl 1 :ecx)
		    (:inw :dx :ax)
		    (:movw :ax (:ebx ,(+ offset -2) (:ecx 2)))
		    (:jmp 'io-read-loop)
		   end-io-read-loop))))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       ((and (movitz:movitz-constantp offset env))
	(let ((offset (movitz:movitz-eval offset env)))
	  (case byte-size
	    (:8-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :eax)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :ecx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:inb :dx :al)
		  (:addl 1 :ecx)
		  (:movb :al (:ebx ,(+ offset -1) (:ecx 1)))
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (:16-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :eax)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :ecx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:inw :dx :ax)
		  (:addl 1 :ecx)
		  (:movw :ax (:ebx ,(+ offset -2) (:ecx 2)))
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:inl :dx :eax)
		  (:addl 4 :ecx)
		  (:movl :eax (:ebx ,(+ offset -4) :ecx))
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       (t (error "Variable offset not implemented."))))))

(defun %io-port-read-succession (port object offset start end byte-size)
  (unless (= 2 offset)
    (error "Only offset 2 implemented."))
  (case byte-size
    (:8-bit
     (%io-port-read-succession port object 2 start end :8-bit))
    (:16-bit
     (%io-port-read-succession port object 2 start end :16-bit))
    (:32-bit
     (%io-port-read-succession port object 2 start end :32-bit))
    (t (error "Unknown byte-size ~S." byte-size))))

(define-compiler-macro %io-port-write-succession (&whole form port object offset start end byte-size
						  &environment env)
  (if (not (movitz:movitz-constantp byte-size env))
      form
    (let ((byte-size (movitz:movitz-eval byte-size env)))
      (cond
       ((and (movitz:movitz-constantp offset env)
	     (movitz:movitz-constantp start env)
	     (movitz:movitz-constantp end env))
	(let* ((offset (movitz:movitz-eval offset env))
	       (start (movitz:movitz-eval start env))
	       (end (movitz:movitz-eval end env))
	       (count (- end start)))
	  (check-type count (integer 0 #x10000))
	  (case byte-size
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     (if (<= 1 count 20)
		 `(with-inline-assembly-case ()
		    (do-case (t :eax)
		      (:compile-two-forms (:edx :ebx) ,port ,object)
		      (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      ,@(loop for i from start below end
			    appending
			      `((:movl (:ebx ,(+ offset (* 4 i))) :eax)
				(:outl :eax :dx)))
		      (:movl :ebx :eax)))
	       `(with-inline-assembly-case ()
		  (do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		    (:compile-two-forms (:edx :ebx) ,port ,object)
		    (:andl ,(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:pushl ,(cl:* movitz::+movitz-fixnum-factor+ end)) ; keep end in (:esp)
		    (:movl ,(cl:* movitz::+movitz-fixnum-factor+ start) :ecx)
		   io-read-loop
		    (:cmpl :ecx (:esp))
		    (:jbe 'end-io-read-loop)
		    (:addl 4 :ecx)
		    (:movl (:ebx ,(+ offset -4) :ecx) :eax)
		    (:outl :eax :dx)
		    (:jmp 'io-read-loop)
		    (:popl :eax)	; increment :esp, and put a lispval in :eax.
		   end-io-read-loop))))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       ((and (movitz:movitz-constantp offset env))
	(let ((offset (movitz:movitz-eval offset env)))
	  (case byte-size
	    (:8-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :eax)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :ecx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:addl 1 :ecx)
		  (:movb (:ebx ,(+ offset -1) (:ecx 1)) :al)
		  (:outb :al :dx)
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (:16-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :eax)
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :ecx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :eax)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:addl 1 :ecx)
		  (:movw (:ebx ,(+ offset -2) (:ecx 2)) :ax)
		  (:outw :ax :dx)
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(with-inline-assembly-case ()
		(do-case (t :ebx :labels (io-read-loop end-io-read-loop not-fixnum))
		  (:compile-form (:result-mode :push) ,port)
		  (:compile-form (:result-mode :push) ,object)
		  (:compile-two-forms (:ecx :eax) ,start ,end)
		  (:popl :ebx)		; object
		  (:popl :edx)		; port
		  (:andl #.(cl:* #xffff movitz::+movitz-fixnum-factor+) :edx)
		  (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
		  (:pushl :eax)		; keep end in (:esp)
		 io-read-loop
		  (:cmpl :ecx (:esp))
		  (:jbe 'end-io-read-loop)
		  (:addl 4 :ecx)
		  (:movl (:ebx ,(+ offset -4) :ecx) :eax)
		  (:outl :eax :dx)
		  (:jmp 'io-read-loop)
		  (:popl :eax)		; increment :esp, and put a lispval in :eax.
		 end-io-read-loop)))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       (t (error "Variable offset not implemented."))))))

(defun %io-port-write-succession (port object offset start end byte-size)
  (unless (= 2 offset)
    (error "Only offset 2 implemented."))
  (case byte-size
    (:8-bit
     (%io-port-write-succession port object 2 start end :8-bit))
    (:16-bit
     (%io-port-write-succession port object 2 start end :16-bit))
    (:32-bit
     (%io-port-write-succession port object 2 start end :32-bit))
    (t (error "Unknown byte-size ~S." byte-size))))


(defun io-port-read-sequence (sequence port type transfer-unit &key (start 0) end)
  (etypecase sequence
    ((or string muerte::vector-u8)
     (unless end (setf end (length sequence)))
     (let ((size (- end start)))
       (assert (<= 0 start end (length sequence)) (start end)
	 "io-port-read-sequence out of bounds: ~D - ~D into ~D / ~D" start end (length sequence) (array-dimension sequence 0))
       (ecase type
	 (:unsigned-byte8
	  (ecase transfer-unit
	    (:8-bits
	     ;; one-to-one
	     (with-inline-assembly (:returns :nothing)
	       (:compile-form (:result-mode :edx) port)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	       (:compile-form (:result-mode :ecx) start)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:addl #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data) :ebx)
	       (:addl :ecx :ebx)
	       (:compile-form (:result-mode :ecx) size)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:xorl :eax :eax)
	       (:jecxz 'read8-done)
	      read8-loop
	       (:inb :dx :al)
	       (:movb :al (:ebx))
	       (:incl :ebx)
	       (:decl :ecx)
	       (:jnz 'read8-loop)
	      read8-done))
	    (:16-bits
	     ;; each 16-bits IOW maps to two u2
	     (with-inline-assembly (:returns :nothing)
	       (:compile-form (:result-mode :edx) port)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	       (:compile-form (:result-mode :ecx) start)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:addl #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data) :ebx)
	       (:addl :ecx :ebx)
	       (:compile-form (:result-mode :ecx) size)
	       (:shrl #.(cl:1+ movitz::+movitz-fixnum-shift+) :ecx)
	       (:xorl :eax :eax)
	       (:jecxz 'read16-done)
	      read16-loop
	       (:inw :dx :ax)
	       (:movw :ax (:ebx))
	       (:addl 2 :ebx)
	       (:decl :ecx)
	       (:jnz 'read16-loop)
	      read16-done))))
	 (:unsigned-byte16
	  (ecase transfer-unit
	    (:16-bits
	     ;; 16-bit io-port squeezed into 8 bits..
	     (with-inline-assembly (:returns :nothing)
	       (:compile-form (:result-mode :edx) port)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:addl #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data) :ebx)
	       (:compile-form (:result-mode :ecx) start)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:addl :ecx :ebx)
	       (:compile-form (:result-mode :ecx) size)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:xorl :eax :eax)
	       (:jecxz 'read16-8-done)
	      read16-8-loop
	       (:inw :dx :ax)
	       (:movb :al (:ebx))
	       (:incl :ebx)
	       (:decl :ecx)
	       (:jnz 'read16-8-loop)
	      read16-8-done)))))))
    (vector
     (unless end (setf end (length sequence)))
     (let ((size (- end start)))
       (assert (<= 0 start end (length sequence)) (start end)
	 "io-port-read-sequence out of bounds.")
       (ecase type
	 (:unsigned-byte8
	  (ecase transfer-unit
	    (:8-bits
	     (dotimes (i size)
	       (setf (aref sequence (+ start i))
		 (io-port port :unsigned-byte8))))
	    (:16-bits
	     (dotimes (i (truncate size 2))
	       (let ((byte (io-port port :unsigned-byte16)))
		 (setf (aref sequence (+ start (* 2 i))) (ldb (byte 8 0) byte) ; little endian..
		       (aref sequence (+ start (* 2 i) 1)) (ldb (byte 8 8) byte))))))))))
    (list
     (when sequence
       (let ((start-cons (nthcdr start sequence)))
	 (assert start-cons (sequence)
	   "Sequence start ~D out of range: ~S" start sequence)
	 (ecase type
	   (:unsigned-byte8
	    (ecase transfer-unit
	      (:8-bits
	       (if (not end)
		   (loop for p on start-cons
		       do (setf (car p) (io-port port :unsigned-byte8)))
		 (loop for i upfrom start below end as p on (nthcdr start sequence)
		     do (setf (car p) (io-port port :unsigned-byte8))
		     finally (assert (= i end) (end)
			       "Sequence end ~D out of range: ~S" end sequence))))
	      (:16-bits
	       (if (not end)
		   (loop for p on start-cons by #'cddr
		       do (let ((byte (io-port port :unsigned-byte16)))
			    (setf (car p) (ldb (byte 8 0) byte) ; little endian..
				  (cadr p) (ldb (byte 8 8) byte))))
		 (loop for i upfrom start below end by 2 as p on (nthcdr start sequence) by #'cddr
		     do (let ((byte (io-port port :unsigned-byte16)))
			  (setf (car p) (ldb (byte 8 0) byte) ; little endian..
				(cadr p) (ldb (byte 8 8) byte)))
		     finally (assert (= i end) (end)
			       "Sequence end ~D out of range: ~S" end sequence)))))))))))
  sequence)

(defun io-port-write-sequence (sequence port type transfer-unit &key (start 0) end)
  (etypecase sequence
    ((or string muerte::vector-u8)
     (unless end (setf end (length sequence)))
     (let ((size (- end start)))
       (assert (<= 0 start end (length sequence)) (start end)
	 "io-port-write-sequence out of bounds.")
       (ecase type
	 ((:unsigned-byte8)
	  (ecase (or transfer-unit :8-bits)
	    (:8-bits
	     ;; one-to-one
	     (with-inline-assembly (:returns :nothing)
	       (:compile-form (:result-mode :edx) port)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:compile-form (:result-mode :ecx) start)
	       (:addl #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data) :ebx)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:addl :ecx :ebx)
	       (:compile-form (:result-mode :ecx) size)
	       (:xorl :eax :eax)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:align :code :loop)
	       write8-loop
	       (:movb (:ebx) :al)
	       (:outb :al :dx)
	       (:incl :ebx)
	       (:decl :ecx)
	       (:jnz 'write8-loop)))
	    (:16-bits
	     ;; each 16-bits IOW maps to two u2
	     (with-inline-assembly (:returns :nothing)
	       (:compile-form (:result-mode :edx) port)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :edx)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:compile-form (:result-mode :ecx) start)
	       (:addl #.(bt:slot-offset 'movitz::movitz-vector 'movitz::data) :ebx)
	       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
	       (:addl :ecx :ebx)
	       (:compile-form (:result-mode :ecx) size)
	       (:xorl :eax :eax)
	       (:shrl #.(cl:1+ movitz::+movitz-fixnum-shift+) :ecx)
	       (:align :code :loop)
	       write16-loop
	       (:movw (:ebx) :ax)
	       (:outw :ax :dx)
	       (:addl 2 :ebx)
	       (:decl :ecx)
	       (:jnz 'write16-loop))))))))
    (vector
     (unless end (setf end (length sequence)))
     (let ((size (- end start)))
       (ecase type
	 (:character
	  (ecase (or transfer-unit :8-bits)
	    (:8-bits
	     (dotimes (i size)
	       (setf (io-port port :character)
		 (char sequence (+ start i)))))))
	 (:unsigned-byte8
	  (ecase (or transfer-unit :8-bits)
	    (:8-bits
	     ;; one-to-one 8 bits
	     (dotimes (i size)
	       (setf (io-port port :unsigned-byte8)
		 (aref sequence (+ start i)))))
	    (:16-bits
	     ;; two by two (8-bit) array elements into each 16-bit io-port
	     (dotimes (i (truncate size 2))
	       (setf (io-port port :unsigned-byte16)
		 (dpb (aref sequence (+ start (* 2 i) 1)) ; little endian..
		      (byte 8 8)
		      (aref sequence (+ start (* 2 i)))))))
	    )))))))

