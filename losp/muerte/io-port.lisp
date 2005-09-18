;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      io-port.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Mar 21 22:14:08 2001
;;;;                
;;;; $Id: io-port.lisp,v 1.20 2005/09/18 16:21:25 ffjeld Exp $
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
    (ecase (movitz:movitz-eval type env)
      (:unsigned-byte8
       `(with-inline-assembly-case (:type (unsigned-byte 8))
	  (do-case (:untagged-fixnum-ecx :untagged-fixnum-ecx)
	    (:compile-form (:result-mode :edx) ,port)
	    (:std)			; only EBX is now GC root
	    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	    (:xorl :eax :eax)
	    (:inb :dx :al)
	    (:movl :eax :ecx)
	    (:movl :edi :eax)
	    (:movl :edi :edx)
	    (:cld))
	  (do-case (t :eax)
	    (:compile-form (:result-mode :edx) ,port)
	    (:std)			; only EBX is now GC root
	    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	    (:xorl :eax :eax)
	    (:inb :dx :al)
	    (:shll ,movitz:+movitz-fixnum-shift+ :eax)
	    (:movl :edi :edx)
	    (:cld))))
      (:unsigned-byte16
       `(with-inline-assembly-case (:type (unsigned-byte 16))
	  (do-case (:untagged-fixnum-ecx :untagged-fixnum-ecx)
	    (:compile-form (:result-mode :edx) ,port)
	    (:std)
	    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	    (:xorl :eax :eax)
	    (:inw :dx :ax)
	    (:movl :eax :ecx)
	    (:movl :edi :eax)
	    (:movl :edi :edx)
	    (:cld))
	  (do-case (t :eax)
	    (:compile-form (:result-mode :edx) ,port)
	    (:std)
	    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	    (:xorl :eax :eax)
	    (:inw :dx :ax)
	    (:shll ,movitz:+movitz-fixnum-shift+ :eax)
	    (:movl :edi :edx)
	    (:cld))))
      (:unsigned-byte32
       `(with-inline-assembly (:returns :untagged-fixnum-ecx
					:type (unsigned-byte 32))
	  (:compile-form (:result-mode :edx) ,port)
	  (:std)
	  (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	  (:inl :dx :eax)
	  (:movl :eax :ecx)
	  (:movl :edi :eax)
	  (:movl :edi :edx)
	  (:cld)))
      (:location
       `(with-inline-assembly (:returns :eax :type fixnum)
	  (:compile-form (:result-mode :edx) ,port)
	  (:std)
	  (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	  (:inl :dx :eax)
	  (:andl -8 :eax)
	  (:movl :edi :edx)
	  (:cld)))
      (:character
       `(with-inline-assembly (:returns :eax)
	  (:compile-form (:result-mode :edx) ,port)
	  (:std)
	  (:shrl ,movitz:+movitz-fixnum-shift+ :edx)
	  (:xorl :eax :eax)
	  (:inb :dx :al)
	  (:shll 8 :eax)
	  (:movb ,(movitz::tag :character) :al)
	  (:movl :edi :edx)
	  (:cld))))))

(defun io-port (port type)
  (ecase type
    (:unsigned-byte8
     (io-port port :unsigned-byte8))
    (:unsigned-byte16
     (io-port port :unsigned-byte16))
    (:unsigned-byte32
     (io-port port :unsigned-byte32))
    (:location
     (io-port port :location))
    (:character
     (io-port port :character))))

(define-compiler-macro (setf io-port) (&whole form value port type &environment env)
  (let ((value-var (gensym "(setf io-port)-value-"))
	(port-var (gensym "(setf io-port)-port-")))
    (cond
     ((and (movitz:movitz-constantp type env)
	   (movitz:movitz-constantp port env))
      (let ((the-port (movitz:movitz-eval port env))
	    (the-type (movitz:movitz-eval type env)))
	(etypecase the-port
	  ((unsigned-byte 8)		; short form of outb can be used
	   (ecase the-type
	     (:unsigned-byte8
	      `(let ((,value-var ,value))
		 (with-inline-assembly (:returns :nothing)
		   (:load-lexical (:lexical-binding ,value-var) :eax)
		   (:std)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :eax)
		   (:outb :al ,the-port)
		   (:movl :edi :eax)
		   (:movl :edi :edx)
		   (:cld))
		 ,value-var))
	     (:unsigned-byte16
	      `(let ((,value-var ,value))
		 (with-inline-assembly (:returns :nothing)
		   (:load-lexical (:lexical-binding ,value-var) :eax)
		   (:std)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :eax)
		   (:outw :ax ,the-port)
		   (:movl :edi :eax)
		   (:movl :edi :edx)
		   (:cld))
		 ,value-var))))
	  ((unsigned-byte 16)		; indirect (by DX) form of outb must be used
	   (ecase the-type
	     (:unsigned-byte8
	      `(let ((,value-var ,value))
		 (with-inline-assembly (:returns :nothing)
		   (:load-lexical (:lexical-binding ,value-var) :eax)
		   (:std)
		   ,@(movitz::make-immediate-move the-port :edx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :eax)
		   (:outb :al :dx)
		   ,@(unless (= 0 (mod the-port 4))
		       `((:movl :edi :edx)))
		   (:movl :edi :eax)
		   (:cld))
		 ,value-var))
	     (:unsigned-byte16
	      `(let ((,value-var ,value))
		 (with-inline-assembly (:returns :nothing)
		   (:load-lexical (:lexical-binding ,value-var) :eax)
		   (:std)
		   ,@(movitz::make-immediate-move the-port :edx)
		   (:shrl ,movitz:+movitz-fixnum-shift+ :eax)
		   (:outw :ax :dx)
		   ,@(unless (= 0 (mod the-port 4))
		       `((:movl :edi :edx)))
		   (:movl :edi :eax)
		   (:cld)))))))))
     ((and (movitz:movitz-constantp type env)
	   (movitz:movitz-constantp value env))
      (let ((value (movitz:movitz-eval value env)))
	(ecase (movitz:movitz-eval type env)
	  (:unsigned-byte8
	   (check-type value (unsigned-byte 8))
	   `(let ((,port-var ,port))
	      (with-inline-assembly (:returns :nothing)
		(:load-lexical (:lexical-binding ,port-var) :untagged-fixnum-ecx)
		(:std)
		(:movl :ecx :edx)
		(:movb ,value :al)
		(:outb :al :dx)
		(:movl :edi :edx)
		(:movl :edi :eax)
		(:cld))
	      ,value))
	  (:unsigned-byte16
	   (check-type value (unsigned-byte 16))
	   `(let ((,port-var ,port))
	      (with-inline-assembly (:returns :nothing)
		(:load-lexical (:lexical-binding ,port-var) :untagged-fixnum-ecx)
		(:std)
		(:movl :ecx :edx)
		(:movl ,value :eax)
		(:outw :ax :dx)
		(:movl :edi :edx)
		(:movl :edi :eax)
		(:cld))
	      ,value))
	  (:unsigned-byte32
	   `(let ((,port-var ,port))
	      (with-inline-assembly (:returns :nothing)
		(:load-lexical (:lexical-binding ,port-var) :untagged-fixnum-ecx)
		(:std)
		(:movl :ecx :edx)
		(:movl ,value :eax)
		(:outl :eax :dx)
		(:movl :edi :edx)
		(:movl :edi :eax)
		(:cld))
	      ,value))
	  (:character
	   `(let ((,port-var ,port))
	      (check-type value character)
	      (with-inline-assembly (:returns :nothing)
		(:load-lexical (:lexical-binding ,port-var) :untagged-fixnum-ecx)
		(:std)
		(:movl :ecx :edx)
		(:movb ,(char-code value) :al)
		(:outb :al :dx)
		(:movl :edi :edx)
		(:movl :edi :eax)
		(:cld))
	      ,value)))))
     ((movitz:movitz-constantp type env)
      (ecase (movitz:movitz-eval type env)
	(:unsigned-byte8
	 `(let ((,value-var ,value)
		(,port-var ,port))
	    (with-inline-assembly (:returns :nothing)
	      (:load-lexical (:lexical-binding ,port-var) :edx)
	      (:load-lexical (:lexical-binding ,value-var) :eax)
	      (:std)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :eax)
	      (:outb :al :dx)
	      (:movl :edi :edx)
	      (:movl :edi :eax)
	      (:cld))
	    ,value-var))
	(:unsigned-byte16
	 `(let ((,value-var ,value)
		(,port-var ,port))
	    (with-inline-assembly (:returns :nothing)
	      (:load-lexical (:lexical-binding ,port-var) :edx)
	      (:load-lexical (:lexical-binding ,value-var) :untagged-fixnum-ecx)
	      (:std)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	      (:movl :ecx :eax)
	      (:outw :ax :dx)
	      (:movl :edi :edx)
	      (:movl :edi :eax)
	      (:cld))
	    ,value-var))
	(:unsigned-byte32
	 `(let ((,value-var ,value)
		(,port-var ,port))
	    (with-inline-assembly (:returns :untagged-fixnum-ecx)
	      (:load-lexical (:lexical-binding ,port-var) :edx)
	      (:load-lexical (:lexical-binding ,value-var) :untagged-fixnum-ecx)
	      (:std)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	      (:movl :ecx :eax)
	      (:outl :eax :dx)
	      (:movl :edi :edx)
	      (:movl :edi :eax)
	      (:cld))))
	(:location
	 `(let ((,value-var ,value)
		(,port-var ,port))
	    (with-inline-assembly (:returns :nothing)
	      (:load-lexical (:lexical-binding ,port-var) :edx)
	      (:load-lexical (:lexical-binding ,value-var) :eax)
	      (:andl -8 :eax)
	      (:std)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	      (:outl :eax :dx)
	      (:movl :edi :edx)
	      (:movl :edi :eax)
	      (:cld))
	    ,value-var))
	(:character
	 `(let ((,value-var ,value)
		(,port-var ,port))
	    (with-inline-assembly (:returns :nothing)
	      (:load-lexical (:lexical-binding ,port-var) :edx)
	      (:load-lexical (:lexical-binding ,value-var) :eax)
	      (:std)
	      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
	      (:shrl 8 :eax)
	      (:outb :al :dx)
	      (:movl :edi :edx)
	      (:movl :edi :eax)
	      (:cld))
	    ,value-var))))
     (t form))))

(defun (setf io-port) (value port type)
  (ecase type
    (:unsigned-byte8
     (setf (io-port port :unsigned-byte8) value))
    (:unsigned-byte16
     (setf (io-port port :unsigned-byte16) value))
    (:unsigned-byte32
     (setf (io-port port :unsigned-byte32) value))
    (:location
     (setf (io-port port :location) value))
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
    `(let ((,io-var (check-the (unsigned-byte 16) ,io-base-form)))
       (let ((,name ,io-var))
	 (declare (ignorable ,name))
	 (macrolet ((,name (offset &optional (type :unsigned-byte8))
		      `(io-port (+ ,',io-var ,offset) ,type)))
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
    (let ((port-var (gensym "port-var-"))
	  (object-var (gensym "object-var-"))
	  (byte-size (movitz:movitz-eval byte-size env)))
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
		 `(let ((,port-var ,port)
			(,object-var ,object))
		    (with-inline-assembly-case ()
		      (do-case (t :eax)
			(:compile-two-forms (:edx :ebx) ,port-var ,object-var)
			(:std)
			(:shrl ,movitz::+movitz-fixnum-shift+ :edx)
			,@(loop for i from start below end
			      appending
				`((:inl :dx :eax)
				  (:movl :eax (:ebx ,(+ offset (* 4 i))))))
			(:movl :edi :edx)
			(:movl :ebx :eax)
			(:cld))))
	       `(let ((,port-var ,port)
		      (,object-var ,object))
		  (with-inline-assembly-case ()
		    (do-case (t :eax :labels (io-read-loop end-io-read-loop not-fixnum))
		      (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		      (:std)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      (:movl ,(cl:* movitz::+movitz-fixnum-factor+ start) :ecx)
		     io-read-loop
		      (:cmpl :ecx ,(cl:* movitz::+movitz-fixnum-factor+ end))
		      (:jbe 'end-io-read-loop)
		      (:addl 4 :ecx)
		      (:inl :dx :eax)
		      (:movl :eax (:ebx ,(+ offset -4) :ecx))
		      (:jmp 'io-read-loop)
		     end-io-read-loop
		      (:movl :edi :edx)
		      (:movl :edi :eax)
		      (:cld)
		      (:movl :ebx :eax))))))
	    (:16-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     (if (and t (<= 1 count 20))
		 `(let ((,port-var ,port)
			(,object-var ,object))
		    (with-inline-assembly-case ()
		      (do-case (t :eax)
			(:std)
			(:compile-two-forms (:edx :ebx) ,port-var ,object-var)
			(:shrl ,movitz::+movitz-fixnum-shift+ :edx)
			,@(loop for i from start below end
			      appending
				`((:inw :dx :ax)
				  (:movw :ax (:ebx ,(+ offset (* 2 i))))))
			(:movl :edi :edx)
			(:movl :ebx :eax)
			(:cld))))
	       `(let ((,port-var ,port)
		      (,object-var ,object))
		  (with-inline-assembly-case ()
		    (do-case (t :eax :labels (io-read-loop end-io-read-loop not-fixnum))
		      (:std)
		      (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      (:movl ,(cl:* 1 start) :ecx)
		     io-read-loop
		      (:cmpl ,end :ecx)
		      (:ja 'end-io-read-loop)
		      (:addl 1 :ecx)
		      (:inw :dx :ax)
		      (:movw :ax (:ebx ,(+ offset -2) (:ecx 2)))
		      (:jmp 'io-read-loop)
		     end-io-read-loop
		      (:movl :edi :edx)
		      (:movl :ebx :eax)
		      (:cld))))))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       ((and (movitz:movitz-constantp offset env))
	(let ((start-var (gensym "start-"))
	      (end-var (gensym "end-"))
	      (offset (movitz:movitz-eval offset env)))
	  (case byte-size
	    (:8-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop not-fixnum zero-length))
		    (:std)
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:subl :ecx :eax)	; EAX = length
		    (:jna 'zero-length)
		    (:movl :eax :esi)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
		   io-read-loop
		    (:inb :dx :al)
		    (:addl 1 :ecx)
		    (:subl ,movitz:+movitz-fixnum-factor+ :esi)
		    (:movb :al (:ebx ,(+ offset -1) (:ecx 1)))
		    (:ja 'io-read-loop)
		   zero-length
		    (:movl :edi :edx)
		    (:movl :edi :eax)
		    (:cld)
		    (:movl :ebx :eax)))))
	    (:16-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop not-fixnum zero-length))
		    (:std)		; only EBX is GC root now
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:subl :ecx :eax)
		    (:jna 'zero-length)
		    (:movl :eax :esi)	; ESI = length
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
		   io-read-loop
		    (:inw :dx :ax)
		    (:addl 2 :ecx)
		    (:movw :ax (:ebx ,(+ offset -2) (:ecx 1)))
		    (:subl ,(* 2 movitz:+movitz-fixnum-factor+) :esi)
		    (:ja 'io-read-loop)
		   zero-length
		    (:movl :edi :edx)	; safe value
		    (:movl :edi :eax)
		    (:cld)
		    (:movl :ebx :eax)
		    (:movl (:ebp -4) :esi)))))
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop end-io-read-loop not-fixnum))
		    (:std)		; only EBX is GC root now
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:pushl :eax)	; keep end in (:esp)
		   io-read-loop
		    (:cmpl :ecx (:esp))
		    (:jbe 'end-io-read-loop)
		    (:inw :dx :ax)
		    (:addl 4 :ecx)
		    (:movw :ax (:ebx ,(+ offset -4) :ecx))
		    (:jmp 'io-read-loop)
		   end-io-read-loop
		    (:popl :edx)	; increment :esp, and put a lispval in :edx.
		    (:movl :ebx :eax)
		    (:cld)))))
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
    (let ((port-var (gensym "port-var-"))
	  (object-var (gensym "object-var-"))
	  (byte-size (movitz:movitz-eval byte-size env)))
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
		 `(let ((,port-var ,port)
			(,object-var ,object))
		    (with-inline-assembly-case ()
		      (do-case (t :eax)
			(:std)
			(:compile-two-forms (:edx :ebx) ,port-var ,object-var)
			(:shrl ,movitz::+movitz-fixnum-shift+ :edx)
			,@(loop for i from start below end
			      appending
				`((:movl (:ebx ,(+ offset (* 4 i))) :eax)
				  (:outl :eax :dx)))
			(:movl :edi :edx)
			(:movl :ebx :eax)
			(:cld))))
	       `(let ((,port-var ,port)
		      (,object-var ,object))
		  (with-inline-assembly-case ()
		    (do-case (t :eax :labels (io-read-loop end-io-read-loop not-fixnum))
		      (:std)
		      (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		      (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		      (:movl ,(cl:* movitz::+movitz-fixnum-factor+ start) :ecx)
		     io-read-loop
		      (:cmpl :ecx ,(cl:* movitz::+movitz-fixnum-factor+ end)) ; XXX
		      (:jbe 'end-io-read-loop)
		      (:addl 4 :ecx)
		      (:movl (:ebx ,(+ offset -4) :ecx) :eax)
		      (:outl :eax :dx)
		      (:jmp 'io-read-loop)
		     end-io-read-loop
		      (:movl :edi :edx)
		      (:movl :ebx :eax)
		      (:cld))))))
	    (t (error "~S byte-size ~S not implemented." (car form) byte-size)))))
       ((and (movitz:movitz-constantp offset env))
	(let ((start-var (gensym "start-"))
	      (end-var (gensym "end-"))
	      (offset (movitz:movitz-eval offset env)))
	  (case byte-size
	    (:8-bit
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop not-fixnum zero-length))
		    (:std)
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:subl :ecx :eax)	; EAX = length
		    (:jna 'zero-length)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
		    (:pushl :eax)	; keep end in (:esp)
		   io-read-loop
		    (:addl 1 :ecx)
		    (:subl ,movitz:+movitz-fixnum-factor+ (:esp))
		    (:movb (:ebx ,(+ offset -1) (:ecx 1)) :al)
		    (:outb :al :dx)
		    (:jnz 'io-read-loop)
		    (:popl :edx)	; increment :esp, and put a lispval in :edx.
		   zero-length
		    (:movl :ebx :eax)
		    (:cld)))))
	    (:16-bit
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop not-fixnum zero-length))
		    (:std)
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:subl :ecx :eax)
		    (:jna 'zero-length)
		    (:movl :eax :esi)	; ESI = length
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
		   io-read-loop
		    (:addl 2 :ecx)
		    (:movw (:ebx ,(+ offset -2) (:ecx 1)) :ax)
		    (:outw :ax :dx)
		    (:subl ,(* 2 movitz:+movitz-fixnum-factor+) :esi)
		    (:ja 'io-read-loop)
		   zero-length
		    (:movl :edi :edx)
		    (:movl :edi :eax)
		    (:cld)
		    (:movl :ebx :eax)
		    (:movl (:ebp -4) :esi)))))
	    (:32-bit
	     (assert (= 4 movitz:+movitz-fixnum-factor+))
	     `(let ((,port-var ,port)
		    (,object-var ,object)
		    (,start-var ,start)
		    (,end-var ,end))
		(with-inline-assembly-case ()
		  (do-case (t :eax :labels (io-read-loop not-fixnum end-io-read-loop))
		    (:std)
		    (:compile-two-forms (:edx :ebx) ,port-var ,object-var)
		    (:compile-two-forms (:ecx :eax) ,start-var ,end-var)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :edx)
		    (:shrl ,movitz::+movitz-fixnum-shift+ :ecx)
		    (:pushl :eax)	; keep end in (:esp)
		   io-read-loop
		    (:cmpl :ecx (:esp))
		    (:jbe 'end-io-read-loop)
		    (:addl 4 :ecx)
		    (:movl (:ebx ,(+ offset -4) (:ecx 1)) :eax)
		    (:outl :eax :dx)
		    (:jmp 'io-read-loop)
		   end-io-read-loop
		    (:popl :edx)	; increment :esp, and put a lispval in :edx.
		    (:movl :ebx :eax)
		    (:cld)))))
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

