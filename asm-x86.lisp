;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2007 Frode V. Fjeld
;;;; 
;;;; Description:   x86 assembler for 16, 32, and 64-bit modes.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: asm-x86.lisp,v 1.39 2008-08-06 09:43:36 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defpackage asm-x86
  (:use :common-lisp :asm)
  (:export #:assemble-instruction
	   #:disassemble-instruction
	   #:*cpu-mode*
	   #:*position-independent-p*))

(in-package asm-x86)

(defvar *cpu-mode* :32-bit)

(defvar *instruction-encoders*
  (make-hash-table :test 'eq))

(defvar *use-jcc-16-bit-p* nil
  "Whether to use 16-bit JCC instructions in 32-bit mode.")

(defun prefix-lookup (prefix-name)
  (cdr (or (assoc prefix-name
		  '((:operand-size-override . #x66)
		    (:address-size-override . #x67)
		    (:16-bit-operand . #x66)
		    (:16-bit-address . #x67)
		    (:lock . #xf0)
		    (:repne . #xf2)
		    (:repz . #xf3)
		    (:cs-override . #x2e)
		    (:ss-override . #x36)
		    (:ds-override . #x3e)
		    (:es-override . #x26)
		    (:fs-override . #x64)
		    (:gs-override . #x65)))
	   (error "There is no instruction prefix named ~S." prefix-name))))

(defun rex-encode (rexes &key rm)
  (let ((rex (logior (if (null rexes)
			 0
			 (+ #x40 (loop for rex in rexes
				    sum (ecase rex
					  (:rex.w #b1000)
					  (:rex.r #b0100)
					  (:rex.x #b0010)
					  (:rex.b #b0001)))))
		     (if (not rm)
			 0
			 (ldb (byte 1 3) rm)))))
    (unless (zerop rex)
      (list rex))))



(deftype octet ()
  '(unsigned-byte 8))

(deftype xint (size)
  `(or (unsigned-byte ,size)
       (signed-byte ,size)))

(deftype uint (size)
  `(unsigned-byte ,size))

(deftype sint (size)
  `(signed-byte ,size))

(defun integer-to-octets (i n)
  "Return list of n octets, encoding i in signed little endian."
  (loop for b from 0 below (* 8 n) by 8
     collect (ldb (byte 8 b) i)))

(defun encode-values-fun (operator legacy-prefixes prefixes rexes opcode mod reg rm scale index base displacement immediate operand-size address-size)
  (assert opcode)
  (when (or (and (eq address-size :32-bit)
		 (eq *cpu-mode* :64-bit))
	    (and (eq address-size :16-bit)
		 (eq *cpu-mode* :32-bit))
	    (and (eq address-size :64-bit)
		 (eq *cpu-mode* :32-bit))
	    (and (eq address-size :32-bit)
		 (eq *cpu-mode* :16-bit)))
    (pushnew :address-size-override
	     prefixes))
  (when (or (and (eq operand-size :16-bit)
		 (eq *cpu-mode* :64-bit))
	    (and (eq operand-size :16-bit)
		 (eq *cpu-mode* :32-bit))
	    (and (eq operand-size :32-bit)
		 (eq *cpu-mode* :16-bit)))
    (pushnew :operand-size-override
	     prefixes))
  (let ((code (append legacy-prefixes
		      (mapcar #'prefix-lookup (reverse prefixes))
		      (rex-encode rexes :rm rm)
		      (when (< 16 (integer-length opcode))
			(list (ldb (byte 8 16) opcode)))
		      (when (< 8(integer-length opcode))
			(list (ldb (byte 8 8) opcode)))
		      (list (ldb (byte 8 0) opcode))
		      (when (or mod reg rm)
			(assert (and mod reg rm) (mod reg rm)
				"Either all or none of mod, reg, and rm must be defined. mod=~S, reg=~S, rm=~S." mod reg rm)
			(check-type mod (unsigned-byte 2))
			(list (logior (ash (ldb (byte 2 0) mod)
					   6)
				      (ash (ldb (byte 3 0) reg)
					   3)
				      (ash (ldb (byte 3 0) rm)
					   0))))
		      (when (or scale index base)
			(assert (and scale index base) (scale index base)
				"Either all or none of scale, index, and base must be defined. scale=~S, index=~S, base=~S." scale index base)
			(check-type scale (unsigned-byte 2))
			(check-type index (unsigned-byte 4))
			(check-type base (unsigned-byte 4))
			(list (logior (ash (ldb (byte 2 0) scale)
					   6)
				      (ash (ldb (byte 3 0) index)
					   3)
				      (ash (ldb (byte 3 0) base)
					   0))))
		      displacement
		      immediate)))
    (append (compute-extra-prefixes operator *pc* (length code))
	    code)))

(defmacro encode (values-form)
  `(multiple-value-call #'encode-values-fun operator legacy-prefixes ,values-form))

(defmacro merge-encodings (form1 form2)
  `(multiple-value-bind (prefixes1 rexes1 opcode1 mod1 reg1 rm1 scale1 index1 base1 displacement1 immediate1 operand-size1 address-size1)
       ,form1
     (multiple-value-bind (prefixes2 rexes2 opcode2 mod2 reg2 rm2 scale2 index2 base2 displacement2 immediate2 operand-size2 address-size2)
	 ,form2
       (macrolet ((getone (a b name)
		    `(cond
		       ((and ,a ,b)
			(error "~A doubly defined: ~S and ~S." ',name ,a ,b))
		       (,a)
		       (,b))))
	 (encoded-values :prefixes (append prefixes1 prefixes2)
			 :rex (append (if (listp rexes1)
					  rexes1
					  (list rexes1))
				      (if (listp rexes2)
					  rexes2
					  (list rexes2)))
			 :opcode (getone opcode1 opcode2 opcode)
			 :mod (getone mod1 mod2 mod)
			 :reg (getone reg1 reg2 reg)
			 :rm (getone rm1 rm2 rm)
			 :scale (getone scale1 scale2 scale)
			 :index (getone index1 index2 index)
			 :base (getone base1 base2 base)
			 :displacement (getone displacement1 displacement2 displacement)
			 :immediate (getone immediate1 immediate2 immediate)
			 :operand-size (getone operand-size1 operand-size2 operand-size)
			 :address-size (getone address-size1 address-size2 address-size))))))


(defun encoded-values (&key prefixes prefix rex opcode mod reg rm scale index base displacement immediate operand-size address-size)
  (values (append (when prefix
		    (list prefix))
		  prefixes)
	  (if (keywordp rex)
	      (list rex)
	      rex)
	  opcode
	  mod reg rm
	  scale index base
	  displacement
	  immediate
	  operand-size
	  address-size))
 
(defun assemble-instruction (instruction)
  "Assemble a single instruction to a list of octets of x86 machine code, according to *cpu-mode* etc."
  (multiple-value-bind (instruction legacy-prefixes options)
      (if (listp (car instruction))
	  (values (cdr instruction)
		  (remove-if #'listp (car instruction))
		  (remove-if #'keywordp (car instruction)))
	  (values instruction
		  nil
		  nil))
    (destructuring-bind (operator &rest operands)
	instruction
      (multiple-value-bind (code failp)
	  (apply (or (gethash operator *instruction-encoders*)
		     (error "Unknown instruction operator ~S in ~S." operator instruction))
		 operator
		 (mapcar #'prefix-lookup legacy-prefixes)
		 operands)
	(cond
	  (failp
	   (error "Unable to encode ~S." instruction))
	  ((null options)
	   code)
	  ((assoc :size options)
	   (assert (= (second (assoc :size options))
		      (length code)))
	   code))))))

(defmacro define-operator (operator operator-mode lambda-list &body body)
  (check-type operator keyword)
  (labels ((find-forms (body)
	     (cond
	       ((atom body)
		nil)
	       ((member (car body) '(reg-modrm modrm opcode imm-modrm imm opcode-reg
				     opcode-reg-imm pc-rel moffset sreg-modrm reg-cr
				     far-pointer))
		(list body))
	       (t (mapcan #'find-forms body)))))
    (let ((defun-name (intern (format nil "~A-~A" 'instruction-encoder operator))))
      `(progn
	 (defun ,defun-name (operator legacy-prefixes ,@lambda-list)
	   (declare (ignorable operator legacy-prefixes))
	   (let ((operator-mode ',operator-mode)
		 (default-rex nil))
	     (declare (ignorable operator-mode default-rex))
	     (macrolet ((disassembler (&body body)
			  (declare (ignore body)))
			(assembler (&body body)
			  `(progn ,@body)))
	       (block operator
		 ,@body
		 (values nil 'fail)))))
	 (setf (gethash ',operator *instruction-encoders*)
	       ',defun-name)
	 (macrolet ((disassembler (&body body)
		      `(progn ,@body))
		    (assembler (&body body)
		      (declare (ignore body))))
	   (let ((operator ',operator)
		 (operator-mode ',operator-mode)
		 (operand-formals ',lambda-list))
	     (declare (ignorable operator operand-formals operator-mode))
	     ,@(find-forms body)))
	 ',operator))))

(defmacro define-operator/none (name lambda-list &body body)
  `(define-operator ,name nil ,lambda-list ,@body))

(deftype list-of (&rest elements)
  "A list with elements of specified type(s)."
  (labels ((make-list-of (elements)
	     (if (null elements)
		 'null
		 `(cons ,(car elements)
			,(make-list-of (cdr elements))))))
    (make-list-of elements)))

(deftype list-of* (&rest elements)
  "A list starting with elements of specified type(s)."
  (labels ((make-list-of (elements)
	     (if (null elements)
		 'list
		 `(cons ,(car elements)
			,(make-list-of (cdr elements))))))
    (make-list-of elements)))

(defparameter *opcode-disassemblers-16*
  (make-array 256 :initial-element nil))

(defparameter *opcode-disassemblers-32*
  (make-array 256 :initial-element nil))

(defparameter *opcode-disassemblers-64*
  (make-array 256 :initial-element nil))

(deftype disassembly-decoder ()
  '(list-of* boolean keyword (or keyword null) symbol))

(defun (setf opcode-disassembler) (decoder opcode operator-mode)
  (check-type decoder disassembly-decoder)
  (labels ((set-it (table pos)
	     (check-type pos (integer 0 *))
	     (check-type table (simple-vector 256))
	     (let ((bit-pos (* 8 (1- (ceiling (integer-length pos) 8)))))
	       (if (not (plusp bit-pos))
		   (progn
		     #+(or) (unless (or (eq nil decoder)
					(eq nil (svref table pos))
					(equal decoder (svref table pos)))
			      (warn "Redefining disassembler for ~@[~(~A~) ~]opcode #x~X from ~{~S ~}to ~{~S~^ ~}."
				    operator-mode opcode (svref table pos) decoder))
		     (setf (svref table pos) decoder))
		   (set-it (or (svref table (ldb (byte 8 bit-pos) pos))
			       (setf (svref table (ldb (byte 8 bit-pos) pos))
				     (make-array 256 :initial-element nil)))
			   (ldb (byte bit-pos 0) pos))))))
    (ecase operator-mode
      (:16-bit
       (set-it *opcode-disassemblers-16* opcode))
      (:32-bit
       (set-it *opcode-disassemblers-32* opcode))
      (:64-bit
       (set-it *opcode-disassemblers-64* opcode))
      ((:8-bit nil)
       (set-it *opcode-disassemblers-16* opcode)
       (set-it *opcode-disassemblers-32* opcode)
       (set-it *opcode-disassemblers-64* opcode)))))


(defmacro pop-code (code-place &optional context)
  `(progn
     (unless ,code-place
       (error "End of byte-stream in the middle of an instruction."))
     (let ((x (pop ,code-place)))
     (check-type x (unsigned-byte 8) ,(format nil "an octet (context: ~A)" context))
     x)))

(defmacro code-call (form &optional (code-place (case (car form) ((funcall apply) (third form)) (t (second form)))))
  "Execute form, then 'magically' update the code binding with the secondary return value from form."
  `(let (tmp)
     (declare (ignorable tmp))
     (setf (values tmp ,code-place) ,form)))

(defmacro define-disassembler ((operator opcode &optional cpu-mode digit backup-p operand-size) lambda-list &body body)
  (cond
    (digit
     `(loop for mod from #b00 to #b11
	 do (loop for r/m from #b000 to #b111
	       as ext-opcode = (logior (ash ,opcode 8)
				       (ash ,digit 3)
				       (ash mod 6)
				       r/m)
	       do (define-disassembler (,operator ext-opcode ,cpu-mode nil t ,operand-size) ,lambda-list ,@body))))
    ((symbolp lambda-list)
     `(setf (opcode-disassembler ,opcode ,cpu-mode) (list ,backup-p ,operator ,(or operand-size cpu-mode) ',lambda-list ,@body)))
    (t (let ((defun-name (intern (format nil "~A-~A-~X~@[-~A~]" 'disassembler operator opcode cpu-mode))))
	 `(progn
	    (defun ,defun-name ,lambda-list ,@body)
	    (setf (opcode-disassembler ,opcode ',cpu-mode) (list ,backup-p ,operator ',(or operand-size cpu-mode) ',defun-name))
	    ',defun-name)))))

(defun disassemble-simple-prefix (code operator opcode operand-size address-size rex)
  (declare (ignore opcode rex))
  (let ((instruction (code-call (disassemble-instruction code operand-size address-size nil))))
    (values (if (consp (car instruction))
		(list* (list* operator (car instruction))
		       (cdr instruction))
		(list* (list operator)
		       instruction))
	    code)))

(define-disassembler (:lock #xf0) disassemble-simple-prefix)
(define-disassembler (:repne #xf2) disassemble-simple-prefix)
(define-disassembler (:repz #xf3) disassemble-simple-prefix)
(define-disassembler (:cs-override #x2e) disassemble-simple-prefix)
(define-disassembler (:ss-override #x36) disassemble-simple-prefix)
(define-disassembler (:ds-override #x3e) disassemble-simple-prefix)
(define-disassembler (:es-override #x26) disassemble-simple-prefix)
(define-disassembler (:fs-override #x64) disassemble-simple-prefix)
(define-disassembler (:gs-override #x65) disassemble-simple-prefix)

(define-disassembler (:operand-size-override #x66 :32-bit) (code operator opcode operand-size address-size rex)
  (declare (ignore operator opcode operand-size rex))
  (disassemble-instruction code :16-bit address-size nil))

(define-disassembler (:address-size-override #x67 :32-bit) (code operator opcode operand-size address-size rex)
  (declare (ignore operator opcode address-size rex))
  (disassemble-instruction code operand-size :16-bit nil))

(define-disassembler (:operand-size-override #x66 :16-bit) (code operator opcode operand-size address-size rex)
  (declare (ignore operator opcode operand-size rex))
  (disassemble-instruction code :32-bit address-size nil))

(define-disassembler (:address-size-override #x67 :16-bit) (code operator opcode operand-size address-size rex)
  (declare (ignore operator opcode address-size rex))
  (disassemble-instruction code operand-size :32-bit nil))

(defmacro define-operator/8 (operator lambda-list &body body)
  `(define-operator ,operator :8-bit ,lambda-list
     (let ((default-rex nil))
       (declare (ignorable default-rex))
       ,@body)))

(defmacro define-operator/16 (operator lambda-list &body body)
  `(define-operator ,operator :16-bit ,lambda-list
     (let ((default-rex nil))
       (declare (ignorable default-rex))
       ,@body)))

(defmacro define-operator/32 (operator lambda-list &body body)
  `(define-operator ,operator :32-bit ,lambda-list
     (let ((default-rex nil))
       (declare (ignorable default-rex))
       ,@body)))

(defmacro define-operator/64 (operator lambda-list &body body)
  `(define-operator ,operator :64-bit ,lambda-list
     (let ((default-rex '(:rex.w)))
       (declare (ignorable default-rex))
       ,@body)))

(defmacro define-operator/64* (operator lambda-list &body body)
  `(define-operator ,operator :64-bit ,lambda-list
     (let ((default-rex (case *cpu-mode*
			  (:64-bit nil)
			  (t '(:rex.w)))))
       (declare (ignorable default-rex))
       ,@body)))

(defmacro define-operator* ((&key |16| |32| |64| dispatch) args &body body)
  (let ((body16 (subst '(xint 16) :int-16-32-64
                       (subst :dx :dx-edx-rdx
                              (subst :ax :ax-eax-rax body))))
        (body32 (subst '(xint 32) :int-16-32-64
                       (subst :edx :dx-edx-rdx
                              (subst :eax :ax-eax-rax body))))
        (body64 (subst '(sint 32) :int-16-32-64
                       (subst :rdx :dx-edx-rdx
                              (subst :rax :ax-eax-rax body)))))
    `(progn
       ,(when |16|
              `(define-operator/16 ,|16| ,args ,@body16))
       ,(when |32|
              `(define-operator/32 ,|32| ,args ,@body32))
       ,(when |64|
              `(define-operator/64 ,|64| ,args ,@body64))
       ,(when dispatch
	      (let ((dispatch-name (intern (format nil "~A-~A" 'instruction-dispatcher dispatch))))
		`(progn
		   (defun ,dispatch-name (&rest args)
		     (declare (dynamic-extent args))
		     (loop for encoder in (ecase *cpu-mode*
					    (:32-bit ',(remove nil (list |32| |16| |64|)))
					    (:64-bit ',(remove nil (list |64| |32| |16|)))
					    (:16-bit ',(remove nil (list |16| |32| |64|))))
			thereis (apply (gethash encoder *instruction-encoders*) args)
			finally (return (values nil 'fail))))
		   (setf (gethash ',dispatch *instruction-encoders*)
			 ',dispatch-name))))
       nil)))

(defun resolve-and-encode (x type &key size)
  (encode-integer (cond
		    ((typep x type)
		     x)
		    ((integerp x)
		     (error "Immediate value #x~X out of range for ~S." x type))
		    ((assoc x *symtab*)
		     (let ((value (cdr (assoc x *symtab*))))
		       (assert (typep value type))
		       value))
		    (t (error "Unresolved symbol ~S (size ~S)." x size)))
		  type))

(defun resolve-pc-relative (operand)
  (etypecase operand
    (pc-relative-operand
     (reduce #'+ (cdr operand)
	     :key #'resolve-operand))
    (symbol-reference
     (assert *pc* (*pc*) "Cannot encode a pc-relative operand without a value for ~S." '*pc*)
     (- (resolve-operand operand)
	*pc*))))

(defun encode-integer (i type)
  (assert (typep i type))
  (let ((bit-size (cadr type)))
    (loop for b upfrom 0 below bit-size by 8
       collect (ldb (byte 8 b) i))))	 

(defun type-octet-size (type)
  (assert (member (car type)
		  '(sint uint xint))
	  (type))
  (values (ceiling (cadr type) 8)))

(defun opcode-octet-size (opcode)
  (loop do (setf opcode (ash opcode -8))
     count t
     while (plusp opcode)))

(defun parse-indirect-operand (operand)
  (assert (indirect-operand-p operand))
  (let (reg offsets reg2 reg-scale)
    (dolist (expr operand)
      (etypecase expr
	(register-operand
	 (if reg
	     (setf reg2 expr)
	     (setf reg expr)))
	((cons register-operand
	       (cons (member 1 2 4 8) null))
	 (when reg
	   (assert (not reg-scale))
	   (setf reg2 reg))
	 (setf reg (first expr)
	       reg-scale (second expr)))
	(immediate-operand
	 (push expr offsets))
	((cons (eql :+))
	 (dolist (term (cdr expr))
	   (push term offsets)))))
    (when (and (eq reg2 :esp)
	       (or (not reg-scale)
		   (eql 1 reg-scale)))
      (psetf reg reg2
	     reg2 reg))
    (values reg offsets reg2 (if (not reg)
				 nil
				 (or reg-scale 1)))))

(defun register-set-by-mode (mode)
  (ecase mode
    (:8-bit  '(:al :cl :dl :bl :ah :ch :dh :bh))
    (:16-bit '(:ax :cx :dx :bx :sp :bp :si :di))
    (:32-bit '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
    (:64-bit '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :13 :r14 :r15))
    (:mm '(:mm0 :mm1 :mm2 :mm3 :mm4 :mm5 :mm6 :mm7))
    (:xmm '(:xmm0 :xmm1 :xmm2 :xmm3 :xmm4 :xmm5 :xmm6 :xmm7))
    (:segment '(:es :cs :ss :ds :fs :gs))))

(defun encode-reg/mem (operand mode)
  (check-type mode (member nil :8-bit :16-bit :32-bit :64-bit :mm :xmm))
  (if (and mode (keywordp operand))
      (encoded-values :mod #b11
		      :rm (or (position operand (register-set-by-mode mode))
			      (error "Unknown ~(~D~) register ~S." mode operand)))
      (multiple-value-bind (reg offsets reg2 reg-scale)
	  (parse-indirect-operand operand)
	(check-type reg-scale (member nil 1 2 4 8))
	(assert (or (not reg2)
		    (and reg reg2)))
	(assert (or (not reg-scale)
		    (and reg reg-scale)))
	(let ((offset (reduce #'+ offsets
			      :key #'resolve-operand)))
	  (cond
            ((and (not reg)
                  (eq mode :16-bit)
                  (typep offset '(xint 16)))
             (encoded-values :mod #b00
                             :rm #b110
                             :address-size :16-bit
                             :displacement (encode-integer offset '(xint 16))))
	    ((and (not reg)
		  (typep offset '(xint 32)))
	     (encoded-values :mod #b00
			     :rm #b101
                             :address-size :32-bit
			     :displacement (encode-integer offset '(xint 32))))
	    ((and (eq reg :sp)
		  (not reg2)
		  (= 1 reg-scale))
	     (etypecase offset
	       ((eql 0)
		(encoded-values :mod #b00
				:rm #b100
				:scale 0
				:index #b100
				:base #b100
				:address-size :16-bit))
	       ((sint 8)
		(encoded-values :mod #b01
				:rm #b100
				:displacement (encode-integer offset '(sint 8))
				:scale 0
				:index #b100
				:base #b100
				:address-size :16-bit))
	       ((xint 32)
		(encoded-values :mod #b10
				:rm #b100
				:displacement (encode-integer offset '(xint 32))
				:scale 0
				:index #b100
				:base #b100
				:address-size :16-bit))))
	    ((and (eq reg :esp)
		  (= 1 reg-scale))
	     (let ((reg2-index (or (position reg2 '(:eax :ecx :edx :ebx nil :ebp :esi :edi))
				   (error "Unknown reg2 [F] ~S." reg2))))
	       (etypecase offset
		 ((eql 0)
		  (encoded-values :mod #b00
				  :rm #b100
				  :scale 0
				  :index reg2-index
				  :base #b100
				  :address-size :32-bit))
		 ((sint 8)
		  (encoded-values :mod #b01
				  :rm #b100
				  :displacement (encode-integer offset '(sint 8))
				  :scale 0
				  :index reg2-index
				  :base #b100
				  :address-size :32-bit))
		 ((xint 32)
		  (encoded-values :mod #b10
				  :rm #b100
				  :displacement (encode-integer offset '(xint 32))
				  :scale 0
				  :index reg2-index
				  :base #b100
				  :address-size :32-bit)))))
	    ((and (eq reg :rsp)
		  (not reg2)
		  (= 1 reg-scale))
	     (etypecase offset
	       ((eql 0)
		(encoded-values :mod #b00
				:rm #b100
				:scale 0
				:index #b100
				:base #b100
				:address-size :64-bit))
	       ((sint 8)
		(encoded-values :mod #b01
				:rm #b100
				:displacement (encode-integer offset '(sint 8))
				:scale 0
				:index #b100
				:base #b100
				:address-size :64-bit))
	       ((sint 32)
		(encoded-values :mod #b10
				:rm #b100
				:displacement (encode-integer offset '(sint 32))
				:scale 0
				:index #b100
				:base #b100
				:address-size :64-bit))))
	    (t (multiple-value-bind (register-index map address-size)
		   (let* ((map32 '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
			  (index32 (position reg map32))
			  (map64 '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :r13 :r14 :r15))
			  (index64 (unless index32
				     (position reg map64))))
		     (if index32
			 (values index32 map32 :32-bit)
			 (values index64 map64 :64-bit)))
		 (cond
		   ((and (not reg2)
			 register-index
			 (= 1 reg-scale)
			 (and (zerop offset)
			      (not (= register-index #b101))))
		    (encoded-values :mod #b00
				    :rm register-index
				    :address-size address-size))
		   ((and (not reg2)
			 register-index
			 (= 1 reg-scale)
			 (typep offset '(sint 8)))
		    (encoded-values :mod #b01
				    :rm register-index
				    :displacement (encode-integer offset '(sint 8))
				    :address-size address-size))
		   ((and (not reg2)
			 register-index
			 (= 1 reg-scale)
			 (or (typep offset '(sint 32))
			     (and (eq :32-bit address-size)
				  (typep offset '(xint 32)))))
		    (encoded-values :mod #b10
				    :rm register-index
				    :displacement (encode-integer offset '(sint 32))
				    :address-size address-size))
                   ((and (not reg2)
                         register-index
                         (if (eq :64-bit *cpu-mode*)
                             (typep offset '(sint 32))
                             (typep offset '(xint 32)))
                         (not (= #b100 register-index)))
                    (encoded-values :rm #b100
                                    :mod #b00
                                    :index register-index
                                    :base #b101
                                    :scale (or (position reg-scale '(1 2 4 8))
                                               (error "Unknown register scale ~S." reg-scale))
                                    :displacement (encode-integer offset '(xint 32))))
		   ((and reg2
			 register-index
			 (zerop offset)
			 (not (= register-index #b100)))
		    (encoded-values :mod #b00
				    :rm #b100
				    :scale (or (position reg-scale '(1 2 4 8))
                                               (error "Unknown register scale ~S." reg-scale))
				    :index register-index
				    :base (or (position reg2 map)
					      (error "unknown reg2 [A] ~S" reg2))
				    :address-size address-size))
		   ((and reg2
			 register-index
			 (typep offset '(sint 8))
			 (not (= register-index #b100)))
		    (encoded-values :mod #b01
				    :rm #b100
				    :scale (position reg-scale '(1 2 4 8))
				    :index register-index
				    :base (or (position reg2 map)
					      (error "unknown reg2 [B] ~S" reg2))
				    :address-size address-size
				    :displacement (encode-integer offset '(sint 8))))
		   ((and reg2
			 register-index
			 (eq :32-bit address-size)
			 (typep offset '(sint 8))
			 (not (= register-index #b100)))
		    (encoded-values :mod #b01
				    :rm #b100
				    :scale (position reg-scale '(1 2 4 8))
				    :index register-index
				    :base (or (position reg2 map)
					      (error "unknown reg2 [C] ~S." reg2))
				    :address-size address-size
				    :displacement (encode-integer offset '(sint 8))))
		   ((and reg2
			 register-index
			 (eq :32-bit address-size)
			 (typep offset '(xint 32))
			 (not (= register-index #b100)))
		    (encoded-values :mod #b10
				    :rm #b100
				    :scale (position reg-scale '(1 2 4 8))
				    :index register-index
				    :base (or (position reg2 map)
					      (error "unknown reg2 [D] ~S." reg2))
				    :address-size address-size
				    :displacement (encode-integer offset '(xint 32))))
		   ((and reg2
			 register-index
			 (eq :64-bit address-size)
			 (typep offset '(sint 32))
			 (not (= register-index #b100)))
		    (encoded-values :mod #b01
				    :rm #b100
				    :scale (position reg-scale '(1 2 4 8))
				    :index register-index
				    :base (or (position reg2 map)
					      (error "unknown reg2 [E] ~S" reg2))
				    :address-size address-size
				    :displacement (encode-integer offset '(sint 32))))
		   (t (let ((rm16 (position-if (lambda (x)
						 (or (and (eq (car x) reg)
							  (eq (cdr x) reg2))
						     (and (eq (car x) reg2)
							  (eq (cdr x) reg))))
					       '((:bx . :si) (:bx . :di) (:bp . :si) (:bp . :di)
						 (:si) (:di) (:bp) (:bx)))))
			(cond
			  ((and rm16
				(zerop offset)
				(not (= #b110 rm16)))
			   (encoded-values :mod #b00
					   :rm rm16
					   :address-size :16-bit))
			  ((and rm16
				(typep offset '(sint 8)))
			   (encoded-values :mod #b01
					   :rm rm16
					   :address-size :16-bit
					   :displacement (encode-integer offset '(sint 8))))
			  ((and rm16
				(typep offset '(xint 16)))
			   (encoded-values :mod #b10
					   :rm rm16
					   :address-size :16-bit
					   :displacement (encode-integer offset '(xint 16))))
			  (t (error "Huh? reg: ~S, reg2: ~S, scale: ~S, offset: ~S" reg reg2 reg-scale offset)))))))))))))

(defun operand-ordering (formals &rest arrangement)
  (loop with rarrangement = (reverse arrangement)
     for formal in formals
     when (getf rarrangement formal)
     collect it))

(defun order-operands (ordering &rest operands)
  (loop for key in ordering
     collect (or (getf operands key)
		 (error "No operand ~S in ~S." key operands))))

(defun decode-integer (code type)
  "Decode an integer of specified type."
  (let* ((bit-size (cadr type))
	 (unsigned-integer (loop for b from 0 below bit-size by 8
			      sum (ash (pop-code code integer) b))))
    (values (if (or (not (member (car type) '(sint signed-byte)))
		    (not (logbitp (1- bit-size) unsigned-integer)))
		unsigned-integer
		(- (ldb (byte bit-size 0)
			(1+ (lognot unsigned-integer)))))
	    code)))

(defun disassemble-instruction (code &optional override-operand-size override-address-size rex)
  (labels ((lookup-decoder (table opcode)
	     (let* ((backup-code code)
		    (datum (pop-code code))
		    (opcode (logior (ash opcode 8)
				    datum))
		    (decoder (svref table datum)))
	       (typecase decoder
		 (vector
		  (lookup-decoder decoder opcode))
		 (disassembly-decoder
		  (when (car decoder)
		    (setf code backup-code))
		  (values (cdr decoder)
			  opcode))
		 (t (error "No disassembler registered for opcode #x~X." opcode))))))
    (multiple-value-bind (decoder opcode)
	(lookup-decoder (ecase (or override-operand-size *cpu-mode*)
			  (:16-bit *opcode-disassemblers-16*)
			  (:32-bit *opcode-disassemblers-32*)
			  (:64-bit *opcode-disassemblers-64*))
			0)
      (destructuring-bind (operator operand-size decoder-function &rest extra-args)
	  decoder
	(values (code-call (apply decoder-function
				  code
				  operator
				  opcode
				  (or operand-size override-operand-size)
				  (or override-address-size *cpu-mode*)
				  rex
				  extra-args))
		code)))))

(defun decode-no-operands (code operator opcode operand-size address-size rex &rest fixed-operands)
  (declare (ignore opcode operand-size address-size rex))
  (values (list* operator
		 (remove nil fixed-operands))
	  code))

(defun decode-reg-cr (code operator opcode operand-size address-size rex operand-ordering)
  (declare (ignore opcode operand-size address-size))
  (let ((modrm (pop-code code)))
    (values (list* operator
		   (order-operands operand-ordering
				   :reg (nth (ldb (byte 3 0) modrm)
					     (register-set-by-mode (if rex :64-bit :32-bit)))
				   :cr (nth (ldb (byte 3 3) modrm)
					    '(:cr0 :cr1 :cr2 :cr3 :cr4 :cr5 :cr6 :cr7))))
	    code)))

(defun decode-reg-modrm (code operator opcode operand-size address-size rex operand-ordering &optional (reg-mode operand-size))
  (declare (ignore opcode rex))
  (values (list* operator
		 (order-operands operand-ordering
				 :reg (nth (ldb (byte 3 3) (car code))
					   (register-set-by-mode reg-mode))
				 :modrm (ecase address-size
					  (:32-bit
					   (code-call (decode-reg-modrm-32 code operand-size)))
					  (:16-bit
					   (code-call (decode-reg-modrm-16 code operand-size))))))
	  code))
	      

(defun decode-modrm (code operator opcode operand-size address-size rex)
  (declare (ignore opcode rex))
  (values (list operator
		(ecase address-size
		  (:32-bit
		   (code-call (decode-reg-modrm-32 code operand-size)))
		  (:16-bit
		   (code-call (decode-reg-modrm-16 code operand-size)))))
	  code))

(defun decode-imm-modrm (code operator opcode operand-size address-size rex imm-type operand-ordering &key fixed-modrm)
  (declare (ignore opcode rex))
  (values (list* operator
		 (order-operands operand-ordering
				 :modrm (or fixed-modrm
					    (when (member :modrm operand-ordering)
					      (ecase address-size
						(:32-bit
						 (code-call (decode-reg-modrm-32 code operand-size)))
						(:16-bit
						 (code-call (decode-reg-modrm-16 code operand-size))))))
				 :imm (code-call (decode-integer code imm-type))))
	  code))

(defun decode-far-pointer (code operator opcode operand-size address-size rex type)
  (declare (ignore opcode operand-size address-size rex))
  (let ((offset (code-call (decode-integer code type)))
	(segment (code-call (decode-integer code '(uint 16)))))
    (values (list operator
		  segment
		  (list offset))
	    code)))

(defun decode-pc-rel (code operator opcode operand-size address-size rex type)
  (declare (ignore opcode operand-size address-size rex))
  (values (list operator
		`(:pc+ ,(code-call (decode-integer code type))))
	  code))

(defun decode-moffset (code operator opcode operand-size address-size rex type operand-ordering fixed-operand)
  (declare (ignore opcode operand-size address-size rex))
  (values (list* operator
		 (order-operands operand-ordering
				 :moffset (list (code-call (decode-integer code type)))
				 :fixed fixed-operand))
	  code))

(defun decode-opcode-reg (code operator opcode operand-size address-size rex operand-ordering extra-operand)
  (declare (ignore address-size rex))
  (values (list* operator
		 (order-operands operand-ordering
				 :reg (nth (ldb (byte 3 0) opcode)
					   (register-set-by-mode operand-size))
				 :extra extra-operand))
	  code))

(defun decode-opcode-reg-imm (code operator opcode operand-size address-size rex operand-ordering imm-type)
  (declare (ignore address-size rex))
  (values (list* operator
		 (order-operands operand-ordering
				 :reg (nth (ldb (byte 3 0) opcode)
					   (register-set-by-mode operand-size))
				 :imm (code-call (decode-integer code imm-type))))
	  code))

(defun decode-reg-modrm-16 (code operand-size)
  (let* ((modrm (pop-code code mod/rm))
	 (mod (ldb (byte 2 6) modrm))
	 (reg (ldb (byte 3 3) modrm))
	 (r/m (ldb (byte 3 0) modrm)))
    (values (if (= mod #b11)
		(nth reg (register-set-by-mode operand-size))
		(flet ((operands (i)
			 (nth i '((:bx :si) (:bx :di) (:bp :si) (:bp :di) (:si) (:di) (:bp) (:bx)))))
		  (ecase mod
		    (#b00
		     (case r/m
		       (#b110 (list (code-call (decode-integer code '(uint 16)))))
		       (t (operands r/m))))
		    (#b01
		     (append (operands r/m)
			     (list (code-call (decode-integer code '(sint 8))))))
		    (#b10
		     (append (operands r/m)
			     (list (code-call (decode-integer code '(uint 16)))))))))
	    code)))

(defun decode-reg-modrm-32 (code operand-size)
  "Return a list of the REG, and the MOD/RM operands."
  (let* ((modrm (pop-code code mod/rm))
	 (mod (ldb (byte 2 6) modrm))
	 (r/m (ldb (byte 3 0) modrm)))
    (values (if (= mod #b11)
		(nth r/m (register-set-by-mode operand-size))
		(flet ((decode-sib ()
			 (let* ((sib (pop-code code sib))
				(ss (ldb (byte 2 6) sib))
				(index (ldb (byte 3 3) sib))
				(base (ldb (byte 3 0) sib)))
			   (nconc (unless (= index #b100)
				    (let ((index-reg (nth index (register-set-by-mode :32-bit))))
				      (if (= ss #b00)
					  (list index-reg)
					  (list (list index-reg (ash 2 ss))))))
				  (if (/= base #b101)
				      (list (nth base (register-set-by-mode :32-bit)))
				      (ecase mod
					(#b00 nil)
					((#b01 #b10) (list :ebp))))))))
		  (ecase mod
		    (#b00 (case r/m
			    (#b100 (decode-sib))
			    (#b101 (code-call (decode-integer code '(uint 32))))
			    (t (list (nth r/m (register-set-by-mode :32-bit))))))
		    (#b01 (case r/m
			    (#b100 (nconc(decode-sib)
					 (list (code-call (decode-integer code '(sint 8))))))
			    (t (list (nth r/m (register-set-by-mode :32-bit))
				     (code-call (decode-integer code '(sint 8)))))))
		    (#b10 (case r/m
			    (#b100 (nconc (decode-sib)
					  (list (code-call (decode-integer code '(uint 32))))))
			    (t (list (nth r/m (register-set-by-mode :32-bit))
				     (code-call (decode-integer code '(uint 32))))))))))
	    code)))


(defmacro return-when (form)
  `(let ((x ,form))
     (when x (return-from operator x))))

(defmacro return-values-when (form)
  `(let ((x (encode ,form)))
     (when x (return-from operator x))))

(defmacro imm (imm-operand opcode imm-type &optional extra-operand &rest extras)
  `(progn
     (assembler
      (when (and ,@(when extra-operand
			 (list (list* 'eql extra-operand)))
		 (immediate-p ,imm-operand))
	(let ((immediate (resolve-operand ,imm-operand)))
	  (when (typep immediate ',imm-type)
	    (return-values-when
	     (encoded-values :opcode ,opcode
			     :immediate (encode-integer immediate ',imm-type)
			     :operand-size operator-mode
			     :rex default-rex
			     ,@extras))))))
     (disassembler
      ,(if extra-operand
	   `(define-disassembler (operator ,opcode operator-mode)
		decode-imm-modrm
	      ',imm-type
	      (operand-ordering operand-formals
				:imm ',imm-operand
				:modrm ',(first extra-operand))
	      :fixed-modrm ',(second extra-operand))
	   `(define-disassembler (operator ,opcode operator-mode)
		decode-imm-modrm
	      ',imm-type
	      '(:imm))))))

(defmacro imm-modrm (op-imm op-modrm opcode digit type)
  `(progn
     (assembler
      (when (immediate-p ,op-imm)
	(let ((immediate (resolve-operand ,op-imm)))
	  (when (typep immediate ',type)
	    (return-values-when
	     (merge-encodings (encoded-values :opcode ,opcode
					      :reg ,digit
					      :operand-size operator-mode
					      :rex default-rex
					      :immediate (encode-integer immediate ',type))
			      (encode-reg/mem ,op-modrm operator-mode)))))))
     (disassembler
      (define-disassembler (operator ,opcode operator-mode ,digit)
	  decode-imm-modrm
	',type
	(operand-ordering operand-formals
			  :imm ',op-imm
			  :modrm ',op-modrm)))))


(defun compute-extra-prefixes (operator pc size)
  (loop for (pattern . function) in *instruction-compute-extra-prefix-map*
     when (or (eq pattern t)
	      (eq pattern operator))
     return (funcall function pc size)))
	      

(defun encode-pc-rel (operator legacy-prefixes opcode operand type &rest extras)
  (when (typep operand '(or pc-relative-operand symbol-reference))
    (let* ((estimated-code-size-no-extras (+ (length legacy-prefixes)
					     (type-octet-size type)
					     (opcode-octet-size opcode)))
	   (estimated-extra-prefixes (compute-extra-prefixes operator *pc* estimated-code-size-no-extras))
	   (estimated-code-size (+ estimated-code-size-no-extras
				   (length estimated-extra-prefixes)))
	   (offset (let ((*pc* (when *pc*
				 (+ *pc* estimated-code-size))))
		     (resolve-pc-relative operand))))
      (when (typep offset type)
	(let ((code (let ((*instruction-compute-extra-prefix-map* nil))
		      (encode (apply #'encoded-values
				     :opcode opcode
				     :displacement (encode-integer offset type)
				     extras)))))
	  (if (= (length code)
		 estimated-code-size-no-extras)
	      (append estimated-extra-prefixes code)
	      (let* ((code-size (length code))
		     (extra-prefixes (compute-extra-prefixes operator *pc* code-size))
		     (offset (let ((*pc* (when *pc*
					   (+ *pc* code-size (length extra-prefixes)))))
			       (resolve-pc-relative operand))))
		(when (typep offset type)
		  (let ((code (let ((*instruction-compute-extra-prefix-map* nil))
				(encode (apply #'encoded-values
					       :opcode opcode
					       :displacement (encode-integer offset type)
					       extras)))))
		    (assert (= code-size (length code)))
		    (append extra-prefixes code))))))))))

(defmacro pc-rel (opcode operand type &optional (mode 'operator-mode) &rest extras)
  `(progn
     (assembler
      (return-when (encode-pc-rel operator legacy-prefixes ,opcode ,operand ',type ,@extras)))
     (disassembler
      (define-disassembler (operator ,opcode ,mode)
	  decode-pc-rel
	',type))))

(defmacro modrm (operand opcode digit)
  `(progn
     (assembler
      (when (typep ,operand '(or register-operand indirect-operand))
	(return-values-when
	 (merge-encodings (encoded-values :opcode ,opcode
					  :reg ,digit
					  :operand-size operator-mode
					  :rex default-rex)
			  (encode-reg/mem ,operand operator-mode)))))
     (disassembler
      (define-disassembler (operator ,opcode operator-mode ,digit) decode-modrm))))

(defun encode-reg-modrm (operator legacy-prefixes op-reg op-modrm opcode operator-mode default-rex &optional reg/mem-mode &rest extras)
  (let* ((reg-map (ecase operator-mode
		    (:8-bit '(:al :cl :dl :bl :ah :ch :dh :bh))
		    (:16-bit '(:ax :cx :dx :bx :sp :bp :si :di))
		    (:32-bit '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
		    (:64-bit '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :r13 :r14 :r15))
		    (:mm '(:mm0 :mm1 :mm2 :mm3 :mm4 :mm5 :mm6 :mm7 :mm8))
		    (:xmm '(:xmm0 :xmm1 :xmm2 :xmm3 :xmm4 :xmm5 :xmm6 :xmm7))))
	 (reg-index (position op-reg reg-map)))
    (when reg-index
      (encode (merge-encodings (apply #'encoded-values
				      :opcode opcode
				      :reg reg-index
				      :operand-size operator-mode
				      :rex default-rex
				      extras)
			       (encode-reg/mem op-modrm (or reg/mem-mode operator-mode)))))))

(defmacro reg-modrm (op-reg op-modrm opcode &optional reg/mem-mode &rest extras)
  `(progn
     (assembler
      (return-when (encode-reg-modrm operator legacy-prefixes ,op-reg ,op-modrm ,opcode
				     operator-mode default-rex ,reg/mem-mode ,@extras)))
     (disassembler
      (define-disassembler (operator ,opcode operator-mode)
	  decode-reg-modrm
	(operand-ordering operand-formals
			  :reg ',op-reg
			  :modrm ',op-modrm)))))

(defun encode-reg-cr (operator legacy-prefixes op-reg op-cr opcode operator-mode default-rex &rest extras)
  (let* ((reg-map (ecase operator-mode
		    (:32-bit '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
		    (:64-bit '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :r13 :r14 :r15))))
	 (reg-index (position op-reg reg-map))
	 (cr-index (position op-cr '(:cr0 :cr1 :cr2 :cr3 :cr4 :cr5 :cr6 :cr7))))
    (when (and reg-index
	       cr-index)
      (encode (apply #'encoded-values
		     :opcode opcode
		     :mod #b11
		     :rm reg-index
		     :reg cr-index
		     :operand-size (if (not (eq *cpu-mode* :64-bit))
				       nil
				       operator-mode)
		     :rex default-rex
		     extras)))))

(defmacro reg-cr (op-reg op-cr opcode &rest extras)
  `(progn
     (assembler
      (return-when (encode-reg-cr operator legacy-prefixes ,op-reg ,op-cr ,opcode operator-mode default-rex ,@extras)))
     (disassembler
      (define-disassembler (operator ,opcode nil nil nil :32-bit)
	  decode-reg-cr
	(operand-ordering operand-formals
			  :reg ',op-reg
			  :cr ',op-cr)))))

(defmacro sreg-modrm (op-sreg op-modrm opcode &rest extras)
  `(progn
     (assembler
      (let* ((reg-map '(:es :cs :ss :ds :fs :gs))
	     (reg-index (position ,op-sreg reg-map)))
	(when reg-index
	  (return-values-when
	   (merge-encodings (encoded-values :opcode ,opcode
					    :reg reg-index
					    :rex default-rex
					    ,@extras)
			    (encode-reg/mem ,op-modrm operator-mode))))))
     (disassembler
      (define-disassembler (operator ,opcode nil nil nil :16-bit)
	  decode-reg-modrm
	(operand-ordering operand-formals
			  :reg ',op-sreg
			  :modrm ',op-modrm)
	:segment))))

(defmacro moffset (opcode op-offset type fixed-operand)
  `(progn
     (assembler
      (when (and ,@(when fixed-operand
			 `((eql ,@fixed-operand)))
		 (indirect-operand-p ,op-offset))
	(multiple-value-bind (reg offsets reg2)
	    (parse-indirect-operand ,op-offset)
	  (when (and (not reg)
		     (not reg2))
	    (return-values-when
	     (encoded-values :opcode ,opcode
			     :displacement (encode-integer (reduce #'+ offsets
								   :key #'resolve-operand)
							   ',type)))))))
     (disassembler
      (define-disassembler (operator ,opcode operator-mode)
	  decode-moffset
	',type
	(operand-ordering operand-formals
			  :moffset ',op-offset
			  :fixed ',(first fixed-operand))
	',(second fixed-operand)))))



(defmacro opcode (opcode &optional fixed-operand fixed-operand2 &rest extras)
  `(progn
     (assembler
      (when (and ,@(when fixed-operand
			 `((eql ,@fixed-operand)))
		 ,@(when fixed-operand2
			 `((eql ,@fixed-operand2))))
	(return-values-when
	 (encoded-values :opcode ,opcode
			 ,@extras
			 :operand-size operator-mode))))
     (disassembler
      (define-disassembler (operator ,opcode)
	  decode-no-operands
	,(second fixed-operand)
	,(second fixed-operand2)))))

(defmacro opcode* (opcode &rest extras)
  `(return-values-when
    (encoded-values :opcode ,opcode
                     ,@extras)))

(defun encode-opcode-reg (operator legacy-prefixes opcode op-reg operator-mode default-rex)
  (let* ((reg-map (ecase operator-mode
		    (:8-bit '(:al :cl :dl :bl :ah :ch :dh :bh))
		    (:16-bit '(:ax :cx :dx :bx :sp :bp :si :di))
		    (:32-bit '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
		    (:64-bit '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :r13 :r14 :r15))
		    (:mm '(:mm0 :mm1 :mm2 :mm3 :mm4 :mm5 :mm6 :mm7 :mm8))
		    (:xmm '(:xmm0 :xmm1 :xmm2 :xmm3 :xmm4 :xmm5 :xmm6 :xmm7))))
	 (reg-index (position op-reg reg-map)))
    (when reg-index
      (encode (encoded-values :opcode (+ opcode (ldb (byte 3 0) reg-index))
			      :operand-size operator-mode
			      :rex (cond
				     ((>= reg-index 8)
				      (assert (eq :64-bit operator-mode))
				      '(:rex.w :rex.r))
				     (t default-rex)))))))

(defmacro opcode-reg (opcode op-reg &optional extra-operand)
  `(progn
     (assembler
      (when (and ,@(when extra-operand
			 `((eql ,@extra-operand))))
	(return-when
	 (encode-opcode-reg operator legacy-prefixes ,opcode ,op-reg operator-mode default-rex))))
     (disassembler
      (loop for reg from #b000 to #b111
	 do ,(if (not extra-operand)
		 `(define-disassembler (operator (logior ,opcode reg) operator-mode)
		      decode-opcode-reg
		    '(:reg)
		    nil)
		 `(define-disassembler (operator (logior ,opcode reg) operator-mode)
		      decode-opcode-reg
		    (operand-ordering operand-formals
				      :reg ',op-reg
				      :extra ',(first extra-operand))
		    ',(second extra-operand)))))))

(defun encode-opcode-reg-imm (operator legacy-prefixes opcode op-reg op-imm type operator-mode default-rex)
  (when (immediate-p op-imm)
    (let ((immediate (resolve-operand op-imm)))
      (when (typep immediate type)
	(let* ((reg-map (ecase operator-mode
			  (:8-bit '(:al :cl :dl :bl :ah :ch :dh :bh))
			  (:16-bit '(:ax :cx :dx :bx :sp :bp :si :di))
			  (:32-bit '(:eax :ecx :edx :ebx :esp :ebp :esi :edi))
			  (:64-bit '(:rax :rcx :rdx :rbx :rsp :rbp :rsi :rdi :r8 :r9 :r10 :r11 :r12 :r13 :r14 :r15))
			  (:mm '(:mm0 :mm1 :mm2 :mm3 :mm4 :mm5 :mm6 :mm7 :mm8))
			  (:xmm '(:xmm0 :xmm1 :xmm2 :xmm3 :xmm4 :xmm5 :xmm6 :xmm7))))
	       (reg-index (position op-reg reg-map)))
	  (when reg-index
	    (encode (encoded-values :opcode (+ opcode (ldb (byte 3 0) reg-index))
				    :operand-size operator-mode
				    :immediate (encode-integer immediate type)
				    :rex (cond
					   ((>= reg-index 8)
					    (assert (eq :64-bit operator-mode))
					    '(:rex.w :rex.r))
					   (t default-rex))))))))))

(defmacro opcode-reg-imm (opcode op-reg op-imm type)
  `(progn
     (assembler
      (return-when
       (encode-opcode-reg-imm operator legacy-prefixes ,opcode ,op-reg ,op-imm ',type operator-mode default-rex)))
     (disassembler
      (loop for reg from #b000 to #b111
	 do (define-disassembler (operator (logior ,opcode reg) operator-mode)
		decode-opcode-reg-imm
	      (operand-ordering operand-formals
				:reg ',op-reg
				:imm ',op-imm)
	      ',type)))))

(defmacro far-pointer (opcode segment offset offset-type &optional mode &rest extra)
  `(progn
     (assembler
      (when (and (immediate-p ,segment)
		 (indirect-operand-p ,offset)) ; FIXME: should be immediate-p, change in bootblock.lisp.
	(let ((segment (resolve-operand ,segment))
	      (offset (resolve-operand (car ,offset))))
	  (when (and (typep segment '(uint 16))
		     (typep offset ',offset-type))
	    (return-when (encode (encoded-values :opcode ,opcode
						 :immediate (append (encode-integer offset ',offset-type)
								    (encode-integer segment '(uint 16)))
						 ,@extra)))))))
     (disassembler
      (define-disassembler (operator ,opcode ,(or mode 'operator-mode))
	  decode-far-pointer
	',offset-type))))


;;;;;;;;;;; Pseudo-instructions

(define-operator/none :% (op &rest form)
  (case op
    (:bytes
     (return-from operator
       (destructuring-bind (byte-size &rest data)
	   form
	 (loop for datum in data
	    append (loop for b from 0 below byte-size by 8
		      collect (ldb (byte 8 b)
				   (resolve-operand datum)))))))
    (:funcall
     (return-from operator
       (destructuring-bind (function &rest args)
	   form
	 (apply function (mapcar #'resolve-operand args)))))
    (:fun
     (return-from operator
       (destructuring-bind (function &rest args)
	   (car form)
	 (loop for cbyte in (apply function (mapcar #'resolve-operand args))
	    append (loop for octet from 0 below (imagpart cbyte)
		      collect (ldb (byte 8 (* 8 octet))
				   (realpart cbyte)))))))
    (:format
     (return-from operator
       (destructuring-bind (byte-size format-control &rest format-args)
	   form
	 (ecase byte-size
	   (8 (let ((data (map 'list #'char-code
			       (apply #'format nil format-control
				      (mapcar #'resolve-operand format-args)))))
		(cons (length data)
		      data)))))))
    (:align
     (return-from operator
       (destructuring-bind (alignment)
	   form
	 (let* ((offset (mod *pc* alignment)))
	   (when (plusp offset)
	     (make-list (- alignment offset)
			:initial-element 0))))))))

;;;;;;;;;;; ADC

(define-operator/8 :adcb (src dst)
  (imm src #x14 (xint 8) (dst :al))
  (imm-modrm src dst #x80 2 (xint 8))
  (reg-modrm dst src #x12)
  (reg-modrm src dst #x10))

(define-operator* (:16 :adcw :32 :adcl :64 :adcr) (src dst)
  (imm-modrm src dst #x83 2 (sint 8))
  (imm src #x15 :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm src dst #x81 2 :int-16-32-64)
  (reg-modrm dst src #x13)
  (reg-modrm src dst #x11))

;;;;;;;;;;; ADD

(define-operator/8 :addb (src dst)
  (imm src #x04 (xint 8) (dst :al))
  (imm-modrm src dst #x80 0 (xint 8))
  (reg-modrm dst src #x02)
  (reg-modrm src dst #x00))

(define-operator* (:16 :addw :32 :addl :64 :addr) (src dst)
  (imm-modrm src dst #x83 0 (sint 8))
  (imm src #x05 :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm src dst #x81 0 :int-16-32-64)
  (reg-modrm dst src #x03)
  (reg-modrm src dst #x01))

;;;;;;;;;;; AND

(define-operator/8 :andb (mask dst)
  (imm mask #x24 (xint 8) (dst :al))
  (imm-modrm mask dst #x80 4 (xint 8))
  (reg-modrm dst mask #x22)
  (reg-modrm mask dst #x20))

(define-operator* (:16 :andw :32 :andl :64 :andr) (mask dst)
  (imm-modrm mask dst #x83 4 (sint 8))
  (imm mask #x25 :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm mask dst #x81 4 :int-16-32-64)
  (reg-modrm dst mask #x23)
  (reg-modrm mask dst #x21))

;;;;;;;;;;; BOUND, BSF, BSR, BSWAP

(define-operator* (:16 :boundw :32 :bound) (bounds reg)
  (reg-modrm reg bounds #x62))

(define-operator* (:16 :bsfw :32 :bsfl :64 :bsfr) (src dst)
  (reg-modrm dst src #x0fbc))

(define-operator* (:16 :bsrw :32 :bsrl :64 :bsrr) (src dst)
  (reg-modrm dst src #x0fbd))

(define-operator* (:32 :bswap :64 :bswapr) (dst)
  (opcode-reg #x0fc8 dst))

;;;;;;;;;;; BT, BTC, BTR, BTS

(define-operator* (:16 :btw :32 :btl :64 :btr) (bit src)
  (imm-modrm bit src #x0fba 4 (uint 8))
  (reg-modrm bit src #x0fa3))

(define-operator* (:16 :btcw :32 :btcl :64 :btcr) (bit src)
  (imm-modrm bit src #x0fba 7 (uint 8))
  (reg-modrm bit src #x0fbb))

(define-operator* (:16 :btrw :32 :btrl :64 :btrr) (bit src)
  (imm-modrm bit src #x0fba 6 (uint 8))
  (reg-modrm bit src #x0fb3))

(define-operator* (:16 :btsw :32 :btsl :64 :btsr) (bit src)
  (imm-modrm bit src #x0fba 5 (uint 8))
  (reg-modrm bit src #x0fab))

;;;;;;;;;;; CALL

(define-operator/16 :callw (dest)
  (pc-rel #xe8 dest (sint 16))
  (modrm dest #xff 2))

(define-operator/32 :call (dest)
  (pc-rel #xe8 dest (sint 32))
  (modrm dest #xff 2))

(define-operator/none :call-segment (dest)
  (modrm dest #xff 3))

;;;;;;;;;;; CLC, CLD, CLI, CLTS, CMC

(define-operator/none :clc () (opcode #xf8))
(define-operator/none :cld () (opcode #xfc))
(define-operator/none :cli () (opcode #xfa))
(define-operator/none :clts () (opcode #x0f06))
(define-operator/none :cmc () (opcode #xf5))

;;;;;;;;;;; CMOVcc

(define-operator* (:16 :cmovaw :32 :cmova :64 :cmovar) (src dst)
  (reg-modrm dst src #x0f47)) ; Move if above, CF=0 and ZF=0.

(define-operator* (:16 :cmovaew :32 :cmovae :64 :cmovaer) (src dst)
  (reg-modrm dst src #x0f43)) ; Move if above or equal, CF=0.

(define-operator* (:16 :cmovbw :32 :cmovb :64 :cmovbr) (src dst)
  (reg-modrm dst src #x0f42)) ; Move if below, CF=1.

(define-operator* (:16 :cmovbew :32 :cmovbe :64 :cmovber) (src dst)
  (reg-modrm dst src #x0f46)) ; Move if below or  equal, CF=1 or ZF=1.

(define-operator* (:16 :cmovcw :32 :cmovc :64 :cmovcr) (src dst)
  (reg-modrm dst src #x0f42)) ; Move if carry, CF=1.

(define-operator* (:16 :cmovew :32 :cmove :64 :cmover) (src dst)
  (reg-modrm dst src #x0f44)) ; Move if equal, ZF=1.

(define-operator* (:16 :cmovgw :32 :cmovg :64 :cmovgr) (src dst)
  (reg-modrm dst src #x0f4f)) ; Move if greater, ZF=0 and SF=OF.

(define-operator* (:16 :cmovgew :32 :cmovge :64 :cmovger) (src dst)
  (reg-modrm dst src #x0f4d)) ; Move if greater or equal, SF=OF.

(define-operator* (:16 :cmovlw :32 :cmovl :64 :cmovlr) (src dst)
  (reg-modrm dst src #x0f4c))

(define-operator* (:16 :cmovlew :32 :cmovle :64 :cmovler) (src dst)
  (reg-modrm dst src #x0f4e)) ; Move if less or equal, ZF=1 or SF/=OF.

(define-operator* (:16 :cmovnaw :32 :cmovna :64 :cmovnar) (src dst)
  (reg-modrm dst src #x0f46)) ; Move if not above, CF=1 or ZF=1.

(define-operator* (:16 :cmovnaew :32 :cmovnae :64 :cmovnaer) (src dst)
  (reg-modrm dst src #x0f42)) ; Move if not above or equal, CF=1.

(define-operator* (:16 :cmovnbw :32 :cmovnb :64 :cmovnbr) (src dst)
  (reg-modrm dst src #x0f43)) ; Move if not below, CF=0.

(define-operator* (:16 :cmovnbew :32 :cmovnbe :64 :cmovnber) (src dst)
  (reg-modrm dst src #x0f47)) ; Move if not below or equal, CF=0 and ZF=0.

(define-operator* (:16 :cmovncw :32 :cmovnc :64 :cmovncr) (src dst)
  (reg-modrm dst src #x0f43)) ; Move if not carry, CF=0.

(define-operator* (:16 :cmovnew :32 :cmovne :64 :cmovner) (src dst)
  (reg-modrm dst src #x0f45)) ; Move if not equal, ZF=0.

(define-operator* (:16 :cmovngew :32 :cmovnge :64 :cmovnger) (src dst)
  (reg-modrm dst src #x0f4c)) ; Move if not greater or equal, SF/=OF.

(define-operator* (:16 :cmovnlw :32 :cmovnl :64 :cmovnlr) (src dst)
  (reg-modrm dst src #x0f4d)) ; Move if not less SF=OF.

(define-operator* (:16 :cmovnlew :32 :cmovnle :64 :cmovnler) (src dst)
  (reg-modrm dst src #x0f4f)) ; Move if not less or equal, ZF=0 and SF=OF.

(define-operator* (:16 :cmovnow :32 :cmovno :64 :cmovnor) (src dst)
  (reg-modrm dst src #x0f41)) ; Move if not overflow, OF=0.

(define-operator* (:16 :cmovnpw :32 :cmovnp :64 :cmovnpr) (src dst)
  (reg-modrm dst src #x0f4b)) ; Move if not parity, PF=0.

(define-operator* (:16 :cmovnsw :32 :cmovns :64 :cmovnsr) (src dst)
  (reg-modrm dst src #x0f49)) ; Move if not sign, SF=0.

(define-operator* (:16 :cmovnzw :32 :cmovnz :64 :cmovnzr) (src dst)
  (reg-modrm dst src #x0f45)) ; Move if not zero, ZF=0.

(define-operator* (:16 :cmovow :32 :cmovo :64 :cmovor) (src dst)
  (reg-modrm dst src #x0f40)) ; Move if overflow, OF=1.

(define-operator* (:16 :cmovpw :32 :cmovp :64 :cmovpr) (src dst)
  (reg-modrm dst src #x0f4a)) ; Move if parity, PF=1.

(define-operator* (:16 :cmovsw :32 :cmovs :64 :cmovsr) (src dst)
  (reg-modrm dst src #x0f48)) ; Move if sign, SF=1

(define-operator* (:16 :cmovzw :32 :cmovz :64 :cmovzr) (src dst)
  (reg-modrm dst src #x0f44)) ; Move if zero, ZF=1

;;;;;;;;;;; CMP

(define-operator/8 :cmpb (src dst)
  (imm src #x3c (xint 8) (dst :al))
  (imm-modrm src dst #x80 7 (xint 8))
  (reg-modrm dst src #x3a)
  (reg-modrm src dst #x38))

(define-operator* (:16 :cmpw :32 :cmpl :64 :cmpr) (src dst)
  (imm-modrm src dst #x83 7 (sint 8))
  (imm src #x3d :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm src dst #x81 7 :int-16-32-64)
  (reg-modrm dst src #x3b)
  (reg-modrm src dst #x39))

;;;;;;;;;;; CMPXCHG

(define-operator/8 :cmpxchgb (cmp-reg cmp-modrm al-dst)
  (when (eq al-dst :al)
    (reg-modrm cmp-reg cmp-modrm #x0fb0)))

(define-operator* (:16 :cmpxchgw :32 :cmpxchgl :64 :cmpxchgr) (cmp-reg cmp-modrm al-dst)
  (when (eq al-dst :ax-eax-rax)
    (reg-modrm cmp-reg cmp-modrm #x0fb1)))

;;;;;;;;;;; CMPXCHG8B, CMPXCHG16B

(define-operator/32 :cmpxchg8b (address)
  (modrm address #x0fc7 1))

(define-operator/64 :cmpxchg16b (address)
  (modrm address #x0fc7 1))

;;;;;;;;;;; CPUID

(define-operator/none :cpuid ()
  (opcode* #x0fa2))

;;;;;;;;;;; CWD, CDQ

(define-operator/16 :cwd (reg1 reg2)
  (when (and (eq reg1 :ax)
	     (eq reg2 :dx))
    (opcode #x99)))

(define-operator/32 :cdq (reg1 reg2)
  (when (and (eq reg1 :eax)
		 (eq reg2 :edx))
    (opcode #x99)))

(define-operator/64 :cqo (reg1 reg2)
  (when (and (eq reg1 :rax)
		 (eq reg2 :rdx))
    (opcode #x99)))

;;;;;;;;;;; DEC

(define-operator/8 :decb (dst)
  (modrm dst #xfe 1))

(define-operator* (:16 :decw :32 :decl) (dst)
  (unless (eq *cpu-mode* :64-bit)
    (opcode-reg #x48 dst))
  (modrm dst #xff 1))

(define-operator* (:64 :decr) (dst)
  (modrm dst #xff 1))
    
;;;;;;;;;;; DIV

(define-operator/8 :divb (divisor dividend)
  (when (eq dividend :ax)
    (modrm divisor #xf6 6)))

(define-operator* (:16 :divw :32 :divl :64 :divr) (divisor dividend1 dividend2)
  (when (and (eq dividend1 :ax-eax-rax)
	     (eq dividend2 :dx-edx-rdx))
    (modrm divisor #xf7 6)))

;;;;;;;;;;; HLT

(define-operator/none :halt ()
  (opcode #xf4))

;;;;;;;;;;; IDIV

(define-operator/8 :idivb (divisor dividend1 dividend2)
  (when (and (eq dividend1 :al)
	     (eq dividend2 :ah))
    (modrm divisor #xf6 7)))

(define-operator* (:16 :idivw :32 :idivl :64 :idivr) (divisor dividend1 dividend2)
  (when (and (eq dividend1 :ax-eax-rax)
		 (eq dividend2 :dx-edx-rdx))
    (modrm divisor #xf7 7)))

;;;;;;;;;;; IMUL

(define-operator/32 :imull (factor product1 &optional product2)
  (when (not product2)
    (reg-modrm product1 factor #x0faf))
  (when (and (eq product1 :eax)
	     (eq product2 :edx))
    (modrm factor #xf7 5))
  (typecase factor
    ((sint 8)
     (reg-modrm product1 product2 #x6b
		nil
		:displacement (encode-integer factor '(sint 8))))
    ((sint 32)
     (reg-modrm product1 product2 #x69
		nil
		:displacement (encode-integer factor '(sint 32))))))

;;;;;;;;;;; IN

(define-operator/8 :inb (port dst)
  (opcode #xec (port :dx) (dst :al))
  (imm port #xe4 (uint 8) (dst :al)))

(define-operator/16 :inw (port dst)
  (opcode #xed (port :dx) (dst :ax))
  (imm port #xe5 (uint 8) (dst :ax)))

(define-operator/32 :inl (port dst)
  (opcode #xed (port :dx) (dst :eax))
  (imm port #xe5 (uint 8) (dst :eax)))

;;;;;;;;;;; INC

(define-operator/8 :incb (dst)
  (modrm dst #xfe 0))

(define-operator* (:16 :incw :32 :incl) (dst)
  (unless (eq *cpu-mode* :64-bit)
    (opcode-reg #x40 dst))
  (modrm dst #xff 0))

(define-operator* (:64 :incr) (dst)
  (modrm dst #xff 0))

;;;;;;;;;;; INT

(define-operator/none :break ()
  (opcode #xcc))

(define-operator/none :int (vector)
  (imm vector #xcd (uint 8)))

(define-operator/none :into ()
  (opcode #xce))

;;;;;;;;;;; INVLPG

(define-operator/none :invlpg (address)
  (modrm address #x0f01 7))

;;;;;;;;;;; IRET

(define-operator* (:16 :iret :32 :iretd :64 :iretq) ()
  (opcode #xcf () ()
	  :rex default-rex))

;;;;;;;;;;; Jcc

(defmacro define-jcc (name opcode1 &optional (opcode2 (+ #x0f10 opcode1)))
 `(define-operator/none ,name (dst)
    (pc-rel ,opcode1 dst (sint 8))
    (when (or (and (eq *cpu-mode* :32-bit)
		   *use-jcc-16-bit-p*)
	      (eq *cpu-mode* :16-bit))
      (pc-rel ,opcode2 dst (sint 16) nil
	      :operand-size :16-bit))
    (pc-rel ,opcode2 dst (sint 32) nil
	    :operand-size (case *cpu-mode*
			    ((:16-bit :32-bit)
			     :32-bit)))))

(define-jcc :ja #x77)
(define-jcc :jae #x73)
(define-jcc :jb #x72)
(define-jcc :jbe #x76)
(define-jcc :jc #x72)
(define-jcc :jecx #xe3)
(define-jcc :je #x74)
(define-jcc :jg #x7f)
(define-jcc :jge #x7d)
(define-jcc :jl #x7c)
(define-jcc :jle #x7e)
(define-jcc :jna #x76)
(define-jcc :jnae #x72)
(define-jcc :jnb #x73)
(define-jcc :jnbe #x77)
(define-jcc :jnc #x73)
(define-jcc :jne #x75)
(define-jcc :jng #x7e)
(define-jcc :jnge #x7c)
(define-jcc :jnl #x7d)
(define-jcc :jnle #x7f)
(define-jcc :jno #x71)
(define-jcc :jnp #x7b)
(define-jcc :jns #x79)
(define-jcc :jnz #x75)
(define-jcc :jo #x70)
(define-jcc :jp #x7a)
(define-jcc :jpe #x7a)
(define-jcc :jpo #x7b)
(define-jcc :js #x78)
(define-jcc :jz #x74)

(define-operator* (:16 :jcxz :32 :jecxz :64 :jrcxz) (dst)
  (pc-rel #xe3 dst (sint 8) nil
	  :operand-size operator-mode
	  :rex default-rex))
  
;;;;;;;;;;; JMP

(define-operator/none :jmp (seg-dst &optional dst)
  (cond
    (dst
     (when (eq *cpu-mode* :16-bit)
       (far-pointer #xea seg-dst dst (uint 16) :16-bit))
     (when (eq *cpu-mode* :32-bit)
       (far-pointer #xea seg-dst dst (xint 32) :32-bit)))
    (t (let ((dst seg-dst))
	 (pc-rel #xeb dst (sint 8))
	 (when (or (and (eq *cpu-mode* :32-bit)
			*use-jcc-16-bit-p*)
		   (eq *cpu-mode* :16-bit))
	   (pc-rel #xe9 dst (sint 16) :16-bit))
	 (pc-rel #xe9 dst (sint 32) :32-bit)
	 (when (or (not *position-independent-p*)
		   (indirect-operand-p dst))
	   (let ((operator-mode :32-bit))
	     (modrm dst #xff 4)))))))

(define-operator* (:16 :jmpw-segment :32 :jmp-segment :64 :jmpr-segment) (addr)
  (modrm addr #xff 5))

;;;;;;;;;;; LAHF, LAR

(define-operator/none :lahf ()
  (case *cpu-mode*
    ((:16-bit :32-bit)
     (opcode #x9f))))

(define-operator* (:16 :larw :32 :larl :64 :larr) (src dst)
  (reg-modrm dst src #x0f02))

;;;;;;;;;;; LEA

(define-operator* (:16 :leaw :32 :leal :64 :lear) (addr dst)
  (reg-modrm dst addr #x8d))

;;;;;;;;;;; LEAVE

(define-operator/none :leave ()
  (opcode #xc9))

;;;;;;;;;;; LFENCE

(define-operator/none :lfence ()
  (opcode #x0faee8))

;;;;;;;;;;; LGDT, LIDT

(define-operator* (:16 :lgdtw :32 :lgdtl :64 :lgdtr :dispatch :lgdt) (addr)
  (when (eq operator-mode *cpu-mode*)
    (modrm addr #x0f01 2)))

(define-operator* (:16 :lidtw :32 :lidt :64 :lidtr) (addr)
  (modrm addr #x0f01 3))

;;;;;;;;;;; LMSW

(define-operator/16 :lmsw (src)
  (modrm src #x0f01 6))

;;;;;;;;;;; LODS

(define-operator/8 :lodsb ()
  (opcode #xac))

(define-operator* (:16 :lodsw :32 :lodsl :64 :lodsr) ()
  (opcode #xad))

;;;;;;;;;;; LOOP, LOOPE, LOOPNE

(define-operator/none :loop (dst)
  (pc-rel #xe2 dst (sint 8)))

(define-operator/none :loope (dst)
  (pc-rel #xe1 dst (sint 8)))

(define-operator/none :loopne (dst)
  (pc-rel #xe0 dst (sint 8)))

;;;;;;;;;;; MOV

(define-operator/8 :movb (src dst)
  (moffset #xa2 dst (uint 8) (src :al))
  (moffset #xa0 src (uint 8) (dst :al))
  (opcode-reg-imm #xb0 dst src (xint 8))
  (imm-modrm src dst #xc6 0 (xint 8))
  (reg-modrm dst src #x8a)
  (reg-modrm src dst #x88))

(define-operator/16 :movw (src dst)
  (moffset #xa3 dst (uint 16) (src :ax))
  (moffset #xa0 src (uint 16) (dst :ax))
  (opcode-reg-imm #xb8 dst src (xint 16))
  (imm-modrm src dst #xc7 0 (xint 16))
  (sreg-modrm src dst #x8c)
  (sreg-modrm dst src #x8e)
  (reg-modrm dst src #x8b)
  (reg-modrm src dst #x89))

(define-operator/32 :movl (src dst)
  (moffset #xa3 dst (uint 32) (src :eax))
  (moffset #xa0 src (uint 32) (dst :eax))
  (opcode-reg-imm #xb8 dst src (xint 32))
  (imm-modrm src dst #xc7 0 (xint 32))
  (reg-modrm dst src #x8b)
  (reg-modrm src dst #x89))

;;;;;;;;;;; MOVCR

(define-operator* (:32 :movcrl :dispatch :movcr) (src dst)
  (reg-cr src dst #x0f22)
  (reg-cr dst src #x0f20))

;;;;;;;;;;; MOVS

(define-operator/8 :movsb ()
  (opcode #xa4))

(define-operator/16 :movsw ()
  (opcode #xa5))

(define-operator/32 :movsl ()
  (opcode #xa5))

;;;;;;;;;;; MOVSX

(define-operator* (:32 :movsxb) (src dst)
  (reg-modrm dst src #x0fbe))

(define-operator* (:32 :movsxw) (src dst)
  (reg-modrm dst src #x0fbf))

;;;;;;;;;;; MOVZX

(define-operator* (:16 :movzxbw :32 :movzxbl :dispatch :movzxb) (src dst)
  (reg-modrm dst src #x0fb6 :8-bit))

(define-operator* (:32 :movzxw) (src dst)
  (reg-modrm dst src #x0fb7))

;;;;;;;;;;; MUL

(define-operator/32 :mull (factor product1 &optional product2)
  (when (and (eq product1 :eax)
	     (eq product2 :edx))
    (modrm factor #xf7 4)))

;;;;;;;;;;; NEG

(define-operator/8 :negb (dst)
  (modrm dst #xf6 3))

(define-operator* (:16 :negw :32 :negl :64 :negr) (dst)
  (modrm dst #xf7 3))

;;;;;;;;;;; NOT

(define-operator/8 :notb (dst)
  (modrm dst #xf6 2))

(define-operator* (:16 :notw :32 :notl :64 :notr) (dst)
  (modrm dst #xf7 2))

;;;;;;;;;;; OR

(define-operator/8 :orb (src dst)
  (imm src #x0c (xint 8) (dst :al))
  (imm-modrm src dst #x80 1 (xint 8))
  (reg-modrm dst src #x0a)
  (reg-modrm src dst #x08))

(define-operator* (:16 :orw :32 :orl :64 :orr) (src dst)
  (imm-modrm src dst #x83 1 (sint 8))
  (imm src #x0d :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm src dst #x81 1 :int-16-32-64)
  (reg-modrm dst src #x0b)
  (reg-modrm src dst #x09))

;;;;;;;;;;; OUT

(define-operator/8 :outb (src port)
  (opcode #xee (src :al) (port :dx))
  (imm port #xe6 (uint 8) (src :al)))

(define-operator/16 :outw (src port)
  (opcode #xef (src :ax) (port :dx))
  (imm port #xe7 (uint 8) (src :ax)))

(define-operator/32 :outl (src port)
  (opcode #xef (src :eax) (port :dx))
  (imm port #xe7 (uint 8) (src :eax)))

;;;;;;;;;;; POP

(define-operator* (:16 :popw :32 :popl) (dst)
  (opcode #x1f (dst :ds))
  (opcode #x07 (dst :es))
  (opcode #x17 (dst :ss))
  (opcode #x0fa1 (dst :fs))
  (opcode #x0fa9 (dst :gs))
  (opcode-reg #x58 dst)
  (modrm dst #x8f 0))

(define-operator/64* :popr (dst)
  (opcode-reg #x58 dst)
  (modrm dst #x8f 0))

;;;;;;;;;;; POPF

(define-operator* (:16 :popfw :32 :popfl :64 :popfr) ()
  (opcode #x9d))

;;;;;;;;;;; PRFETCH

(define-operator/none :prefetch-nta (m8)
  (modrm m8 #x0f18 0))

(define-operator/none :prefetch-t0 (m8)
  (modrm m8 #x0f18 1))

(define-operator/none :prefetch-t1 (m8)
  (modrm m8 #x0f18 2))

(define-operator/none :prefetch-t2 (m8)
  (modrm m8 #x0f18 3))

;;;;;;;;;;; PUSH

(define-operator* (:16 :pushw :32 :pushl) (src)
  (opcode #x0e (src :cs))
  (opcode #x16 (src :ss))
  (opcode #x1e (src :ds))
  (opcode #x06 (src :es))
  (opcode #x0fa0 (src :fs))
  (opcode #x0fa8 (src :gs))
  (opcode-reg #x50 src)
  (imm src #x6a (sint 8))
  (imm src #x68 :int-16-32-64 () :operand-size operator-mode)
  (modrm src #xff 6))

(define-operator/64* :pushr (src)
  (opcode-reg #x50 src)
  (imm src #x6a (sint 8))
  (imm src #x68 (sint 16) () :operand-size :16-bit)
  (imm src #x68 (sint 32))
  (modrm src #xff 6))

;;;;;;;;;;; PUSHF

(define-operator* (:16 :pushfw :32 :pushfl :64 :pushfr) ()
  (opcode #x9c))

;;;;;;;;;;; RDMSR

(define-operator/none :rdmsr ()
  (opcode #x0f32))

;;;;;;;;;;; RDTSC

(define-operator/none :rdtsc ()
  (opcode #x0f31))

;;;;;;;;;;; RET

(define-operator/none :ret ()
  (opcode #xc3))

;;;;;;;;;;; SAR

(define-operator/8 :sarb (count dst)
  (case count
    (1 (modrm dst #xd0 7))
    (:cl (modrm dst #xd2 7)))
  (imm-modrm count dst #xc0 7 (uint 8)))

(define-operator* (:16 :sarw :32 :sarl :64 :sarr) (count dst)
  (case count
    (1 (modrm dst #xd1 7))
    (:cl (modrm dst #xd3 7)))
  (imm-modrm count dst #xc1 7 (uint 8)))

;;;;;;;;;;; SBB

(define-operator/8 :sbbb (subtrahend dst)
  (imm subtrahend #x1c (xint 8) (dst :al))
  (imm-modrm subtrahend dst #x80 3 (xint 8))
  (reg-modrm dst subtrahend #x1a)
  (reg-modrm subtrahend dst #x18))

(define-operator* (:16 :sbbw :32 :sbbl :64 :sbbr) (subtrahend dst)
  (imm-modrm subtrahend dst #x83 3 (sint 8))
  (imm subtrahend #x1d :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm subtrahend dst #x81 3 :int-16-32-64)
  (reg-modrm dst subtrahend #x1b)
  (reg-modrm subtrahend dst #x19))

;;;;;;;;;;; SGDT

(define-operator/8 :sgdt (addr)
  (modrm addr #x0f01 0))

;;;;;;;;;;; SHL

(define-operator/8 :shlb (count dst)
  (case count
    (1 (modrm dst #xd0 4))
    (:cl (modrm dst #xd2 4)))
  (imm-modrm count dst #xc0 4 (uint 8)))

(define-operator* (:16 :shlw :32 :shll :64 :shlr) (count dst)
  (case count
    (1 (modrm dst #xd1 4))
    (:cl (modrm dst #xd3 4)))
  (imm-modrm count dst #xc1 4 (uint 8)))

;;;;;;;;;;; SHLD

(define-operator* (:16 :shldw :32 :shldl :64 :shldr) (count dst1 dst2)
  (when (eq :cl count)
    (reg-modrm dst1 dst2 #x0fa5))
  (when (immediate-p count)
    (let ((immediate (resolve-operand count)))
      (when (typep immediate '(uint #x8))
	(reg-modrm dst1 dst2 #x0fa4
		   nil
		   :immediate (encode-integer count '(uint 8)))))))

;;;;;;;;;;; SHR

(define-operator/8 :shrb (count dst)
  (case count
    (1 (modrm dst #xd0 5))
    (:cl (modrm dst #xd2 5)))
  (imm-modrm count dst #xc0 5 (uint 8)))

(define-operator* (:16 :shrw :32 :shrl :64 :shrr) (count dst)
  (case count
    (1 (modrm dst #xd1 5))
    (:cl (modrm dst #xd3 5)))
  (imm-modrm count dst #xc1 5 (uint 8)))

;;;;;;;;;;; SHRD

(define-operator* (:16 :shrdw :32 :shrdl :64 :shrdr) (count dst1 dst2)
  (when (eq :cl count)
    (reg-modrm dst1 dst2 #x0fad))
  (when (immediate-p count)
    (let ((immediate (resolve-operand count)))
      (when (typep immediate '(uint #x8))
	(reg-modrm dst1 dst2 #x0fac
		   nil
		   :immediate (encode-integer count '(uint 8)))))))
    

;;;;;;;;;;; STC, STD, STI

(define-operator/none :stc ()
  (opcode #xf9))

(define-operator/none :std ()
  (opcode #xfd))

(define-operator/none :sti ()
  (opcode #xfb))

;;;;;;;;;;; SUB

(define-operator/8 :subb (subtrahend dst)
  (imm subtrahend #x2c (xint 8) (dst :al))
  (imm-modrm subtrahend dst #x80 5 (xint 8))
  (reg-modrm dst subtrahend #x2a)
  (reg-modrm subtrahend dst #x28))

(define-operator* (:16 :subw :32 :subl :64 :subr) (subtrahend dst)
  (imm-modrm subtrahend dst #x83 5 (sint 8))
  (imm subtrahend #x2d :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm subtrahend dst #x81 5 :int-16-32-64)
  (reg-modrm dst subtrahend #x2b)
  (reg-modrm subtrahend dst #x29))

;;;;;;;;;;; TEST

(define-operator/8 :testb (mask dst)
  (imm mask #xa8 (xint 8) (dst :al))
  (imm-modrm mask dst #xf6 0 (xint 8))
  (reg-modrm mask dst #x84))

(define-operator* (:16 :testw :32 :testl :64 :testr) (mask dst)
  (imm mask #xa9 :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm mask dst #xf7 0 :int-16-32-64)
  (reg-modrm mask dst #x85))

;;;;;;;;;;; WBINVD, WSRMSR

(define-operator/none :wbinvd ()
  (opcode #x0f09))

(define-operator/none :wrmsr ()
  (opcode #x0f30))

;;;;;;;;;;; XCHG

(define-operator/8 :xchgb (x y)
  (reg-modrm y x #x86)
  (reg-modrm x y #x86))

(define-operator* (:16 :xchgw :32 :xchgl :64 :xchgr) (x y)
  (opcode-reg #x90 x (y :ax-eax-rax))
  (opcode-reg #x90 y (x :ax-eax-rax))
  (reg-modrm x y #x87)
  (reg-modrm y x #x87))

;;;;;;;;;;; XOR

(define-operator/8 :xorb (src dst)
  (imm src #x34 (xint 8) (dst :al))
  (imm-modrm src dst #x80 6 (xint 8))
  (reg-modrm dst src #x32)
  (reg-modrm src dst #x30))

(define-operator* (:16 :xorw :32 :xorl :64 :xorr) (src dst)
  (imm-modrm src dst #x83 6 (sint 8))
  (imm src #x35 :int-16-32-64 (dst :ax-eax-rax))
  (imm-modrm src dst #x81 6 :int-16-32-64)
  (reg-modrm dst src #x33)
  (reg-modrm src dst #x31))

;;;;;;;;;;;;;;;; NOP

(define-operator/none :nop ()
  (opcode #x90))

