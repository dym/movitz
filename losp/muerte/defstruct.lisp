;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      defstruct.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Jan 22 13:10:59 2001
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: defstruct.lisp,v 1.21 2008-04-21 19:39:08 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)
(provide :muerte/defstruct)

(in-package muerte)

(defun structure-object-length (object)
  (check-type object structure-object)
  (memref object -4 :type :unsigned-byte14))

(defun structure-object-class (x)
  (memref x -6 :index 1))

(defun copy-structure (object)
  (%shallow-copy-object object (+ 2 (structure-object-length object))))

(defun struct-predicate-prototype (obj)
  "Prototype function for predicates of user-defined struct.
Parameters: struct-name."
  (with-inline-assembly (:returns :boolean-zf=1)
    (:compile-form (:result-mode :eax) obj)
    (:leal (:eax #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jnz 'fail)
    (:cmpb #.(movitz:tag :defstruct) (:eax #.movitz:+other-type-offset+))
    (:jne 'fail)
    (:load-constant struct-class :ebx)
    (:cmpl :ebx (:eax (:offset movitz-struct class)))
    fail))

(defun structure-ref (object slot-number)
  (macrolet
      ((do-it ()
	 `(with-inline-assembly (:returns :eax)
	    ;; type test
	    (:compile-form (:result-mode :eax) object)
	    (:leal (:eax ,(- (movitz:tag :other))) :ecx)
	    (:testb 7 :cl)
	    (:jne '(:sub-program (type-error) (:int 66)))
	    (:cmpb ,(movitz:tag :defstruct) (:eax ,movitz:+other-type-offset+))
	    (:jne '(:sub-program (type-error) (:int 66)))
	    ;; type test passed, read slot
	    ,@(if (= 4 movitz::+movitz-fixnum-factor+)
		  `((:compile-form  (:result-mode :ecx) slot-number)
		    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
		     :movl (:eax :ecx (:offset movitz-struct slot0))
			   :eax))
		`((:compile-form  (:result-mode :untagged-fixnum-ecx) slot-number)
		  (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
		   :movl (:eax (:ecx 4) (:offset movitz-struct slot0)) :eax))))))
    (do-it)))

(defun (setf structure-ref) (value object slot-number)
  (macrolet
      ((do-it ()
	 (assert (= 4 movitz::+movitz-fixnum-factor+))
	 `(with-inline-assembly (:returns :eax)
	    ;; type test
	    (:compile-two-forms (:eax :ebx) object slot-number)
	    (:leal (:eax ,(- (movitz:tag :other))) :ecx)
	    (:testb 7 :cl)
	    (:jne '(:sub-program (type-error) (:int 66)))
	    (:cmpb ,(movitz:tag :defstruct) (:eax ,movitz:+other-type-offset+))
	    (:jne '(:sub-program (type-error) (:int 66)))
	    (:movzxw (:eax (:offset movitz-struct length)) :ecx)
	    (:testb ,movitz::+movitz-fixnum-zmask+ :bl)
	    (:jnz '(:sub-program (not-fixnum) (:movl :ebx :eax) (:int 64)))
	    (:cmpl :ecx :ebx)
	    (:jae '(:sub-program (out-of-range) (:int 65)))
	    ;; type test passed, write slot
	    (:compile-form (:result-mode :edx) value)
	    (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
	     :movl :edx (:eax :ebx (:offset movitz-struct slot0))))))
    (do-it)))

(defun struct-accessor-prototype (object)
  "Parameters: struct-name, slot-number."
  (with-inline-assembly (:returns :eax)
    ;; type test
    (:compile-form (:result-mode :eax) object)
    (:leal (:eax #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jne '(:sub-program (type-error)
            (:load-constant struct-name :edx)
            (:int 59)))
    (:cmpb #.(movitz:tag :defstruct) (:eax #.movitz:+other-type-offset+))
    (:jne 'type-error)
;;     (:load-constant struct-name :ebx)
;;;    (:cmpl :ebx (:eax #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)))
;;;    (:jne '(:sub-program (type-error) (:int 66)))
    ;; type test passed, read slot
    (:load-constant slot-number :ecx)
;;;    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (#.movitz:*compiler-nonlocal-lispval-read-segment-prefix*
     :movl (:eax (:ecx 1) #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0))
	   :eax)))

(defun (setf struct-accessor-prototype) (value obj)
  "Parameters: struct-name, slot-number."
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) value obj)
    ;; type test
    (:leal (:ebx #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jnz '(:sub-program (type-error)
            (:load-constant struct-name :edx)
            (:movl :ebx :eax)
            (:int 59)))
    (:cmpb #.(movitz:tag :defstruct) (:ebx #.movitz:+other-type-offset+))
    (:jne 'type-error)
;;     (:cmpl :edx (:ebx (:offset movitz-struct name)))
;;     (:jne 'type-error)
    ;; type test passed, write slot
    (:load-constant slot-number :ecx)
;;;    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (#.movitz:*compiler-nonlocal-lispval-write-segment-prefix*
     :movl :eax (:ebx (:ecx 1) #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0)))))

(defun list-struct-accessor-prototype (s)
  (nth 'slot-number s))

(defun (setf list-struct-accessor-prototype) (value s)
  (setf (nth 'slot-number s) value))

(defmacro/cross-compilation defstruct (name-and-options &optional documentation &rest slot-descriptions)
  (unless (stringp documentation)
    (push documentation slot-descriptions)
    (setf documentation nil))
  (let ((struct-name (if (symbolp name-and-options)
			 name-and-options
			 (car name-and-options))))
    (flet ((parse-option (option collector)
	     (etypecase option
	       (symbol
		(ecase option
		  (:conc-name (push "" (getf collector :conc-name)))
		  (:constructor (push (intern (concatenate 'string (string 'make-) (string struct-name)))
				      (getf collector :constructor)))
		  (:copier)		; do default
		  (:predicate)		; do default
		  (:named (push t (getf collector :named)))))
	       ((cons symbol null)
		(ecase (car option)
		  (:conc-name (push "" (getf collector :conc-name)))
		  (:constructor (push (intern (concatenate 'string
							   (string 'make-) (string struct-name)))
				      (getf collector :constructor)))
		  (:copier)		; do default
		  (:predicate)		; do default
		  (:named (push t (getf collector :named)))
		  (:print-object)
		  (:print-function)))
	       ((cons symbol (cons * null))
		(let ((parameter (second option)))
		  (ecase (car option)
		    (:superclass (push parameter (getf collector :superclass)))
		    (:conc-name (push (string (or parameter ""))
				      (getf collector :conc-name)))
		    (:constructor (push parameter (getf collector :constructor)))
		    (:copier (push parameter (getf collector :copier)))
		    (:predicate (push parameter (getf collector :predicate)))
		    (:type (push parameter (getf collector :type)))
		    (:initial-offset (push parameter (getf collector :initial-offset)))
		    (:print-object (push parameter (getf collector :print-object)))
		    (:print-function (push parameter (getf collector :print-function)))
                    (:include (push (cdr option) (getf collector :include))))))
	       ((cons symbol (cons * cons))
		(ecase (car option)
		  (:include (push (cdr option) (getf collector :include)))
		  (:constructor
		   (assert (= 3 (length option)))
		   (push (cons (second option) (third option))
			 (getf collector :constructor))))))
	     collector))
      (let ((options nil))
	(when (listp name-and-options)
	  (dolist (option (cdr name-and-options))
	    (setf options (parse-option option options))))
	(macrolet ((default ((option &optional (max-values 1000000)) default-form)
		     `(if (not (getf options ,option))
			  (push ,default-form (getf options ,option))
			  (assert (<= 1 (length (getf options ,option)) ,max-values) ()
				  "Option ~S given too many times." ,option))))
	  (default (:type 1) 'class-struct)
	  (default (:superclass 1) 'structure-object)
	  (default (:named 1) nil)
	  (default (:conc-name 1)
	      (concatenate 'string (string struct-name) (string #\-)))
	  (default (:constructor)
	      (intern (concatenate 'string (string 'make-) (string struct-name))))
	  (default (:predicate 1)
	      (intern (concatenate 'string (string struct-name) (string '-p))))
	  (default (:copier)
	      (intern (concatenate 'string (string 'copy-) (string struct-name)))))
	(let* ((struct-type (first (getf options :type)))
	       (superclass (first (getf options :superclass)))
	       (struct-named (first (getf options :named)))
	       (conc-name (first (getf options :conc-name)))
	       (predicate-name (first (getf options :predicate)))
	       (standard-name-and-options (if (not (consp name-and-options))
					      name-and-options
					      (remove :superclass name-and-options
						      :key (lambda (x)
							     (when (consp x) (car x))))))
	       (canonical-slot-descriptions
		(mapcar #'(lambda (d)
			    "(<slot-name> <init-form> <type> <read-only-p> <initarg>)"
			    (if (symbolp d)
				(list d nil nil nil (intern (symbol-name d) :keyword))
				(destructuring-bind (n &optional i &key type read-only)
				    d
				  (list n i type read-only (intern (symbol-name n) :keyword)))))
			slot-descriptions))
	       (slot-names (mapcar #'car canonical-slot-descriptions))
	       (key-lambda (mapcar #'(lambda (d) (list (first d) (second d)))
				   canonical-slot-descriptions)))
	  (ecase struct-type
	    (class-struct
	     `(progn
		(eval-when (:compile-toplevel)
		  (setf (gethash '(:translate-when :eval ,struct-name :cl :muerte.cl)
				 (movitz::image-struct-slot-descriptions movitz:*image*))
			'(:translate-when :eval ,slot-descriptions :cl :muerte.cl))
		  (defstruct (:translate-when :eval ,standard-name-and-options :cl :muerte.cl)
		    . (:translate-when :eval ,slot-names :cl :muerte.cl)))
		(defclass ,struct-name (,superclass) ()
		  (:metaclass structure-class)
		  (:slots ,(loop for (name init-form type read-only init-arg) in canonical-slot-descriptions
			      as location upfrom 0
			      collect (movitz-make-instance 'structure-slot-definition
							    :name name
							    :initarg init-arg
							    :initform init-form
							    :type type
							    :readonly read-only
							    :location location))))
		,@(loop for copier in (getf options :copier)
		     if (and copier (symbolp copier))
		     collect
		     `(defun ,copier (x)
			(copy-structure x)))
		,@(loop for constructor in (getf options :constructor)
		     if (and constructor (symbolp constructor))
		     collect
		     `(defun ,constructor (&rest args) ; &key ,@key-lambda)
			(declare (dynamic-extent args))
			(apply 'make-structure ',struct-name args))
		     else if (and constructor (listp constructor))
		     collect
		     (let* ((boa-constructor (car constructor))
			    (boa-lambda-list (cdr constructor))
			    (boa-variables (movitz::list-normal-lambda-list-variables boa-lambda-list)))
		       `(defun ,boa-constructor ,boa-lambda-list
			  (let ((class (compile-time-find-class ,struct-name)))
			    (with-allocation-assembly (,(+ 2 (length slot-names))
							:fixed-size-p t
							:object-register :eax)
			      (:movl ,(dpb (length slot-names)
					   (byte 18 14)
					   (movitz:tag :defstruct))
				     (:eax (:offset movitz-struct type)))
			      (:load-lexical (:lexical-binding class) :ebx)
			      (:movl :ebx (:eax (:offset movitz-struct class)))
			      ,@(loop for slot-name in slot-names as i upfrom 0
				   if (member slot-name boa-variables)
				   append
				   `((:load-lexical (:lexical-binding ,slot-name) :ebx)
				     (:movl :ebx (:eax (:offset movitz-struct slot0)
						       ,(* 4 i))))
				   else append
				   `((:movl :edi (:eax (:offset movitz-struct slot0)
						       ,(* 4 i)))))
			      ,@(when (oddp (length slot-names))
				      `((:movl :edi (:eax (:offset movitz-struct slot0)
							  ,(* 4 (length slot-names))))))))))
		     else if constructor
		     do (error "Don't know how to make class-struct constructor: ~S" constructor))
		,(when predicate-name
		       `(defun-by-proto ,predicate-name struct-predicate-prototype
			  (struct-class (:movitz-find-class ,struct-name))))
		,@(loop for (slot-name nil nil read-only-p) in canonical-slot-descriptions
		     as accessor-name = (intern (concatenate 'string conc-name (string slot-name))
						(movitz::symbol-package-fix-cl struct-name))
		     as slot-number upfrom 0
		     unless read-only-p
		     collect
		     `(defun-by-proto (setf ,accessor-name) (setf struct-accessor-prototype)
			(struct-name ,struct-name)
			(slot-number ,slot-number))
		     collect
		     `(defun-by-proto ,accessor-name struct-accessor-prototype
			(struct-name ,struct-name)
			(slot-number ,slot-number)))
		',struct-name))
	    (list
	     `(progn
		,@(if struct-named
		      (append
		       (loop for constructor in (getf options :constructor)
			  if (symbolp constructor)
			  collect
			  `(defun ,constructor (&key ,@key-lambda)
			     (list ',struct-name ,@(mapcar #'car key-lambda)))
			  else do (error "don't know how to make constructor: ~S" constructor))
		       (when predicate-name
			 `((defun ,predicate-name (x)
			     (and (consp x) (eq ',struct-name (car x)))))))
		      (loop for constructor in (getf options :constructor)
			 if (symbolp constructor)
			 collect
			 `(defun ,constructor (&key ,@key-lambda)
			    (list ,@(mapcar #'car key-lambda)))
			 else do (error "don't know how to make constructor: ~S" constructor)))
		,@(loop for (slot-name nil nil read-only-p) in canonical-slot-descriptions
		     as accessor-name = (intern (concatenate 'string conc-name (string slot-name))
						(movitz::symbol-package-fix-cl struct-name))
		     as slot-number upfrom (if struct-named 1 0)
		     unless read-only-p
		     collect
		     `(defun-by-proto (setf ,accessor-name) (setf list-struct-accessor-prototype)
			(slot-number ,slot-number))
		     collect
		     `(defun-by-proto ,accessor-name list-struct-accessor-prototype
			(slot-number ,slot-number)))
		',struct-name))
	    ))))))

(defmacro/run-time defstruct (&rest ignore)
  (identity 'structure); just to reference the symbol.
  (error "Defstruct not implemented."))
