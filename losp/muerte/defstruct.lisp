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
;;;; $Id: defstruct.lisp,v 1.3 2004/03/22 16:37:59 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)
(provide :muerte/defstruct)

(in-package muerte)

(defun struct-predicate-prototype (obj)
  "Prototype function for predicates of user-defined struct.
Parameters: struct-name."
  (with-inline-assembly (:returns :boolean-zf=1)
    (:compile-form (:result-mode :eax) obj)
    (:leal (:eax #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jnz 'fail)
    (:cmpb #.(movitz:tag :defstruct) (-2 :eax))
    (:jne 'fail)
    (:load-constant struct-name :ebx)
    (:cmpl :ebx (:eax #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)))
    fail))

(defun structure-ref (object slot-number)
  (macrolet ((do-it ()
	       `(with-inline-assembly (:returns :eax)
		  ;; type test
		  (:compile-form (:result-mode :eax) object)
		  (:leal (:eax ,(- (movitz:tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jne '(:sub-program (type-error) (:int 60)))
		  (:cmpb ,(movitz:tag :defstruct) (-2 :eax))
		  (:jne '(:sub-program (type-error) (:int 60)))
		  ;; type test passed, read slot
		  ,@(if (= 4 movitz::+movitz-fixnum-factor+)
			`((:compile-form  (:result-mode :ebx) slot-number)
			  (:movl (:eax :ebx #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0))
				 :eax))
		      `((:compile-form  (:result-mode :untagged-fixnum-ecx) slot-number)
			(:movl (:eax (:ecx 4) #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0))
			       :eax))))))
    (do-it)))

(defun (setf structure-ref) (value object slot-number)
  (macrolet ((do-it ()
	       (assert (= 4 movitz::+movitz-fixnum-factor+))
	       `(with-inline-assembly (:returns :eax)
		  ;; type test
		  (:compile-two-forms (:eax :ebx) object slot-number)
		  (:leal (:eax ,(- (movitz:tag :other))) :ecx)
		  (:testb 7 :cl)
		  (:jne '(:sub-program (type-error) (:int 60)))
		  (:cmpb ,(movitz:tag :defstruct) (-2 :eax))
		  (:jne '(:sub-program (type-error) (:int 60)))
		  (:movzxw (:eax ,(bt:slot-offset 'movitz::movitz-struct 'movitz::length)) :ecx)
		  (:leal ((:ecx ,movitz::+movitz-fixnum-factor+)) :ecx)
		  (:testb ,movitz::+movitz-fixnum-zmask+ :bl)
		  (:jnz '(:sub-program (not-fixnum) (:int 107)))
		  (:cmpl :ecx :ebx)
		  (:jae '(:sub-program (out-of-range) (:int 61)))
		  ;; type test passed, read slot
		  (:compile-form (:result-mode :ecx) value)
		  (:movl :ecx (:eax :ebx #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0))))))
    (do-it)))

(defun struct-accessor-prototype (object)
  "Parameters: struct-name, slot-number."
  (with-inline-assembly (:returns :eax)
    ;; type test
    (:compile-form (:result-mode :eax) object)
    (:leal (:eax #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jne '(:sub-program (type-error) (:int 60)))
    (:cmpb #.(movitz:tag :defstruct) (-2 :eax))
    (:jne '(:sub-program (type-error) (:int 60)))
    (:load-constant struct-name :ebx)
    (:cmpl :ebx (:eax #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)))
    (:jne '(:sub-program (type-error) (:int 60)))
    ;; type test passed, read slot
    (:load-constant slot-number :ecx)
    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (:movl (:eax (:ecx 4) #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0))
	   :eax)))

(defun (setf struct-accessor-prototype) (value obj)
  "Parameters: struct-name, slot-number."
  (with-inline-assembly (:returns :eax)
    (:compile-two-forms (:eax :ebx) value obj)
    ;; type test
    (:leal (:ebx #.(cl:- (movitz:tag :other))) :ecx)
    (:testb 7 :cl)
    (:jnz '(:sub-program (type-error) (:int 60)))
    (:cmpb #.(movitz:tag :defstruct) (-2 :ebx))
    (:jne '(:sub-program (type-error) (:int 60)))
    (:load-constant struct-name :ecx)
    (:cmpl :ecx (:ebx #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)))
    (:jne '(:sub-program (type-error) (:int 60)))
    ;; type test passed, write slot
    (:load-constant slot-number :ecx)
    (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
    (:movl :eax (:ebx (:ecx 4) #.(bt:slot-offset 'movitz::movitz-struct 'movitz::slot0)))))

(defun list-struct-accessor-prototype (s)
  (nth 'slot-number s))

(defun (setf list-struct-accessor-prototype) (value s)
  (setf (nth 'slot-number s) value))

(defmacro defstruct (name-and-options &optional documentation &rest slot-descriptions)
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
		    (:conc-name (push (string (or parameter ""))
				      (getf collector :conc-name)))
		    (:constructor (push parameter (getf collector :constructor)))
		    (:copier (push parameter (getf collector :constructor)))
		    (:predicate (push parameter (getf collector :predicate)))
		    (:type (push parameter (getf collector :type)))
		    (:initial-offset (push parameter (getf collector :initial-offset)))
		    (:print-object (push parameter (getf collector :print-object)))
		    (:print-function (push parameter (getf collector :print-function))))))
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
	  (loop for option in (cdr name-and-options)
	      do (setf options (parse-option option options))))
	(macrolet ((default ((option &optional (max-values 1000000)) default-form)
		       `(if (not (getf options ,option))
			    (push ,default-form (getf options ,option))
			  (assert (<= 1 (length (getf options ,option)) ,max-values) ()
			    "Option ~S given too many times." ,option))))
	  (default (:type 1) 'class-struct)
	  (default (:named 1) nil)
	  (default (:conc-name 1)
	      (concatenate 'string (string struct-name) (string #\-)))
	  (default (:constructor)
	      (intern (concatenate 'string (string 'make-) (string struct-name))))
	  (default (:predicate 1)
	      (intern (concatenate 'string (string struct-name) (string '-p)))))
	(let* ((struct-type (first (getf options :type)))
	       (struct-named (first (getf options :named)))
	       (conc-name (first (getf options :conc-name)))
	       (predicate-name (first (getf options :predicate)))
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
		  (defstruct (:translate-when :eval ,name-and-options :cl :muerte.cl)
		    . (:translate-when :eval ,slot-names :cl :muerte.cl)))
		,@(loop for constructor in (getf options :constructor)
		      if (and constructor (symbolp constructor))
		      collect
			`(defun ,constructor (&key ,@key-lambda)
			   (let ((s (malloc-words ,(length slot-names))))
			     (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)
						    0 :lisp)
			       ',struct-name)
			     (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::type)
						    0 :unsigned-byte8)
			       #.(movitz::tag :defstruct))
			     (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::length)
						    0 :unsigned-byte16)
			       ,(length slot-names))
			     ,@(loop for slot-name in slot-names as i upfrom 0 collecting
				     `(setf (memref s #.(bt:slot-offset 'movitz::movitz-struct
										 'movitz::slot0)
							     ,i :lisp)
					,slot-name))
			     s))
		      else if (and constructor (listp constructor))
		      collect
			(let* ((boa-constructor (car constructor))
			       (boa-lambda-list (cdr constructor))
			       (boa-variables (movitz::list-normal-lambda-list-variables boa-lambda-list)))
			  `(defun ,boa-constructor ,boa-lambda-list
			     (let ((s (malloc-words ,(length slot-names))))
			       (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::name)
						      0 :lisp)
				 ',struct-name)
			       (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::type)
						      0 :unsigned-byte8)
				 #.(movitz::tag :defstruct))
			       (setf (memref s #.(bt:slot-offset 'movitz::movitz-struct 'movitz::length)
						      0 :unsigned-byte16)
				 ,(length slot-names))
			       ,@(loop for slot-name in slot-names as i upfrom 0
				     if (member slot-name boa-variables)
				     collect
				       `(setf (memref s #.(bt:slot-offset 'movitz::movitz-struct
										   'movitz::slot0)
							       ,i :lisp)
					  ,slot-name)
				     else collect
					  `(setf (memref s #.(bt:slot-offset 'movitz::movitz-struct
										      'movitz::slot0)
								  ,i :lisp)
					     nil))
			       s)))
		      else if constructor
		      do (error "Don't know how to make class-struct constructor: ~S" constructor))
		,(when predicate-name
		   `(defun-by-proto ,predicate-name struct-predicate-prototype
		      (struct-name ,struct-name)))
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
		(defclass ,struct-name (structure-object) ()
			  (:metaclass structure-class)
			  (:slots ,canonical-slot-descriptions))
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

(defun structure-object-name (x)
  (movitz-accessor x movitz-struct name))

(defmacro with-accessors (slot-entries instance-form &body declarations-and-forms)
  (let ((instance-variable (gensym "with-accessors-instance-")))
    `(let ((,instance-variable ,instance-form))
       (declare (ignorable ,instance-variable))
       (symbol-macrolet ,(loop for (variable-name accessor-name) in slot-entries
			     collecting `(,variable-name (,accessor-name ,instance-variable)))
	 ,@declarations-and-forms))))
