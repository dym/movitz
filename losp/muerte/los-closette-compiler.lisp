;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      los-closette-compiler.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Aug 29 13:15:11 2002
;;;;                
;;;; $Id: los-closette-compiler.lisp,v 1.23 2008-04-27 19:42:26 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :muerte/los-closette-compiler)

(in-package muerte)

(define-compile-time-variable *class-table*
    (make-hash-table :test 'eq))

(define-compile-time-variable *eql-specializer-table*
    (make-hash-table :test 'eql))

(define-compile-time-variable *the-slots-of-standard-class* nil)
(define-compile-time-variable *the-position-of-standard-effective-slots* nil)
(define-compile-time-variable *the-class-standard-class* nil)
(define-compile-time-variable *the-standard-method-combination* nil)
    
(eval-when (:compile-toplevel)		; extends to EOF

  (defvar *classes-with-old-slot-definitions* nil)

  ;; standard-class -> std-slotted-class -> class -> ..

  (defconstant +the-defclasses-before-class+
      '(progn
	(defclass-los metaobject () ())
	(defclass-los specializer (metaobject) ())
	(defclass-los eql-specializer (specializer)
	  ((object)))))

  (defconstant +the-defclass-class+	; class's defclass form
      '(defclass-los class (specializer)
	((name
	  :initarg name)
	 (class-precedence-list)	; :accessor class-precedence-list
	 (direct-superclasses		; :accessor class-direct-superclasses
	  :initarg :direct-superclasses)
	 (direct-subclasses		; :accessor class-direct-subclasses
	  :initform ())
	 (direct-methods
	  :initarg :direct-methods
	  :initform ())
	 (plist
	  :initform nil)
	 (prototype
	  :initform nil))))
  
  (defconstant +the-defclass-std-slotted-class+
      '(defclass-los std-slotted-class (class)
	((effective-slots)		; :accessor class-slots
  	 (direct-slots))))		; :accessor class-direct-slots
  
  (defconstant +the-defclasses-slots+
      '(progn
	(defclass-los slot-definition (metaobject) (name))
	(defclass-los effective-slot-definition (slot-definition) ())
	(defclass-los direct-slot-definition (slot-definition) ())
	(defclass-los standard-slot-definition (slot-definition)
	  (type initform initfunction initargs allocation))
	(defclass-los standard-effective-slot-definition (standard-slot-definition effective-slot-definition)
	  (location))))

  (defconstant +the-defclass-standard-direct-slot-definition+
      '(defclass-los standard-direct-slot-definition
	(standard-slot-definition direct-slot-definition)
	(position readers writers)))

  (defconstant +the-defclass-instance-slotted-class+
      '(defclass-los instance-slotted-class (class)
	((instance-slots))))
  
  (defconstant +the-defclass-standard-class+ ;standard-class's defclass form
      '(defclass-los standard-class (instance-slotted-class std-slotted-class)
	()))
  
  (defmacro push-on-end (value location)
    `(setf ,location (nconc ,location (list ,value))))
  
  (defun mapappend (fun &rest args)
    (declare (dynamic-extent args))
    (if (some #'null args)
	()
      (append (apply fun (mapcar #'car args))
	      (apply #'mapappend fun (mapcar #'cdr args)))))

  (defun make-direct-slot-definition (class-name
				      &key name (initargs ()) (initform nil) (initfunction nil)
					   (readers ()) (writers ()) (allocation :instance)
					   (type t)
					   documentation)
    (declare (ignore documentation type)) ; for now
    (cond
     ((movitz-find-class 'standard-direct-slot-definition nil)
      (let ((slot (std-allocate-instance (movitz-find-class 'standard-direct-slot-definition))))
	(setf (std-slot-value slot 'name) name
	      (std-slot-value slot 'initargs) initargs
	      (std-slot-value slot 'initform) initform
	      (std-slot-value slot 'initfunction) initfunction
	      (std-slot-value slot 'allocation) allocation
	      (std-slot-value slot 'readers) readers
	      (std-slot-value slot 'writers) writers)
	slot))
     (t (pushnew class-name *classes-with-old-slot-definitions*)
	(muerte::translate-program (vector name ; 1
					   initargs ; 3
					   initform ; 5 
					   initfunction ; 7
					   allocation ; 9
					   readers ; 11
					   writers
					   nil)
				   :cl :muerte.cl))))

  (defun translate-direct-slot-definition (old-slot)
    (if (not (vectorp old-slot))
	old-slot
      (loop with slot = (std-allocate-instance (movitz-find-class 'standard-direct-slot-definition))
	  for slot-name in '(name initargs initform initfunction allocation readers writers)
	  as value across old-slot
	  do (setf (std-slot-value slot slot-name) value)
	  finally (return slot))))
      
  (defun make-effective-slot-definition (class &key name (initargs ()) (initform nil) (initfunction nil)
						    (allocation :instance) location)
    (cond
     ((movitz-find-class 'standard-effective-slot-definition nil)
      (let ((slot (std-allocate-instance (movitz-find-class 'standard-effective-slot-definition))))
	(setf (std-slot-value slot 'name) name
	      (std-slot-value slot 'initargs) initargs
	      (std-slot-value slot 'initform) initform
	      (std-slot-value slot 'initfunction) initfunction
	      (std-slot-value slot 'allocation) allocation
	      (std-slot-value slot 'location) location)
	slot))
     (t (pushnew class *classes-with-old-slot-definitions*)
	(translate-program (vector name
				   initargs
				   initform
				   initfunction
				   allocation
				   nil nil
				   location)
			   :cl :muerte.cl))))

  (defun translate-effective-slot-definition (old-slot)
    (if (not (vectorp old-slot))
	old-slot
      (loop with slot = (std-allocate-instance (movitz-find-class 'standard-effective-slot-definition))
	  for slot-name in '(name initargs initform initfunction allocation nil nil location)
	  as value across old-slot
	  when slot-name
	  do (setf (std-slot-value slot slot-name) value)
	  finally (assert (integerp (std-slot-value slot 'location)) ()
		    "No location for ~S: ~S" slot (std-slot-value slot 'location))
	  finally (return slot))))
  
  (defun slot-definition-name (slot)
    (if (vectorp slot)
	(svref slot 0)
      (std-slot-value slot 'name)))
  (defun (setf slot-definition-name) (new-value slot)
    (setf (svref slot 0) new-value))

  (defun slot-definition-initargs (slot)
    (if (vectorp slot)
	(svref slot 1)
      (std-slot-value slot 'initargs)))
  (defun (setf slot-definition-initargs) (new-value slot)
    (setf (svref slot 1) new-value))

  (defun slot-definition-initform (slot)
    (if (vectorp slot)
	(svref slot 2)
      (std-slot-value slot 'initform)))
  (defun (setf slot-definition-initform) (new-value slot)
    (setf (svref slot 2) new-value))

  (defun slot-definition-initfunction (slot)
    (if (vectorp slot)
	(svref slot 3)
      (std-slot-value slot 'initfunction)))
  (defun (setf slot-definition-initfunction) (new-value slot)
    (setf (svref slot 3) new-value))

  (defun slot-definition-allocation (slot)
    (if (vectorp slot)
	(svref slot 4)
      (std-slot-value slot 'allocation)))
  (defun (setf slot-definition-allocation) (new-value slot)
    (setf (svref slot 4) new-value))

  (defun instance-slot-p (slot)
    (eq (slot-definition-allocation slot) :instance))

  (defun slot-definition-readers (slot)
    (if (vectorp slot)
	(svref slot 5)
      (std-slot-value slot 'readers)))
  (defun (setf slot-definition-readers) (new-value slot)
    (setf (svref slot 5) new-value))

  (defun slot-definition-writers (slot)
    (if (vectorp slot)
	(svref slot 6)
      (std-slot-value slot 'writers)))
  (defun (setf slot-definition-writers) (new-value slot)
    (setf (svref slot 6) new-value))

  (defun slot-definition-location (slot)
    (if (vectorp slot)
	(svref slot 7)
      (std-slot-value slot 'location)))
  (defun (setf slot-definition-location) (new-value slot)
    (check-type new-value integer)
    (if (vectorp slot)
	(setf (svref slot 7) new-value)
      (setf (std-slot-value slot 'location) new-value)))

;;; Defining the metaobject slot accessor function as regular functions 
;;; greatly simplifies the implementation without removing functionality.


  (defun movitz-class-name (class) (std-slot-value class 'name))
  (defun (setf movitz-class-name) (new-value class)
    (setf (movitz-slot-value class 'name) new-value))

  (defun class-direct-superclasses (class)
    (movitz-slot-value class 'direct-superclasses))

  (defun (setf class-direct-superclasses) (new-value class)
    (setf (movitz-slot-value class 'direct-superclasses) new-value))

  (defun class-direct-slots (class)
    (if (and (eq (movitz-class-of (movitz-class-of class)) *the-class-standard-class*)
	     (movitz-slot-exists-p class 'direct-slots))
	(movitz-slot-value class 'direct-slots)
      #+ignore (warn "no direct-slots for ~W" class)))
  (defun (setf class-direct-slots) (new-value class)
    (setf (movitz-slot-value class 'direct-slots) new-value))

  (defun class-precedence-list (class)
    (movitz-slot-value class 'class-precedence-list))
  (defun (setf class-precedence-list) (new-value class)
    (setf (movitz-slot-value class 'class-precedence-list) new-value))

  (defun class-slots (class)
    (movitz-slot-value class 'effective-slots))
  (defun (setf class-slots) (new-value class)
    (setf (movitz-slot-value class 'effective-slots) new-value))

  (defun class-direct-subclasses (class)
    (movitz-slot-value class 'direct-subclasses))
  (defun (setf class-direct-subclasses) (new-value class)
    (setf (movitz-slot-value class 'direct-subclasses) new-value))

  (defun class-direct-methods (class)
    (movitz-slot-value class 'direct-methods))
  (defun (setf class-direct-methods) (new-value class)
    (setf (movitz-slot-value class 'direct-methods) new-value))

;;; defclass

  (defmacro defclass-los (name direct-superclasses direct-slots &rest options)
    `(ensure-class ',name
		   :direct-superclasses
		   ,(canonicalize-direct-superclasses direct-superclasses)
		   :direct-slots
		   ,(canonicalize-direct-slots direct-slots name nil)
		   ,@(canonicalize-defclass-options options nil name)))

  (defun canonicalize-direct-slots (direct-slots class-name env)
    `(list ,@(mapcar (lambda (ds) (canonicalize-direct-slot ds class-name env)) direct-slots)))

  (defun canonicalize-direct-slot (spec class-name env)
    (if (symbolp spec)
	`(list :name ',spec)
      (let ((name (car spec))
	    (initfunction nil)
	    (initform nil)
	    (initargs ())
	    (readers ())
	    (writers ())
	    (other-options ()))
	(do ((olist (cdr spec) (cddr olist)))
	    ((null olist))
	  (case (car olist)
	    (:initform
	     (let ((form (cadr olist)))
	       (setq initfunction
		 (if (movitz:movitz-constantp form env)
		     (list 'quote (list 'quote (movitz::eval-form form env)))
		   (compile-in-lexical-environment env
						   (muerte::translate-program
						    (list 'slot-initfunction
							  class-name name)
						    :cl :muerte.cl)
						   `(lambda () ,form))))
	       (setq initform `',form)))
	    (:initarg 
	     (push-on-end (cadr olist) initargs))
	    (:reader 
	     (push-on-end (cadr olist) readers))
	    (:writer 
	     (push-on-end (cadr olist) writers))
	    (:accessor
	     (push-on-end (cadr olist) readers)
	     (push-on-end `(setf ,(cadr olist)) writers))
	    (otherwise 
	     (push-on-end `',(car olist) other-options)
	     (push-on-end `',(cadr olist) other-options))))
	`(list
	  :name ',name
	  ,@(when initfunction
	      `(:initform ,initform :initfunction ,initfunction))
	  ,@(when initargs `(:initargs ',initargs))
	  ,@(when readers `(:readers ',readers))
	  ,@(when writers `(:writers ',writers))
	  ,@other-options))))

  (defun canonicalize-direct-superclasses (direct-superclasses)
    `(list ,@(mapcar #'canonicalize-direct-superclass direct-superclasses)))

  (defun canonicalize-direct-superclass (class-name)
    `(movitz-find-class ',class-name))

  (defun intern-eql-specializer (object)
    (or (gethash object *eql-specializer-table*)
	(setf (gethash object *eql-specializer-table*)
	  (let ((s (std-allocate-instance (movitz-find-class 'eql-specializer))))
	    (setf (movitz-slot-value s 'object) object)
	    s))))
  
  (defun canonicalize-defclass-options (options env class-name)
    (mapcan (lambda (o) (canonicalize-defclass-option o env class-name)) options))
  
  (defun canonicalize-defclass-option (option env class-name)
    (case (car option)
      ((:metaclass)
       (list ':metaclass
	     `(movitz-find-class ',(cadr option))))
      ((:default-initargs)
       (list :default-initargs-function
	     (list 'quote
		   (cons (compile-in-lexical-environment
			  env (gensym (format nil "default-initargs-~A-" class-name))
			  `(lambda (o)
			     (case o
			       ,@(loop for (arg val) on (cdr option) by #'cddr
				     collect `(,arg ,val)))))
			 (loop for arg in (cdr option) by #'cddr collect arg)))))
      (t (list `',(car option) `',(cadr option)))))

  
;;; Class name-space accessors
  
  (defun movitz-find-class (symbol &optional (errorp t))
    (let ((symbol (muerte::translate-program symbol :cl :muerte.cl)))
      (let ((class (gethash symbol *class-table*)))
	(if (and (null class) errorp)
	    (error "Closette compiler: No LOS class named ~W." symbol)
	  class))))
  
  (defun movitz-find-class-name (class)
    (maphash (lambda (key value)
	       (when (eq value class)
		 (return-from movitz-find-class-name key)))
	     *class-table*))

  (defun (setf movitz-find-class) (new-value symbol)
    (let ((symbol (muerte::translate-program symbol :cl :muerte.cl)))
      (if new-value
	  (setf (gethash symbol *class-table*) new-value)
	(remhash symbol *class-table*)))
    new-value)

  (defun forget-all-classes ()
    (clrhash *class-table*)
    (values))

  (defun find-specializer (name)
    (cond
     ((symbolp name)
      (movitz-find-class name))
     ((and (consp name)
	   (string= 'eql (car name)))
      (intern-eql-specializer (movitz::eval-form (cadr name))))
     (t (error "Unknown specializer: ~S" name))))

  (defun specializer-name (specializer)
    (if (eq (movitz-find-class 'eql-specializer)
	    (movitz-class-of specializer))
	(translate-program (list 'eql (movitz-slot-value specializer 'object))
			   :cl :muerte.cl)
      (movitz-class-name specializer)))

;;;
  
  ;; LOS standard-instance
  (defun allocate-std-instance (class slots)
    (movitz::make-movitz-std-instance class slots))

  (defun std-instance-class (class)
    (etypecase class
      (movitz::movitz-std-instance
       (movitz::movitz-std-instance-class class))
      (movitz::movitz-funobj-standard-gf
       (movitz::standard-gf-class class))))

  (defun (setf std-instance-class) (value class)
    (etypecase class
      (movitz::movitz-std-instance
       (setf (movitz::movitz-std-instance-class class) value))
      (movitz::movitz-funobj-standard-gf
       (setf (movitz::standard-gf-class class) value))))

  (defun std-instance-slots (class)
    (etypecase class
      (movitz::movitz-std-instance
       (movitz::movitz-std-instance-slots class))
      (movitz::movitz-funobj-standard-gf
       (movitz::standard-gf-slots class))))

  (defun (setf std-instance-slots) (value class)
    (etypecase class
      (movitz::movitz-std-instance
       (setf (movitz::movitz-std-instance-slots class) value))
      (movitz::movitz-funobj-standard-gf
       (setf (movitz::standard-gf-slots class) value))))

  (defun std-allocate-instance (class)
    (allocate-std-instance class (make-array (count-if #'instance-slot-p (class-slots class))
					     :initial-element (movitz::unbound-value))))
  
  ;; LOS standard-gf-instance
  (defun allocate-std-gf-instance (class slots &rest init-args)
    (apply #'movitz::make-standard-gf class slots init-args))
  
  (defun std-allocate-gf-instance (class &rest init-args)
    (apply #'allocate-std-gf-instance
	   class
	   (make-array (count-if #'instance-slot-p (class-slots class))
		       :initial-element (movitz::unbound-value))
	   init-args))
  
  (defun std-gf-instance-class (class)
    (movitz::standard-gf-class class))
  (defun (setf std-gf-instance-class) (value class)
    (setf (movitz::standard-gf-class class) value))
  (defun std-gf-instance-slots (class)
    (movitz::standard-gf-slots class))
  (defun (setf std-gf-instance-slots) (value class)
    (setf (movitz::standard-gf-slots class) value))
  

;;;
  (defvar *slot-location-nesting* 0)
  (defun slot-location (class slot-name)
    (when (< 10 *slot-location-nesting*)
      (break "Unbounded slot-location?"))
    (let ((*slot-location-nesting* (1+ *slot-location-nesting*)))
      (cond
       ((and (eq slot-name 'effective-slots)
	     (eq class *the-class-standard-class*))
	(position 'effective-slots *the-slots-of-standard-class*
		  :key #'slot-definition-name))
       ((eq class (movitz-find-class 'standard-effective-slot-definition nil))
	(or (position slot-name '(name type initform initfunction initargs allocation location))
	    (error "No slot ~S in ~S." slot-name (movitz-class-name class))))
       (t #+ignore
	  (when (and (eq slot-name 'effective-slots)
		     (subclassp class *the-class-standard-class*))
	    (break "Looking for slot ~S in class ~S, while std-class is ~S."
		   slot-name class *the-class-standard-class*))
	  (let ((slot (find slot-name
			    (std-slot-value class 'effective-slots)
			    :key #'slot-definition-name)))
	    (if (null slot)
		(error "Closette compiler: The slot ~S is missing from the class ~S."
		       slot-name class)
	      (let ((pos (position slot
				   (remove-if-not #'instance-slot-p
						  (std-slot-value class 'effective-slots)))))
		(if (null pos)
		    (error "Closette compiler: The slot ~S is not an instance slot in the class ~S."
			   slot-name class)
		  pos))))))))
  
  (defun movitz-class-of (instance)
    (std-instance-class instance))
  
  (defun subclassp (c1 c2)
    (find c2 (class-precedence-list c1)))

  (defun sub-specializer-p (c1 c2 c-arg)
    (let ((cpl (class-precedence-list c-arg)))
      (find c2 (cdr (member c1 cpl)))))

  (defun std-slot-value (instance slot-name)
    (let* ((slot-name (translate-program slot-name :cl :muerte.cl))
	   (location (slot-location (movitz-class-of instance) slot-name))
	   (slots (std-instance-slots instance))
	   (val (svref slots location)))
      (if (eq (movitz::unbound-value) val)
	  (error "Closette compiler: The slot ~S at ~D is unbound in the object ~S."
		 slot-name location instance)
	val)))
  
  (defun (setf std-slot-value) (value instance slot-name)
    (let* ((location (slot-location (movitz-class-of instance)
				    (translate-program slot-name :cl :muerte.cl)))
	   (slots (std-instance-slots instance)))
      (setf (svref slots location) (muerte::translate-program value :cl :muerte.cl))))
  
  (defun movitz-slot-value (object slot-name)
    (std-slot-value object (translate-program slot-name :cl :muerte.cl)))

  (defun (setf movitz-slot-value) (new-value object slot-name)
    (setf (std-slot-value object (translate-program slot-name :cl :muerte.cl))
      new-value))
  
  (defun std-slot-exists-p (instance slot-name)
    (not (null (find slot-name (class-slots (movitz-class-of instance))
		     :key #'slot-definition-name))))

  (defun movitz-slot-exists-p (object slot-name)
    (if (eq (movitz-class-of (movitz-class-of object)) *the-class-standard-class*)
	(std-slot-exists-p object slot-name)
      (error "Can't do this.")
      #+ignore (movitz-slot-exists-p-using-class (movitz-class-of object)
						 object slot-name)))

;;;
  
;;; Ensure class

  (defun ensure-class (name &rest all-keys &key (metaclass *the-class-standard-class*)
						direct-slots direct-superclasses
		       &allow-other-keys)
    (declare (dynamic-extent all-keys))
    (remf all-keys :metaclass)
    (let ((old-class (movitz-find-class name nil)))
      (if (and old-class
	       (eq metaclass *the-class-standard-class*))
	  (std-after-initialization-for-classes old-class
						:direct-slots direct-slots
						:direct-superclasses direct-superclasses)
	(let ((class (apply (cond
			     ((eq metaclass *the-class-standard-class*)
			      'make-instance-standard-class)
			     ((eq metaclass (movitz-find-class 'structure-class nil))
			      'make-instance-structure-class)
			     ((eq metaclass (movitz-find-class 'built-in-class nil))
			      'make-instance-built-in-class)
			     ((eq metaclass (movitz-find-class 'funcallable-standard-class nil))
			      'movitz-make-instance)
			     ((eq metaclass (movitz-find-class 'run-time-context-class nil))
			      'movitz-make-instance)
                             ((member *the-class-standard-class*
                                      (class-precedence-list metaclass))
                              'make-instance-standard-class)
			     (t (break "Unknown metaclass: ~S" metaclass)
				#+ignore 'make-instance-built-in-class
				'movitz-make-instance))
			    metaclass
			    :name name
			    all-keys)))
	  (setf (movitz-find-class name) class)))))
  
  (defun movitz-make-instance-funcallable (metaclass &rest all-keys &key name direct-superclasses direct-slots &allow-other-keys)
    (declare (ignore all-keys))
    (let ((class (std-allocate-instance metaclass)))
      (setf (movitz-class-name class) name)
      (setf (class-direct-subclasses class) ())
      (setf (class-direct-methods class) ())
      (std-after-initialization-for-classes class
					    :direct-slots direct-slots
					    :direct-superclasses direct-superclasses)
      class))
  
  (defun movitz-make-instance-run-time-context (metaclass &rest all-keys &key name direct-superclasses direct-slots size slot-map plist &allow-other-keys)
    (declare (ignore all-keys))
    (let ((class (std-allocate-instance metaclass)))
      (setf (std-slot-value class 'size)
	(or size (bt:sizeof 'movitz::movitz-run-time-context)))
      (setf (std-slot-value class 'slot-map)
	(or slot-map
	    (movitz::slot-map 'movitz::movitz-run-time-context
			      (cl:+ (bt:slot-offset 'movitz::movitz-run-time-context
						    'movitz::run-time-context-start)
				    0))))
      (setf (std-slot-value class 'plist) plist)
      (setf (movitz-class-name class) name)
      (setf (class-direct-subclasses class) ())
      (setf (class-direct-methods class) ())
      (std-after-initialization-for-classes class
					    :direct-slots direct-slots
					    :direct-superclasses direct-superclasses)
      class))  

  (defun movitz-make-instance (class &rest all-keys)
    ;; (warn "movitz-make-instance: ~S ~S" class all-keys)
    (when (symbolp class)
      (setf class (movitz-find-class class)))
    (cond
     ((eq class (movitz-find-class 'funcallable-standard-class nil))
      (apply 'movitz-make-instance-funcallable class all-keys) )
     ((eq class (movitz-find-class 'run-time-context-class nil))
      (apply 'movitz-make-instance-run-time-context class all-keys))
     (t (let ((instance (std-allocate-instance class)))
	  (dolist (slot (class-slots (movitz-class-of instance)))
	    (let ((slot-name (slot-definition-name slot)))
	      (multiple-value-bind (init-key init-value foundp)
		  (get-properties all-keys (slot-definition-initargs slot))
		(declare (ignore init-key))
		(when foundp
		  (setf (movitz-slot-value instance slot-name) init-value)))))
	  instance))))
  
;;; make-instance-standard-class creates and initializes an instance of
;;; standard-class without falling into method lookup.  However, it cannot be
;;; called until standard-class itself exists.

  (defun initialize-class-object (class &key name plist direct-methods
					     (direct-superclasses (list (movitz-find-class t)))
				  &allow-other-keys)
    (setf (movitz-class-name class) name
	  (std-slot-value class 'plist) plist
	  (class-direct-subclasses class) ()
	  (class-direct-methods class) direct-methods)
    (let ((supers direct-superclasses))
      (setf (class-direct-superclasses class) supers)
      (dolist (superclass supers)
	(push class (class-direct-subclasses superclass))))
    (setf (class-precedence-list class)
      (std-compute-class-precedence-list class))
    class)

  (defun make-instance-structure-class (metaclass &rest all-keys
					&key name slots direct-slots ((:metaclass dummy))
					     (direct-superclasses
					      (list (movitz-find-class 'structure-object))))
    (declare (ignore dummy all-keys))
    (assert (null direct-slots))
    (let ((class (std-allocate-instance (if (symbolp metaclass)
					    (movitz-find-class metaclass)
					  metaclass))))
      (setf (std-slot-value class 'slots) slots)
      (initialize-class-object class :name name
			       :direct-superclasses direct-superclasses)))

  (defun make-instance-built-in-class (metaclass &rest all-keys
				       &key name direct-superclasses
					    direct-methods direct-slots plist size slot-map
				       &allow-other-keys)
    (declare (ignore plist direct-methods direct-slots direct-superclasses name))
;;;    (assert (null direct-slots) (direct-slots)
;;;      "Closette compiler: This class can't have slots: ~S" direct-slots)
    (let ((class (std-allocate-instance (if (symbolp metaclass)
					    (movitz-find-class metaclass)
					  metaclass))))
      (when size (setf (std-slot-value class 'size) size))
      (setf (std-slot-value class 'slot-map) slot-map)
      (apply #'initialize-class-object class all-keys)))
  
  (defun make-instance-standard-class (metaclass &key name direct-superclasses direct-slots
						      default-initargs-function
						      documentation)
    (declare (ignore metaclass documentation))
    (let ((class (std-allocate-instance metaclass)))
      (setf (movitz-class-name class) name)
      (setf (class-direct-subclasses class) ())
      (setf (class-direct-methods class) ())
      (setf (movitz-slot-value class 'prototype) ())
      (setf (movitz-slot-value class 'plist)
	(when default-initargs-function
	  (list :default-initargs-function default-initargs-function)))
      (dolist (slot (class-slots (movitz-class-of class)))
        (let ((slot-name (slot-definition-name slot))
              (slot-initform (muerte::translate-program (slot-definition-initform slot)
                                                        '#:muerte.cl '#:cl)))
          (when slot-initform
            (setf (movitz-slot-value class slot-name) (movitz::eval-form slot-initform)))))
      (std-after-initialization-for-classes class
					    :direct-slots direct-slots
					    :direct-superclasses direct-superclasses)
      class))

  (defun std-after-initialization-for-classes (class &key direct-superclasses direct-slots)
    (let ((supers (or direct-superclasses
		      (list (movitz-find-class 'standard-object)))))
      (setf (class-direct-superclasses class) supers)
      (dolist (superclass supers)
	(pushnew class (class-direct-subclasses superclass))))
    (let ((slots (mapcar #'(lambda (slot-properties)
			     (apply #'make-direct-slot-definition
				    (movitz-class-name class)
				    slot-properties))
			 direct-slots)))
      (setf (class-direct-slots class) slots)
      (dolist (direct-slot slots)
	(dolist (reader (slot-definition-readers direct-slot))
	  (add-reader-method 
	   class reader (slot-definition-name direct-slot)))
	(dolist (writer (slot-definition-writers direct-slot))
	  (add-writer-method 
	   class writer (slot-definition-name direct-slot)))))
    (funcall (if (or (eq (movitz-class-of class)
                         *the-class-standard-class*)
		     (subclassp (movitz-class-of class)
                                (movitz-find-class 'std-slotted-class)))
		 #'std-finalize-inheritance
	       #'finalize-inheritance)
	     class)
    (values))


;;; finalize-inheritance

  (defun std-finalize-inheritance (class) 
    (setf (class-precedence-list class)
      (funcall (if (or (eq (movitz-class-of class) *the-class-standard-class*)
		       (subclassp (movitz-class-of class) (movitz-find-class 'std-slotted-class)))
		   #'std-compute-class-precedence-list
		 #'compute-class-precedence-list)
	       class))
    (setf (class-slots class)
      (funcall (if (or (eq (movitz-class-of class) *the-class-standard-class*)
		       (subclassp (movitz-class-of class) (movitz-find-class 'std-slotted-class)))
		   #'std-compute-slots
		 #'compute-slots)
	       class))
    (values))
  
  (defun finalize-inheritance (class)
    (error "Don't know how to finalize-inheritance for class ~S of class ~S."
	   class (class-of class)))

;;; Class precedence lists

  (defun std-compute-class-precedence-list (class)
    (let ((classes-to-order (collect-superclasses* class)))
;;;    (warn "class: ~W" class)
;;;    (warn "classes-to-order: ~W" classes-to-order)
      (topological-sort classes-to-order
			(remove-duplicates
			 (mapappend #'local-precedence-ordering
				    classes-to-order)
			 :test #'equal)
			#'std-tie-breaker-rule)))
  
  (defun compute-class-precedence-list (class)
    (error "Don't know how to compute class-precedence-list for ~S of class ~S."
	   class (class-of class)))

;;; topological-sort implements the standard algorithm for topologically
;;; sorting an arbitrary set of elements while honoring the precedence
;;; constraints given by a set of (X,Y) pairs that indicate that element
;;; X must precede element Y.  The tie-breaker procedure is called when it
;;; is necessary to choose from multiple minimal elements; both a list of 
;;; candidates and the ordering so far are provided as arguments.

  (defun topological-sort (elements constraints tie-breaker)
    ;; (warn "topological-sort:~%   ~W~%   ~W~%   ~W" elements constraints tie-breaker)
    (let ((remaining-constraints constraints)
	  (remaining-elements elements)
	  (result ())) 
      (loop
	(let ((minimal-elements 
	       (remove-if #'(lambda (class)
			      (member class remaining-constraints
				      :key #'cadr))
			  remaining-elements)))
	  (when (null minimal-elements)
	    (if (null remaining-elements)
		(return-from topological-sort result)
	      (error "Closette compiler: Inconsistent precedence graph.")))
	  (let ((choice (if (null (cdr minimal-elements))
			    (car minimal-elements)
			  (funcall tie-breaker
				   minimal-elements
				   result))))
	    (setq result (append result (list choice)))
	    (setq remaining-elements
	      (remove choice remaining-elements))
	    (setq remaining-constraints
	      (remove choice
		      remaining-constraints
		      :test #'member)))))))

;;; In the event of a tie while topologically sorting class precedence lists,
;;; the CLOS Specification says to "select the one that has a direct subclass
;;; rightmost in the class precedence list computed so far."  The same result
;;; is obtained by inspecting the partially constructed class precedence list
;;; from right to left, looking for the first minimal element to show up among
;;; the direct superclasses of the class precedence list constituent.  
;;; (There's a lemma that shows that this rule yields a unique result.)

  (defun std-tie-breaker-rule (minimal-elements cpl-so-far)
    (dolist (cpl-constituent (reverse cpl-so-far))
      (let* ((supers (class-direct-superclasses cpl-constituent))
	     (common (intersection minimal-elements supers)))
	(when (not (null common))
	  (return-from std-tie-breaker-rule (car common))))))

;;; This version of collect-superclasses* isn't bothered by cycles in the class
;;; hierarchy, which sometimes happen by accident.

  (defun collect-superclasses* (class)
    (labels ((all-superclasses-loop (seen superclasses)
	       (let ((to-be-processed (set-difference superclasses seen)))
		 (if (null to-be-processed)
		     superclasses
		   (let ((class-to-process (car to-be-processed)))
		     (all-superclasses-loop (cons class-to-process seen)
					    (union (class-direct-superclasses class-to-process)
						   superclasses)))))))
      (all-superclasses-loop () (list class))))

;;; The local precedence ordering of a class C with direct superclasses C_1,
;;; C_2, ..., C_n is the set ((C C_1) (C_1 C_2) ...(C_n-1 C_n)).

  (defun local-precedence-ordering (class)
    (mapcar #'list 
	    (cons class
		  (butlast (class-direct-superclasses class)))
	    (class-direct-superclasses class)))
  

;;; Slot inheritance

  (defun std-compute-slots (class)
    (let* ((all-slots (mapcan (lambda (c)
				(copy-list (class-direct-slots c)))
			      (reverse (class-precedence-list class))))
	   (all-names (remove-duplicates (mapcar #'slot-definition-name all-slots)))
	   (effective-slots (mapcar #'(lambda (name)
					(funcall (if (or (eq (movitz-class-of class)
							     *the-class-standard-class*)
							 (subclassp (movitz-class-of class)
								    (movitz-find-class 'std-slotted-class)))
						     #'std-compute-effective-slot-definition 
						   #'compute-effective-slot-definition)
						 class
						 name
						 (remove name all-slots
							 :key #'slot-definition-name
							 :test (complement #'eq))))
				    all-names)))
      (loop for i upfrom 0 as slot in effective-slots
	  do (setf (slot-definition-location slot) i))
      effective-slots))
  
  (defun compute-slots (class)
    (error "Don't know how to compute-slots for class ~S of class ~S."
	   class (class-of class)))
      
  (defun std-compute-effective-slot-definition (class name direct-slots)
    (declare (ignore name))
    (let ((initer (find-if-not #'null direct-slots
			       :key #'slot-definition-initfunction)))
      (make-effective-slot-definition (movitz-class-name class)
				      :name (slot-definition-name (car direct-slots))
				      :initform (if initer
						    (slot-definition-initform initer)
						  nil)
				      :initfunction (if initer
							(slot-definition-initfunction initer)
						      nil)
				      :initargs (remove-duplicates 
						 (mapappend #'slot-definition-initargs
							    direct-slots))
				      :allocation (slot-definition-allocation (car direct-slots)))))
  
  (defun compute-effective-slot-definition (class name direct-slots)
    (declare (ignore name direct-slots))
    (error "Don't know how to compute-effective-slot-definition for class ~S of class ~S."
	   class (class-of class)))
  

;;;;
  
  
;;;
;;; Generic function metaobjects and standard-generic-function
;;;

  (defun generic-function-name (gf)
    (slot-value gf 'movitz::name)
    #+ignore (movitz-slot-value gf 'name))
  (defun (setf generic-function-name) (new-value gf)
    (setf (slot-value gf 'movitz::name) new-value))

  (defun generic-function-lambda-list (gf)
    (slot-value gf 'movitz::lambda-list)
    #+ignore (movitz-slot-value gf 'lambda-list))
  (defun (setf generic-function-lambda-list) (new-value gf)
    (setf (slot-value gf 'movitz::lambda-list)
       new-value))

  (defun generic-function-methods (gf)
    (movitz-slot-value gf 'methods))
  (defun (setf generic-function-methods) (new-value gf)
    (setf (movitz-slot-value gf 'methods) new-value))

  (defun generic-function-method-combination (gf)
    (movitz-slot-value gf 'method-combination))
  (defun (setf generic-function-method-combination) (new-value gf)
    (setf (movitz-slot-value gf 'method-combination) new-value))
  
  (defun generic-function-discriminating-function (gf)
    (slot-value gf 'movitz::standard-gf-function))
  (defun (setf generic-function-discriminating-function) (new-value gf)
    (setf (slot-value gf 'movitz::standard-gf-function) new-value))

  (defun generic-function-method-class (gf)
    (movitz-slot-value gf 'method-class))
  (defun (setf generic-function-method-class) (new-value gf)
    (setf (movitz-slot-value gf 'method-class) new-value))

;;;  accessor for effective method function table

  (defun classes-to-emf-table (gf)
    (slot-value gf 'movitz::classes-to-emf-table)
    #+ignore (movitz-slot-value gf 'classes-to-emf-table))
  (defun (setf classes-to-emf-table) (new-value gf)
    (setf (slot-value gf 'movitz::classes-to-emf-table) new-value)
    #+ignore (setf (movitz-slot-value gf 'classes-to-emf-table) new-value))
  (defun num-required-arguments (gf)
    (slot-value gf 'movitz::num-required-arguments))
  
;;;
;;; Method metaobjects and standard-method
;;;

  ;; (defvar *the-class-standard-method*)	;standard-method's class metaobject

  (defun method-lambda-list (method)
    (movitz-slot-value method 'lambda-list))
  (defun (setf method-lambda-list) (new-value method)
    (setf (movitz-slot-value method 'lambda-list) new-value))

  (defun movitz-method-qualifiers (method)
    (movitz-slot-value method 'qualifiers))
  (defun (setf movitz-method-qualifiers) (new-value method)
    (setf (movitz-slot-value method 'qualifiers) new-value))

  (defun method-specializers (method)
    (movitz-slot-value method 'specializers))
  (defun (setf method-specializers) (new-value method)
    (setf (movitz-slot-value method 'specializers) new-value))

  (defun method-body (method)
    (movitz-slot-value method 'body))
  (defun (setf method-body) (new-value method)
    (setf (movitz-slot-value method 'body) new-value))

  (defun method-declarations (method)
    (movitz-slot-value method 'declarations))
  (defun (setf method-declarations) (new-value method)
    (setf (movitz-slot-value method 'declarations) new-value))

  (defun method-environment (method)
    (movitz-slot-value method 'environment))
  (defun (setf method-environment) (new-value method)
    (setf (movitz-slot-value method 'environment) new-value))

  (defun method-generic-function (method)
    (movitz-slot-value method 'generic-function))
  (defun (setf method-generic-function) (new-value method)
    (setf (movitz-slot-value method 'generic-function) new-value))

  (defun method-function (method) (movitz-slot-value method 'function))
  (defun (setf method-function) (new-value method)
    (setf (movitz-slot-value method 'function) new-value))

  (defun method-optional-arguments-p (method) (movitz-slot-value method 'optional-arguments-p))
  (defun (setf method-optional-arguments-p) (new-value method)
    (setf (movitz-slot-value method 'optional-arguments-p) new-value))
  
;;; defgeneric

  (defmacro movitz-defgeneric (function-name lambda-list &rest options)
    `(movitz-ensure-generic-function ',function-name 
				  :lambda-list ',lambda-list
				  ,@(canonicalize-defgeneric-options options)))

  (defun canonicalize-defgeneric-options (options)
    (mapappend #'canonicalize-defgeneric-option options))

  (defun canonicalize-defgeneric-option (option)
    (case (car option)
      (declare nil)
      (:generic-function-class
       (list ':generic-function-class
	     `(movitz-find-class ',(cadr option))))
      (:method-class
       (list ':method-class
	     `(movitz-find-class ',(cadr option))))
      (:method nil)
      (t (list `',(car option) `',(cadr option)))))

;;; ensure-generic-function

  (defun movitz-ensure-generic-function (function-name &rest all-keys
				      &key (generic-function-class (movitz-find-class 'standard-generic-function))
					   lambda-list (no-clos-fallback nil ncf-p)
					   (method-class (movitz-find-class 'standard-method))
				      &allow-other-keys)
    (declare (dynamic-extent all-keys))
    (let ((function-name (muerte::translate-program function-name :cl :muerte.cl))
	  (remove-old-p nil))
      (let ((gf (movitz::movitz-env-named-function function-name)))
	(with-simple-restart (nil "Remove the old definition for ~S." function-name)
	  (when gf
	    (assert (typep gf 'movitz::movitz-funobj-standard-gf) ()
	      "There is already a non-generic function-definition for ~S of type ~S."
	      function-name (type-of gf))
	    (assert (= (length (getf (analyze-lambda-list lambda-list)
				     :required-args))
		       (num-required-arguments gf))
		() "The lambda-list ~S doesn't match the old generic function's lambda-list ~S."
		lambda-list (generic-function-lambda-list gf))))
	(when (and gf (or (not (typep gf 'movitz::movitz-funobj-standard-gf))
			  (not (= (length (getf (analyze-lambda-list lambda-list)
						:required-args))
				  (num-required-arguments gf)))))
	  (setf remove-old-p t)))
      (let ((gf (or (and (not remove-old-p)
			 (movitz::movitz-env-named-function function-name))
		    (let ((gf (apply (if (eq generic-function-class
					     (movitz-find-class 'standard-generic-function))
					 #'make-instance-standard-generic-function
				       #'movitz-make-instance)
				     generic-function-class
				     :name function-name
				     :method-class method-class
				     (muerte::translate-program all-keys :cl :muerte.cl))))
		      (setf (movitz::movitz-env-named-function function-name) gf)
		      gf))))
	(when ncf-p
	  (setf (getf (slot-value gf 'movitz::plist) :no-clos-fallback)
	    no-clos-fallback)
	  (finalize-generic-function gf))
	gf)))

;;; finalize-generic-function

;;; N.B. Same basic idea as finalize-inheritance.  Takes care of recomputing
;;; and storing the discriminating function, and clearing the effective method
;;; function table.

  (defun finalize-generic-function (gf)
    (setf (movitz::movitz-env-named-function (generic-function-name gf)) gf)
    (setf (classes-to-emf-table gf) nil)
    (setf (movitz::standard-gf-function gf)
      'initial-discriminating-function)
    (let ((ncf (getf (slot-value gf 'movitz::plist) :no-clos-fallback)))
      (cond
       ((not ncf))
       ((member ncf '(:unspecialized-method t))
	(let ((m (find-if (lambda (method)
			    (every (lambda (specializer)
				     (eq specializer
					 (movitz-find-class t)))
				   (method-specializers method)))
			  (generic-function-methods gf))))
	  (setf (classes-to-emf-table gf)
	    (if m (method-function m) 'no-unspecialized-fallback))))
       ((symbolp ncf)
	(setf (classes-to-emf-table gf)
	  ncf))
       ((and (listp ncf) (eq 'muerte.cl:setf (car ncf)))
	(setf (classes-to-emf-table gf)
	  (movitz::movitz-env-setf-operator-name (cadr ncf))))
       (t (error "Unknown ncf."))))
    #+ignore
    (let ((eql-specializer-table (or (slot-value gf 'movitz::eql-specializer-table)
				     (make-hash-table :test #'eql))))
      (clrhash eql-specializer-table)
      (dolist (method (generic-function-methods gf))
	(dolist (specializer (method-specializers method))
	  (when (eq (movitz-find-class 'eql-specializer)
		    (movitz-class-of specializer))
	    (setf (gethash (movitz-slot-value specializer 'object)
			   eql-specializer-table)
	      specializer))))
      (setf (slot-value gf 'movitz::eql-specializer-table)
	(if (plusp (hash-table-count eql-specializer-table))
	    eql-specializer-table
	  nil)))
    (values))

;;; make-instance-standard-generic-function creates and initializes an
;;; instance of standard-generic-function without falling into method lookup.
;;; However, it cannot be called until standard-generic-function exists.

  (defun make-instance-standard-generic-function (generic-function-class
						  &key name lambda-list method-class method-combination
						       no-clos-fallback
						       documentation)
    (declare (ignore documentation no-clos-fallback method-combination))
    (assert (not (null lambda-list)) (lambda-list)
      "Can't make a generic function with nil lambda-list.")
    (let ((gf (std-allocate-gf-instance generic-function-class
					:name name
					:lambda-list lambda-list
					:num-required-arguments
					(length (getf (analyze-lambda-list lambda-list)
						      :required-args)))))
      (setf (generic-function-name gf) name
	    (generic-function-lambda-list gf) lambda-list
	    (generic-function-methods gf) ()
	    (generic-function-method-class gf) method-class
	    (generic-function-method-combination gf) *the-standard-method-combination*)
      (finalize-generic-function gf)
      gf))


;;; defmethod

  (defmacro movitz-defmethod (&rest args)
    (multiple-value-bind (function-name qualifiers lambda-list specializers body declarations documentation)
	(parse-defmethod args)
      (declare (ignore documentation declarations body))
      `(ensure-method (movitz::movitz-env-named-function ',function-name)
		      :lambda-list ',lambda-list
		      :qualifiers ',qualifiers
		      :specializers ,(canonicalize-specializers specializers) 
		      ;; :body ',body
		      ;; :declarations ',declarations
		      ;; :environment ,env)))
		      )))

  (defun canonicalize-specializers (specializers)
    `(list ,@(mapcar #'canonicalize-specializer specializers)))

  (defun canonicalize-specializer (specializer)
    `(find-specializer ',specializer))

  (defun parse-defmethod (args)
    (let ((fn-spec (car args))
	  (qualifiers ())
	  (specialized-lambda-list nil)
	  (decl-doc-body ())
	  (parse-state :qualifiers))
      (dolist (arg (cdr args))
	(ecase parse-state
	  (:qualifiers
	   (if (and (atom arg) (not (null arg)))
	       (push-on-end arg qualifiers)
	     (progn (setq specialized-lambda-list arg)
		    (setq parse-state :body))))
	  (:body (push-on-end arg decl-doc-body))))
      (multiple-value-bind (body declarations documentation)
	  (movitz::parse-docstring-declarations-and-body decl-doc-body 'cl:declare)
	(values fn-spec 
		qualifiers
		(extract-lambda-list specialized-lambda-list)
		(extract-specializers specialized-lambda-list)
		(list* 'block
		       (if (consp fn-spec)
			   (cadr fn-spec)
			 fn-spec)
		       body)
		declarations
		documentation))))

;;; Several tedious functions for analyzing lambda lists

  (defun required-portion (gf args)
    (let ((number-required (length (gf-required-arglist gf))))
      (when (< (length args) number-required)
	(error "Closette compiler: Too few arguments to generic function ~S." gf))
      (subseq args 0 number-required)))

  (defun gf-required-arglist (gf)
    (let ((plist (analyze-lambda-list (generic-function-lambda-list gf))))
      (getf plist ':required-args)))

  (defun extract-lambda-list (specialized-lambda-list)
    (let* ((plist (analyze-lambda-list specialized-lambda-list))
	   (requireds (getf plist ':required-names))
	   (rv (getf plist ':rest-var))
	   (ks (getf plist ':key-args))
	   (aok (getf plist ':allow-other-keys))
	   (opts (getf plist ':optional-args))
	   (auxs (getf plist ':auxiliary-args)))
      `(,@requireds 
	,@(if rv `(&rest ,rv) ())
	,@(if (or ks aok) `(&key ,@ks) ())
	,@(if aok '(&allow-other-keys) ())
	,@(if opts `(&optional ,@opts) ())
	,@(if auxs `(&aux ,@auxs) ()))))

  (defun extract-specializers (specialized-lambda-list)
    (let ((plist (analyze-lambda-list specialized-lambda-list)))
      (getf plist ':specializers)))

  (defun analyze-lambda-list (lambda-list)
    (labels ((make-keyword (symbol)
	       (intern (symbol-name symbol)
		       (find-package 'keyword)))
	     (get-keyword-from-arg (arg)
	       (if (listp arg)
		   (if (listp (car arg))
		       (caar arg)
		     (make-keyword (car arg)))
		 (make-keyword arg))))
      (let ((keys ())			; Just the keywords
	    (key-args ())		; Keywords argument specs
	    (required-names ())		; Just the variable names
	    (required-args ())		; Variable names & specializers
	    (specializers ())		; Just the specializers
	    (rest-var nil)
	    (optionals ())
	    (auxs ())
	    (allow-other-keys nil)
	    (state :parsing-required))
	(dolist (arg (translate-program lambda-list :muerte.cl :cl))
	  (if (member arg lambda-list-keywords)
	      (ecase arg
		(&optional
		 (setq state :parsing-optional))
		(&rest
		 (setq state :parsing-rest))
		(&key
		 (setq state :parsing-key))
		(&allow-other-keys
		 (setq allow-other-keys 't))
		(&aux
		 (setq state :parsing-aux)))
	    (case state
	      (:parsing-required 
	       (push-on-end arg required-args)
	       (if (listp arg)
		   (progn (push-on-end (car arg) required-names)
			  (push-on-end (cadr arg) specializers))
		 (progn (push-on-end arg required-names)
			(push-on-end 't specializers))))
	      (:parsing-optional (push-on-end arg optionals))
	      (:parsing-rest (setq rest-var arg))
	      (:parsing-key
	       (push-on-end (get-keyword-from-arg arg) keys)
	       (push-on-end arg key-args))
	      (:parsing-aux (push-on-end arg auxs)))))
	(translate-program (list :required-names required-names
				 :required-args required-args
				 :specializers specializers
				 :rest-var rest-var
				 :keywords keys
				 :key-args key-args
				 :auxiliary-args auxs
				 :optional-args optionals
				 :allow-other-keys allow-other-keys)
			   :cl :muerte.cl))))

;;; ensure method

  (defun ensure-method (gf &rest all-keys &key lambda-list &allow-other-keys)
    (declare (dynamic-extent all-keys))
    (assert (= (length (getf (analyze-lambda-list lambda-list)
			     :required-args))
	       (num-required-arguments gf))
	() "The method's lambda-list ~S doesn't match the gf's lambda-list ~S."
	lambda-list (generic-function-lambda-list gf))
    (let ((new-method (apply (if (eq (generic-function-method-class gf)
				     (movitz-find-class 'standard-method))
				 #'make-instance-standard-method 
			       #'make-instance)
			     gf
			     :name (generic-function-name gf)
			     all-keys)))
      (movitz-add-method gf new-method)
      new-method))

;;; make-instance-standard-method creates and initializes an instance of
;;; standard-method without falling into method lookup.  However, it cannot
;;; be called until standard-method exists.

  (defun make-instance-standard-method (gf &key (method-class 'standard-method) name lambda-list qualifiers
						specializers body declarations environment slot-definition)
    (let ((method (std-allocate-instance (movitz-find-class method-class))))
      (setf ;; (method-lambda-list method) lambda-list
	    (movitz-method-qualifiers method) qualifiers
	    (method-specializers method) specializers
;;;	    (method-body method) body
;;;	    (method-declarations method) declarations
	    (method-generic-function method) nil
	    (method-optional-arguments-p method) (let ((analysis (analyze-lambda-list lambda-list)))
						   (if (or (getf analysis :optional-args)
							   (getf analysis :key-args)
							   (getf analysis :rest-var))
						       t nil))
	    (method-function method) (std-compute-method-function method name gf environment
								  lambda-list declarations body))
      (when slot-definition
	(setf (movitz-slot-value method 'slot-definition) slot-definition))
      method))

;;; add-method

;;; N.B. This version first removes any existing method on the generic function
;;; with the same qualifiers and specializers.  It's a pain to develop
;;; programs without this feature of full CLOS.

  (defun movitz-add-method (gf method)
    (let ((old-method (movitz-find-method gf (movitz-method-qualifiers method)
				       (method-specializers method) nil)))
      (when old-method (movitz-remove-method gf old-method)))
    (setf (method-generic-function method) gf)
    (push method (generic-function-methods gf))
    (dolist (specializer (method-specializers method))
      (when (subclassp (movitz-class-of specializer) (movitz-find-class 'class))
	(pushnew method (class-direct-methods specializer))))
    (finalize-generic-function gf)
    method)

  (defun movitz-remove-method (gf method)
    (setf (generic-function-methods gf)
      (remove method (generic-function-methods gf)))
    (setf (method-generic-function method) nil)
    (dolist (specializer (method-specializers method))
      (when (subclassp (movitz-class-of specializer) (movitz-find-class 'class))
	(setf (class-direct-methods specializer)
	  (remove method (class-direct-methods specializer)))))
    (finalize-generic-function gf)
    method)

  (defun movitz-find-method (gf qualifiers specializers &optional (errorp t))
    (let ((method (find-if (lambda (method)
			     (and (equal qualifiers
					 (movitz-method-qualifiers method))
				  (equal specializers
					 (method-specializers method))))
			   (generic-function-methods gf))))
      (if (and (null method) errorp)
	  (error "Closette compiler: No method for ~S matching ~S~@[ qualifiers ~S~]."
		 (generic-function-name gf)
		 specializers
		 qualifiers)
	method)))

;;; Reader and write methods

  (defun add-reader-method (class fn-name slot-name)
    (ensure-method (movitz-ensure-generic-function fn-name :lambda-list '(object))
		   :method-class 'standard-reader-method
		   :slot-definition (find slot-name (std-slot-value class 'direct-slots)
					  :key 'slot-definition-name)
		   :lambda-list '(object)
		   :qualifiers ()
		   :specializers (list class)
		   :body `(slot-value object ',slot-name) ; this is LOS code!
		   :environment (top-level-environment))
    (values))

  (defun add-writer-method (class fn-name slot-name)
    (ensure-method (movitz-ensure-generic-function fn-name :lambda-list '(new-value object))
		   :method-class 'standard-writer-method
		   :lambda-list '(new-value object)
		   :slot-definition (find slot-name (std-slot-value class 'direct-slots)
					  :key 'slot-definition-name)
		   :qualifiers ()
		   :specializers (list (movitz-find-class 't) class)
		   :body `(setf (slot-value object ',slot-name) ; this is LOS code!
			    new-value)
		   :environment (top-level-environment))
    (values))

;;;
;;; Generic function invocation
;;;

;;; apply-generic-function

  (defun apply-generic-function (gf args)
    (apply (generic-function-discriminating-function gf) args))

;;; compute-discriminating-function

  (defun std-compute-discriminating-function (gf)
    (declare (ignore gf))
    'discriminating-function
    #+ignore
    (movitz::make-compiled-funobj 'discriminating-function
				(muerte::translate-program
				 '(&edx gf &rest args) :cl :muerte.cl)
				(muerte::translate-program
				 '((dynamic-extent args)) :cl :muerte.cl)
				(muerte::translate-program
				 `(apply #'std-discriminating-function gf args args)
				 #+ignore
				 `(let* ((requireds (subseq args 0 (length (gf-required-arglist ,gf))))
					 (classes (map-into requireds #'class-of requireds))
					 (emfun (gethash classes (classes-to-emf-table ,gf) nil)))
				    (if emfun
					(funcall emfun args)
				      (slow-method-lookup ,gf args classes)))
				 #+ignore
				 `(let ((requireds (subseq args 0 (length (gf-required-arglist ,gf)))))
				    (slow-method-lookup ,gf args (map-into requireds #'class-of requireds)))
				 :cl :muerte.cl)
				nil nil))
  
  (defun slow-method-lookup (gf args classes)
    (let* ((applicable-methods (compute-applicable-methods-using-classes gf classes))
	   (emfun (funcall (if (eq (movitz-class-of gf) (movitz-find-class 'standard-generic-function))
			       #'std-compute-effective-method-function
			     #'compute-effective-method-function)
			   gf applicable-methods)))
      (setf (gethash classes (classes-to-emf-table gf)) emfun)
      (funcall emfun args)))

;;; compute-applicable-methods-using-classes

  (defun compute-applicable-methods-using-classes (gf required-classes)
    (sort (copy-list (remove-if-not #'(lambda (method)
					(every #'subclassp
					       required-classes
					       (method-specializers method)))
				    (generic-function-methods gf)))
	  (lambda (m1 m2) 
	    (funcall (if (eq (movitz-class-of gf) (movitz-find-class 'standard-generic-function))
			 #'std-method-more-specific-p
		       #'method-more-specific-p)
		     gf m1 m2 required-classes))))

;;; method-more-specific-p

  (defun std-method-more-specific-p (gf method1 method2 required-classes)
    "When applying arguments of <required-classes> to <gf>, which of <method1>
and <method2> is more specific?"
    (declare (ignore gf))
;;;    #+movitz (loop
;;;	       for spec1 in (method-specializers method1)
;;;	       for spec2 in (method-specializers method2)
;;;	       for arg-class in required-classes
;;;	       do (unless (eq spec1 spec2)
;;;		    (return-from std-method-more-specific-p
;;;		      (sub-specializer-p spec1 spec2 arg-class))))
    (mapc #'(lambda (spec1 spec2 arg-class)
	      (unless (eq spec1 spec2)
		(return-from std-method-more-specific-p
		  (sub-specializer-p spec1 spec2 arg-class))))
	  (method-specializers method1)
	  (method-specializers method2)
	  required-classes)
    nil)

;;; apply-methods and compute-effective-method-function

  #+ignore
  (defun apply-methods (gf args methods)
    (funcall (compute-effective-method-function gf methods)
	     args))

  (defun primary-method-p (method)
    (null (movitz-method-qualifiers method)))
  (defun before-method-p (method)
    (equal '(:before) (movitz-method-qualifiers method)))
  (defun after-method-p (method)
    (equal '(:after) (movitz-method-qualifiers method)))
  (defun around-method-p (method)
    (equal '(:around) (movitz-method-qualifiers method)))

  #+ignore
  (defun std-compute-effective-method-function (gf methods)
    (let ((primaries (remove-if-not #'primary-method-p methods))
	  (around (find-if #'around-method-p methods)))
      (when (null primaries)
	(error "Closette compiler: No primary methods for the generic function ~S." gf))
      (if around
	  (let ((next-emfun (funcall (if (eq (movitz-class-of gf) (movitz-find-class 'standard-generic-function))
					 #'std-compute-effective-method-function
				       #'compute-effective-method-function)
				     gf (remove around methods))))
	    `(lambda (args)
	      (funcall (method-function ,around) args ,next-emfun)))
	(let ((next-emfun (compute-primary-emfun (cdr primaries)))
	      (befores (remove-if-not #'before-method-p methods))
	      (reverse-afters
	       (reverse (remove-if-not #'after-method-p methods))))
	  `(lambda (args)        
	     (dolist (before ',befores)
	       (funcall (method-function before) args nil))
	     (multiple-value-prog1
		 (funcall (method-function ,(car primaries)) args ,next-emfun)
	       (dolist (after ',reverse-afters)
		 (funcall (method-function after) args nil))))))))

;;; compute an effective method function from a list of primary methods:

  #+ignore
  (defun compute-primary-emfun (methods)
    (if (null methods)
	nil
      (let ((next-emfun (compute-primary-emfun (cdr methods))))
	'(lambda (args)
	  (funcall (method-function (car methods)) args next-emfun)))))

;;; apply-method and compute-method-function

  #+ignore
  (defun apply-method (method args next-methods)
    (funcall (method-function method)
	     args
	     (if (null next-methods)
		 nil
	       (compute-effective-method-function
		(method-generic-function method) next-methods))))

  (defun std-compute-method-function (method name gf env lambda-list declarations body)
    (let* ((block-name (compute-function-block-name name))
	   (analysis (analyze-lambda-list lambda-list))
	   (lambda-variables (append (getf analysis :required-args)
				     (mapcar #'decode-optional-formal
					     (getf analysis :optional-args))
				     (mapcar #'decode-keyword-formal
					     (getf analysis :key-args))
				     (when (getf analysis :rest-var)
				       (list (getf analysis :rest-var)))))
	   (required-variables (subseq lambda-variables
				       0 (num-required-arguments gf)))
	   (funobj
	    (compile-in-lexical-environment
	     env
	     (translate-program (nconc (list 'method name)
				       (copy-list (movitz-method-qualifiers method))
				       (list (mapcar #'specializer-name (method-specializers method))))
				:cl :muerte.cl)
	     (if (movitz::tree-search body '(call-next-method next-method-p))
		 `(lambda ,lambda-list
		    (declare (ignorable ,@required-variables)
			     ,@(mapcan (lambda (declaration)
					 (case (car declaration)
					   (dynamic-extent
					    (list declaration))
					   (ignore
					    (list (cons 'ignorable (cdr declaration))))))
				       declarations))
		    (let ((next-emf 'proto-next-emf))
		      ;; We must capture the value of the dynamic *next-methods*
		      (declare (ignorable next-emf))
		      ;; this is an ugly hack so next-emf wont be a constant-binding..
		      (setf next-emf 'proto-next-emf)
		      (flet ((call-next-method (&rest cnm-args)
			       (declare (dynamic-extent cnm-args))
			       ;; XXX &key args not handled.
			       (if (not (functionp next-emf))
				   (if cnm-args
				       (apply 'no-next-method ,gf ,method cnm-args)
				     (no-next-method ,gf ,method ,@lambda-variables))
				 (if cnm-args
				     (apply next-emf cnm-args)
				   (funcall next-emf ,@lambda-variables)))))
			(declare (ignorable call-next-method))
			(block ,block-name
			  (let ,(mapcar #'list lambda-variables lambda-variables)
			    (declare (ignorable ,@required-variables)
				     ,@declarations)
			    ,body)))))
	       `(lambda ,lambda-list
		  (declare (ignorable ,@required-variables)
			   ,@declarations)
		  (block ,block-name
		    ,body))))))
      (setf (slot-value funobj 'movitz::funobj-type) :method-function)
      funobj))
	      

;;; N.B. The function kludge-arglist is used to pave over the differences
;;; between argument keyword compatibility for regular functions versus 
;;; generic functions.

  (defun kludge-arglist (lambda-list)
    (if (and (member '&key lambda-list)
	     (not (member '&allow-other-keys lambda-list)))
	(append lambda-list '(&allow-other-keys))
      (if (and (not (member '&rest lambda-list))
	       (not (member '&key lambda-list)))
	  (append lambda-list '(&key &allow-other-keys))
	lambda-list)))

;;; Run-time environment hacking (Common Lisp ain't got 'em).

  (defun top-level-environment ()
    nil)				; Bogus top level lexical environment

  (defun compile-in-lexical-environment (env name lambda-expr)
    (declare (ignore env))
    ;; (warn "lambda: ~W" lambda-expr)
    (destructuring-bind (operator lambda-list &body decl-doc-body)
	lambda-expr
      (assert (eq 'lambda operator) (lambda-expr)
	"Closette compiler: Lambda wasn't lambda.")
      (multiple-value-bind (body declarations)
	  (movitz::parse-docstring-declarations-and-body decl-doc-body 'cl:declare)
	(movitz::make-compiled-funobj name
				      (translate-program lambda-list :cl :muerte.cl)
				      (translate-program declarations :cl :muerte.cl)
				      (translate-program (cons 'muerte.cl:progn body) :cl :muerte.cl)
				      nil nil))))
  
;;;
;;; Bootstrap
;;;

  (defun bootstrap-closette ()
    ;; (format t "~&;; Beginning to bootstrap Closette...~%")
    (setf *classes-with-old-slot-definitions* nil)
    (forget-all-classes)
;;;(forget-all-generic-functions)

    ;; How to create the class hierarchy in 10 easy steps:
    ;; 1. Figure out standard-class's slots.
    (setq *the-slots-of-standard-class*
      (mapcar (lambda (slotd)
		(make-effective-slot-definition
		 (movitz::translate-program 'standard-class :cl :muerte.cl)
		 :name (car slotd)
		 :initargs (let ((a (getf (cdr slotd) :initarg)))
			     (if a (list a) ()))
		 :initform (getf (cdr slotd) :initform)
		 :initfunction (getf (cdr slotd) :initform)
		 :allocation :instance))
	      (append (nth 3 +the-defclass-class+) ; slots inherited from "class"
		      (nth 3 +the-defclass-std-slotted-class+) ; slots inherited from "std-slotted-class"
		      (nth 3 +the-defclass-instance-slotted-class+) ; ..
		      (nth 3 +the-defclass-standard-class+))))
    (loop for s in *the-slots-of-standard-class* as i upfrom 0
	do (setf (slot-definition-location s) i))
    (setq *the-position-of-standard-effective-slots*
      (position 'effective-slots *the-slots-of-standard-class*
		:key #'slot-definition-name))
    ;; 2. Create the standard-class metaobject by hand.
    (setq *the-class-standard-class*
      (allocate-std-instance 'tba (make-array (length *the-slots-of-standard-class*)
					      :initial-element (movitz::unbound-value))))
    ;; 3. Install standard-class's (circular) class-of link. 
    (setf (std-instance-class *the-class-standard-class*) 
      *the-class-standard-class*)
    ;; (It's now okay to use class-... accessor).
    ;; 4. Fill in standard-class's class-slots.
    (setf (class-slots *the-class-standard-class*) *the-slots-of-standard-class*)
    ;; (Skeleton built; it's now okay to call make-instance-standard-class.)
    ;; 5. Hand build the class t so that it has no direct superclasses.
    (setf (movitz-find-class 't) 
      (let ((class (std-allocate-instance *the-class-standard-class*)))
	(setf (movitz-class-name class) 't)
	(setf (class-direct-subclasses class) ())
	(setf (class-direct-superclasses class) ())
	(setf (class-direct-methods class) ())
	(setf (class-direct-slots class) ())
	(setf (class-precedence-list class) (list class))
	(setf (class-slots class) ())
	(setf (class-direct-methods class) nil)
	class))
    ;; (It's now okay to define subclasses of t.)
    ;; 6. Create the other superclass of standard-class (i.e., standard-object).
    (defclass-los standard-object (t) ())
    ;; 7. Define the full-blown version of class and standard-class.
    ;; (warn "step 7...")
    (eval +the-defclasses-before-class+)
    (eval +the-defclass-class+)		; Create the class class.
    (eval +the-defclass-std-slotted-class+)
    (eval +the-defclass-instance-slotted-class+)
    (eval +the-defclass-standard-class+) ; Re-create the standard-class..
    (setf (std-instance-slots *the-class-standard-class*) ; ..and copy it into the old standard-class..
      (std-instance-slots (movitz-find-class 'standard-class))) ; (keeping it's identity intact.)
    (setf (movitz-find-class 'standard-class)
      *the-class-standard-class*)
    (setf (class-precedence-list *the-class-standard-class*)
      (std-compute-class-precedence-list *the-class-standard-class*))
    
    ;; 8. Replace all (x..) existing pointers to the skeleton with real one.
    ;; Not necessary because we kept standard-class's identity by the above.

    ;; Define the built-in-class..
    (defclass-los built-in-class (class)
      ((size :initarg :size)
       (slot-map :initarg :slot-map)))
    ;; Change t to be a built-in-class..
    (let ((t-prototype (make-instance-built-in-class 'built-in-class :name t :direct-superclasses nil)))
      ;; both class and slots of t-prototype are copied into the old t metaclass instance,
      ;; so that object's identity is preserved.
      (setf (std-instance-class (movitz-find-class t)) (std-instance-class t-prototype)
	    (std-instance-slots (movitz-find-class t)) (std-instance-slots t-prototype)
	    (class-precedence-list (movitz-find-class t)) (std-compute-class-precedence-list (movitz-find-class t))))
    
    (eval +the-defclasses-slots+)
    (eval +the-defclass-standard-direct-slot-definition+)
    
    ;; (warn "classes with old defs: ~S" *classes-with-old-slot-definitions*)
    (dolist (class-name *classes-with-old-slot-definitions*)
      (let ((class (movitz-find-class class-name)))
	(setf (std-slot-value class 'direct-slots)
	  (mapcar #'translate-direct-slot-definition
		  (std-slot-value class 'direct-slots)))
	(setf (std-slot-value class 'effective-slots)
	  (loop for position upfrom 0
	      as slot in (std-slot-value class 'effective-slots)
	      as slot-name = (slot-definition-name slot)
	      do (if (slot-definition-location slot)
		     (assert (= (slot-definition-location slot) position))
		   (setf (slot-definition-location slot) position))
	      collect (translate-effective-slot-definition slot)
;;;	      do (warn "setting ~S ~S to ~S" class-name slot-name position)
	      do (setf (movitz::movitz-env-get class-name slot-name) position)))))
    (map-into *the-slots-of-standard-class*
	      #'translate-effective-slot-definition
	      *the-slots-of-standard-class*)
    #+ignore (format t "~&;; Closette bootstrap completed."))


    ;; (Clear sailing from here on in).
    ;; 9. Define the other built-in classes.
;;;  (defclass-los symbol (t) () (:metaclass built-in-class))
;;;  (defclass-los sequence (t) () (:metaclass built-in-class))
;;;  (defclass-los array (t) () (:metaclass built-in-class))
;;;  (defclass-los number (t) () (:metaclass built-in-class))
;;;  (defclass-los character (t) () (:metaclass built-in-class))
;;;  (defclass-los function (t) () (:metaclass built-in-class))
;;;  (defclass-los hash-table (t) () (:metaclass built-in-class))
;;;;;;  (defclass-los package (t) () (:metaclass built-in-class))
;;;;;;  (defclass-los pathname (t) () (:metaclass built-in-class))
;;;;;;  (defclass-los readtable (t) () (:metaclass built-in-class))
;;;;;;  (defclass-los stream (t) () (:metaclass built-in-class))
;;;  (defclass-los list (sequence) () (:metaclass built-in-class))
;;;  (defclass-los null (symbol list) () (:metaclass built-in-class))
;;;  (defclass-los cons (list) () (:metaclass built-in-class))
;;;  (defclass-los vector (array sequence) () (:metaclass built-in-class))
;;;  (defclass-los bit-vector (vector) () (:metaclass built-in-class))
;;;  (defclass-los string (vector) () (:metaclass built-in-class))
;;;  (defclass-los complex (number) () (:metaclass built-in-class))
;;;  (defclass-los integer (number) () (:metaclass built-in-class))
;;;  (defclass-los float (number) () (:metaclass built-in-class))
;;;  ;; 10. Define the other standard metaobject classes.
;;;  (setq *the-class-standard-gf* (eval *the-defclass-standard-generic-function*))
;;;  (setq *the-class-standard-method* (eval *the-defclass-standard-method*))
;;;  ;; Voila! The class hierarchy is in place.
;;;  (format t "Class hierarchy created.")
;;;  ;; (It's now okay to define generic functions and methods.)

;;    (setq *the-class-standard-method* (eval +the-defclass-standard-method+)))
  
  (when (zerop (hash-table-count *class-table*))
    (bootstrap-closette)))
