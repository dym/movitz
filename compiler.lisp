;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001,2000, 2002-2004,
;;;;    Department of Computer Science, University of Tromsø, Norway
;;;; 
;;;; Description:   A simple lisp compiler.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Oct 25 12:30:49 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: compiler.lisp,v 1.2 2004/01/15 16:38:52 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defvar *warn-function-change-p* t)
(defvar *explain-peephole-optimizations* nil)

(defvar *compiler-do-optimize* t)
(defvar *compiler-use-cmov-p* nil)
(defvar *compiler-auto-stack-checks-p* nil)
(defvar *compiler-allow-transients* t
  "Allow the compiler to keep function arguments solely in registers.
Hurst debugging, improves performance.")
(defvar *compiler-local-segment-prefix* '(:fs-override))
(defvar *compiler-global-segment-prefix* nil)
(defvar *compiler-compile-eval-whens* t)
(defvar *compiler-compile-macro-expanders* t)

(defvar *compiling-function-name*)

(defun duplicatesp (list)
  "Returns TRUE iff at least one object occurs more than once in LIST."
  (if (null list)
      nil
    (or (member (car list) (cdr list))
	(duplicatesp (cdr list)))))

(defun make-compiled-primitive (form environment top-level-p docstring)
  "Primitive functions have no funobj, no stack-frame, and no implied
   parameter/return value passing conventions."
  (declare (ignore top-level-p docstring))
  (let* ((env (make-local-movitz-environment environment nil))
	 (body-code (compiler-call #'compile-form
		      :form form
		      :funobj nil
		      :env env
		      :top-level-p nil
		      :result-mode :ignore))
	 ;; (ignmore (format t "~{~S~%~}" body-code))
	 (resolved-code (finalize-code body-code nil nil))
	 (function-code (ia-x86:read-proglist resolved-code))
	 (code-vector (ia-x86:proglist-encode :octet-vector
					      :32-bit
					      #x00000000
					      function-code
					      :symtab-lookup
					      #'(lambda (label)
						  (case label
						    (:nil-value (image-nil-word *image*)))))))
    (make-movitz-vector (length code-vector)
		     :element-type 'movitz-code
		     :flags '(:code-vector-p)
		     :alignment 16
		     :alignment-offset 8
		     :initial-contents code-vector)))

(defun register-function-code-size (funobj)
  (let* ((name (movitz-print (movitz-funobj-name funobj)))
	 (hash-name name)
	 (new-size (length (movitz-vector-symbolic-data (movitz-funobj-code-vector funobj)))))
    (let ((old-size (gethash hash-name (function-code-sizes *image*))))
      (cond
       ((not old-size))
       ((eq name :anonymous-lambda))
       ((not *warn-function-change-p*))
       ((> new-size old-size)
	(warn "~S grew from ~D to ~D bytes." name old-size new-size))
       ((< new-size old-size)
	(warn "~S shrunk from ~D to ~D bytes" name old-size new-size))))
    (setf (gethash hash-name (function-code-sizes *image*)) new-size))
  funobj)

(defconstant +code-vector-entry-factor+ 1)

(defclass movitz-funobj-pass1 (movitz-heap-object)
  ((name
    :initarg :name
    :accessor movitz-funobj-name)
   (lambda-list
    :initarg :lambda-list
    :accessor movitz-funobj-lambda-list)
   (function-envs
    :accessor function-envs)
   (funobj-env
    :initarg :funobj-env
    :accessor funobj-env)
   (body-compiler-values
    :accessor body-compiler-values))
  (:documentation "This class is used for funobjs during the first compiler pass.
Before the second pass, such objects will be change-class-ed to proper movitz-funobjs.
This way, we ensure that no undue side-effects on the funobj occur during pass 1."))

(defmethod print-object ((object movitz-funobj-pass1) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (when (slot-boundp object 'name)
      (write (movitz-funobj-name object) :stream stream)))
  object)

(defun movitz-macro-expander-make-function (lambda-form
				       &key (name (gensym "macro-expander-"))
					    (type :unknown))
  "Make a lambda-form that is a macro-expander into a proper function."
  (declare (ignore type))
  (check-type name symbol)
  (if *compiler-compile-macro-expanders*
      (compile name lambda-form)
    (coerce lambda-form 'function)))

(defun make-compiled-funobj (&rest args)
  (handler-bind (((or warning error)
		  (lambda (c)
		    (declare (ignore c))
		    (if (not (boundp 'muerte.cl:*compile-file-pathname*))
			(format *error-output*
				"~&;; While Movitz compiling ~S:"
				(car args))
		      (format *error-output*
			      "~&;; While Movitz compiling ~S in ~A:"
			      (car args) muerte.cl:*compile-file-pathname*)))))
    (register-function-code-size
     (make-compiled-funobj-pass2 (apply #'make-compiled-funobj-pass1 args)))))

(defun make-compiled-funobj-pass1 (name lambda-list declarations form env top-level-p
				   &key funobj)
  "Entry-point for first-pass compilation."
  (with-retries-until-true (retry-pass1 "Retry first-pass compilation of ~S." name)
    ;; First-pass is mostly functional, so it can safely be restarted.
    (funcall (cond
	      ((let ((sub-form (cddr form)))
		 (and (consp (car sub-form))
		      (eq 'muerte::numargs-case (caar sub-form))))
	       'make-compiled-function-pass1-numarg-case)
	      (t 'make-compiled-function-pass1))
	     name lambda-list declarations form env top-level-p :funobj funobj)))

(defun make-compiled-function-pass1-numarg-case (name lambda-list declarations form env top-level-p
						 &key funobj)
  (let* ((funobj (or funobj (make-instance 'movitz-funobj-pass1)))
	 (funobj-env (make-local-movitz-environment env funobj :type 'funobj-env)))
    (setf (movitz-funobj-name funobj) name
	  (movitz-funobj-lambda-list funobj) (movitz-read (lambda-list-simplify lambda-list))
	  (funobj-env funobj) funobj-env
	  (function-envs funobj) nil)
    (loop for (numargs lambda-list . clause-body) in (cdr (caddr form))
	do (when (duplicatesp lambda-list)
	     (error "There are duplicates in lambda-list ~S." lambda-list))
	   (multiple-value-bind (clause-body clause-declarations)
	       (parse-declarations-and-body clause-body)
	     (let ((function-env (add-bindings-from-lambda-list
				  lambda-list
				  (make-local-movitz-environment funobj-env funobj
							      :type 'function-env
							      :declaration-context :funobj
							      :declarations 
							      (append clause-declarations
								      declarations)))))
	       (make-compiled-body-pass1 funobj
					 function-env
					 (list* 'muerte.cl::block
						(compute-function-block-name name)
						clause-body)
					 top-level-p)
	       (push (cons numargs function-env)
		     (function-envs funobj)))))
    funobj))

(defun make-compiled-function-pass1 (name lambda-list declarations form env top-level-p
				     &key funobj)
  "Returns compiler-values, with the pass1 funobj as &final-form."
  (when (duplicatesp lambda-list)
    (error "There are duplicates in lambda-list ~S." lambda-list))
  (let* ((funobj (or funobj (make-instance 'movitz-funobj-pass1)))
	 (funobj-env (make-local-movitz-environment env funobj :type 'funobj-env))
	 (function-env (add-bindings-from-lambda-list
			lambda-list
			(make-local-movitz-environment funobj-env funobj
						    :type 'function-env
						    :declaration-context :funobj
						    :declarations declarations))))
    (setf (movitz-funobj-name funobj) name
	  (movitz-funobj-lambda-list funobj) (movitz-read (lambda-list-simplify lambda-list))
	  (funobj-env funobj) funobj-env
	  (function-envs funobj) (list (cons 'muerte.cl::t function-env)))
    (make-compiled-body-pass1 funobj function-env form top-level-p)))

(defun make-compiled-body-pass1 (funobj function-env form top-level-p)
  "Returns compiler-values, with the pass1 funobj as &final-form."
  (multiple-value-bind (arg-init-code body-form need-normalized-ecx-p)
      (make-function-arguments-init funobj function-env form)
    (compiler-values-bind (&code body-code)
	(compiler-call #'compile-form
	  :form body-form
	  :funobj funobj
	  :env function-env
	  :top-level-p top-level-p
	  :result-mode :function)
      (let ((extended-code (append arg-init-code body-code)))
	(setf (extended-code function-env) extended-code
	      (need-normalized-ecx-p function-env) need-normalized-ecx-p)
	funobj))))

(defun make-compiled-funobj-pass2 (funobj)
  (check-type funobj movitz-funobj-pass1)
  (complete-funobj
   (layout-stack-frames
    (analyze-bindings
     (resolve-sub-functions funobj)))))

(defun analyze-bindings (toplevel-funobj)
  (let ((bindings ()))
    (labels ((type-is-t (type-specifier)
	       (or (eq type-specifier t)
		   (and (listp type-specifier)
			(eq 'or (car type-specifier))
			(some #'type-is-t (cdr type-specifier)))))
	     (analyze-store (binding type)
	       (assert (not (null type)) ()
		 "store-lexical with empty type.")
	       (assert (or (typep type 'binding)
			   (eql 1 (type-specifier-num-values type))) ()
		 "store-lexical with multiple-valued type: ~S for ~S" type binding)
	       (pushnew binding bindings)
	       (pushnew (translate-program type :muerte.cl :cl)
			(binding-store-type binding)))
	     (analyze-code (code)
	       (dolist (instruction code)
		 (when (listp instruction)
		   (multiple-value-bind (store-binding store-type)
		       (find-written-binding-and-type instruction)
		     (when store-binding
		       (analyze-store store-binding store-type)))
		   (analyze-code (instruction-sub-program instruction)))))
	     (analyze-funobj (funobj)
	       (loop for (nil . function-env) in (function-envs funobj)
		   do (analyze-code (extended-code function-env)))
	       (loop for function-binding in (sub-function-binding-usage funobj) by #'cddr
		   do (analyze-funobj (function-binding-funobj function-binding)))
	       funobj))
      #+ignore (analyze-funobj toplevel-funobj)
      #+ignore (dolist (binding bindings)
		 (let ((types (binding-store-type binding)))
		   (unless (some #'type-is-t types)
		     (warn "binding: ~S~%      types: ~S"
			   binding types))))
      toplevel-funobj)))

(defun resolve-borrowed-bindings (toplevel-funobj)
  "For <funobj>'s code, for every non-local binding used we create
a borrowing-binding in the funobj-env. This process must be done
recursively, depth-first wrt. sub-functions. Also, return a plist
of all function-bindings seen."
  (let ((toplevel-funobj (change-class toplevel-funobj 'movitz-funobj
				       :borrowed-bindings nil))
	(function-binding-usage ()))
    (labels ((process-binding (funobj binding usages)
	       (typecase binding
		 (forwarding-binding
		  (setf (forwarding-binding-target binding)
		    (process-binding funobj (forwarding-binding-target binding) usages)))
		 (function-binding
		  (dolist (usage usages)
		    (pushnew usage
			     (getf (sub-function-binding-usage (function-binding-parent binding))
				   binding))
		    (pushnew usage (getf function-binding-usage binding)))))
	       (cond
		((typep binding 'constant-object-binding)
		 binding)
		((eq funobj (binding-funobj binding))
		 binding)
		(t #+ignore (warn "binding ~S is not local to ~S [~S])) .." binding funobj
			 (mapcar #'borrowed-binding-target (borrowed-bindings funobj)))
		 (let ((borrowing-binding
			  (or (find binding (borrowed-bindings funobj)
				    :key #'borrowed-binding-target)
			      (car (push (movitz-env-add-binding (funobj-env funobj)
							      (make-instance 'borrowed-binding
								:name (binding-name binding)
								:target-binding binding))
					 (borrowed-bindings funobj))))))
		     (pushnew borrowing-binding 
			      (getf (binding-lended-p binding) :lended-to))
		     (dolist (usage usages)
		       (pushnew usage (borrowed-binding-usage borrowing-binding)))
		     borrowing-binding))))
	     (resolve-sub-funobj (funobj sub-funobj)
	       (dolist (binding-we-lend (borrowed-bindings (resolve-funobj-borrowing sub-funobj)))
		 (process-binding funobj
				  (borrowed-binding-target binding-we-lend)
				  (borrowed-binding-usage binding-we-lend))))
	     (resolve-code (funobj code)
	       (dolist (instruction code)
		 (when (listp instruction)
		   (let ((store-binding (find-written-binding-and-type instruction)))
		     (when store-binding
		       (process-binding funobj store-binding '(:read))))
		   (let ((load-binding (find-read-bindings instruction)))
		     (when load-binding
		       (process-binding funobj load-binding '(:read))))
		   (case (car instruction)
		     (:call-lexical
		      (process-binding funobj (second instruction) '(:call)))
		     (:load-lambda
		      (let ((lambda-binding (second instruction)))
			(assert (eq funobj (binding-funobj lambda-binding)) ()
			  "A non-local lambda doesn't make sense. There must be a bug.")
			(resolve-sub-funobj funobj (function-binding-funobj lambda-binding))
			(process-binding funobj lambda-binding '(:read))
			;; This funobj is effectively using every binding that the lambda
			;; is borrowing..
			(map nil (lambda (borrowed-binding)
				   (process-binding funobj
						    (borrowed-binding-target borrowed-binding)
						    '(:read)))
			     (borrowed-bindings (function-binding-funobj lambda-binding)))))
		     (:local-function-init
		      (let ((function-binding (second instruction)))
			(assert (eq funobj (binding-funobj function-binding)) ()
			  "Initialization of a non-local function doesn't make sense.")
			(resolve-sub-funobj funobj (function-binding-funobj (second instruction)))
			(map nil (lambda (borrowed-binding)
				   (process-binding funobj
						    (borrowed-binding-target borrowed-binding)
						    '(:read)))
			     (borrowed-bindings (function-binding-funobj (second instruction)))))))
		   (resolve-code funobj (instruction-sub-program instruction)))))
	     (resolve-funobj-borrowing (funobj)
	       (let ((funobj (change-class funobj 'movitz-funobj :borrowed-bindings nil)))
		 (loop for (nil . function-env) in (function-envs funobj)
		     do (resolve-code funobj (extended-code function-env)))
		 ;; (warn "~S borrows ~S." funobj (borrowed-bindings funobj))
		 funobj)))
      (values (resolve-funobj-borrowing toplevel-funobj)
	      function-binding-usage))))

(defun resolve-sub-functions (toplevel-funobj)
  (multiple-value-bind (toplevel-funobj function-binding-usage)
      (resolve-borrowed-bindings toplevel-funobj)
    (assert (null (borrowed-bindings toplevel-funobj)) ()
      "Can't deal with toplevel closures yet.")
    (setf (movitz-funobj-extent toplevel-funobj) :indefinite-extent)
    (let ((sub-funobj-index 0))
      (loop for (function-binding usage) on function-binding-usage by #'cddr
	  do (let ((sub-funobj (function-binding-funobj function-binding)))
	       ;; (warn "USage: ~S => ~S" sub-funobj usage)
	       (case (car (movitz-funobj-name sub-funobj))
		 (:anonymous-lambda
		  (setf (movitz-funobj-name sub-funobj)
		    (list :anonymous-lambda
			  (movitz-funobj-name toplevel-funobj)
			  (post-incf sub-funobj-index)))))
	       (cond
		((or (null usage)
		     (null (borrowed-bindings sub-funobj)))
		 (change-class function-binding 'funobj-binding)
		 (setf (movitz-funobj-extent sub-funobj)
		   :indefinite-extent))
		((equal usage '(:call))
		 (change-class function-binding 'closure-binding)
		 (setf (movitz-funobj-extent sub-funobj)
		   :lexical-extent))
		(t (change-class function-binding 'closure-binding)
		   (setf (movitz-funobj-extent sub-funobj)
		     :indefinite-extent))) ; XXX
	       #+ignore (warn "extent: ~S => ~S"
			      sub-funobj
			      (movitz-funobj-extent sub-funobj)))))
    (loop for function-binding in function-binding-usage by #'cddr
	do (finalize-funobj (function-binding-funobj function-binding)))
    (finalize-funobj toplevel-funobj)))

(defun finalize-funobj (funobj)
  "Calculate funobj's constants, jumpers."
  (loop with all-constants-plist = () and all-jumper-sets = ()
      for (nil . function-env) in (function-envs funobj)
			  ;; (borrowed-bindings body-code) in code-specs
      as body-code = (extended-code function-env)
      as (const-plist jumper-sets) =
	(multiple-value-list (find-code-constants-and-jumpers body-code))
      do (loop for (constant usage) on const-plist by #'cddr
	     do (incf (getf all-constants-plist constant 0) usage))
	 (loop for (name set) on jumper-sets by #'cddr
	     do (assert (not (getf all-jumper-sets name)) ()
		  "Jumper-set ~S multiply defined." name)
		(setf (getf all-jumper-sets name) set))
      finally
	(multiple-value-bind (const-list num-jumpers jumpers-map)
	    (layout-funobj-vector all-constants-plist
				  jumper-sets
				  (length (borrowed-bindings funobj)))
	  (setf (movitz-funobj-num-jumpers funobj) num-jumpers
		(movitz-funobj-const-list funobj) const-list
		(movitz-funobj-num-constants funobj) (length const-list)
		(movitz-funobj-jumpers-map funobj) jumpers-map)
	  (loop for binding in (borrowed-bindings funobj)
	      as pos upfrom num-jumpers
	      do (setf (borrowed-binding-reference-slot binding) pos))
	  (return funobj))))
    
(defun layout-stack-frames (funobj)
  "Lay out the stack-frame (i.e. create a frame-map) for funobj
and all its local functions. This must be done breadth-first, because
a (lexical-extent) sub-function might care about its parent frame-map."
  (loop for (nil . function-env) in (function-envs funobj)
      do (assert (not (slot-boundp function-env 'frame-map)))
	 (setf (frame-map function-env)
	   (funobj-assign-bindings (extended-code function-env)
				   function-env)))
  (loop for (sub-function-binding) on (sub-function-binding-usage funobj) by #'cddr
      do (layout-stack-frames (function-binding-funobj sub-function-binding)))
  funobj)

(defun complete-funobj (funobj)
  ;; (assert (= 1 (length (function-envs funobj))))
  (let ((code-specs
	 (loop for (numargs . function-env) in (function-envs funobj)
	     collecting
	       (let* ((frame-map (frame-map function-env))
		      (resolved-code (finalize-code (extended-code function-env) funobj frame-map))
		      (stack-frame-size (frame-map-size (frame-map function-env)))
		      (use-stack-frame-p (or (plusp stack-frame-size)
					     (tree-search resolved-code '(:ebp :esp :call :leave)))))
		 (multiple-value-bind (prelude-code have-normalized-ecx-p)
		     (make-compiled-function-prelude stack-frame-size function-env use-stack-frame-p
						     (need-normalized-ecx-p function-env) frame-map
						     :do-check-stack-p t
						     :forward-2op-position
						     (when (forward-2op function-env)
						       (movitz-funobj-intern-constant funobj
										   (forward-2op function-env))))
		   (let ((function-code (install-arg-cmp (append prelude-code
								 resolved-code
								 (make-compiled-function-postlude funobj function-env
												  use-stack-frame-p))
							 have-normalized-ecx-p)))
		     (let ((optimized-function-code
			    (optimize-code function-code
					   :keep-labels (nconc (subseq (movitz-funobj-const-list funobj)
								       0 (movitz-funobj-num-jumpers funobj))
							       '(entry%1op
								 entry%2op
								 entry%3op)))))
		       (cons numargs optimized-function-code))))))))
    (let ((code1 (cdr (assoc 1 code-specs)))
	  (code2 (cdr (assoc 2 code-specs)))
	  (code3 (cdr (assoc 3 code-specs)))
	  (codet (cdr (assoc 'muerte.cl::t code-specs))))
      (assert codet () "A default numargs-case is required.")
      (let ((combined-code
	     (delete 'start-stack-frame-setup
		     (append
		      (when code1
			`((:cmpb 1 :cl)
			  (:jne 'not-one-arg)
			  ,@(unless (find 'entry%1op code1)
			      '(entry%1op (:movb 1 :cl)))
			  ,@code1
			  not-one-arg))
		      (when code2
			`((:cmpb 2 :cl)
			  (:jne 'not-two-args)
			  ,@(unless (find 'entry%2op code2)
			      '(entry%2op (:movb 2 :cl)))
			  ,@code2
			  not-two-args))
		      (when code3
			`((:cmpb 3 :cl)
			  (:jne 'not-three-args)
			  ,@(unless (find 'entry%3op code3)
			      '(entry%3op (:movb 3 :cl)))
			  ,@code3
			  not-three-args))
		      codet))))
	;; (warn "opt code: ~{~&~A~}" optimized-function-code)
	(multiple-value-bind (code-vector code-symtab)
	    (ia-x86:proglist-encode :octet-vector :32-bit #x00000000
				    (ia-x86:read-proglist (append combined-code
								  `((% bytes 8 0 0 0))))
				    :symtab-lookup
				    (lambda (label)
				      (case label
					(:nil-value (image-nil-word *image*))
					(t (let ((set (cdr (assoc label
								  (movitz-funobj-jumpers-map funobj)))))
					     (when set
					       (let ((pos (search set (movitz-funobj-const-list funobj)
								  :end2 (movitz-funobj-num-jumpers funobj))))
						 (assert pos ()
						   "Couldn't find for ~s set ~S in ~S."
						   label set (subseq (movitz-funobj-const-list funobj)
								     0 (movitz-funobj-num-jumpers funobj)))
						 (* 4 pos))))))))
	  (setf (movitz-funobj-symtab funobj) code-symtab)
	  (let ((code-length (- (length code-vector) 3)))
	    (assert (not (mismatch #(0 0 0) code-vector :start2 code-length)) ()
	      "No space in code-vector was allocated for entry-points.")
	    (setf (fill-pointer code-vector) code-length)
	    ;; debug info
	    (setf (ldb (byte 1 5) (slot-value funobj 'debug-info))
	      1 #+ignore (if use-stack-frame-p 1 0))
	    (let ((x (cdr (assoc 'start-stack-frame-setup code-symtab))))
	      (cond
	       ((not x)
		#+ignore (warn "No start-stack-frame-setup label for ~S." name))
	       ((<= 0 x 30)
		(setf (ldb (byte 5 0) (slot-value funobj 'debug-info)) x))
	       (t (warn "Can't encode start-stack-frame-setup label ~D into debug-info for ~S."
			x (movitz-funobj-name funobj)))))
	    (loop for ((entry-label slot-name) . rest) on '((entry%1op code-vector%1op)
							    (entry%2op code-vector%2op)
							    (entry%3op code-vector%3op))
		do (cond
		    ((assoc entry-label code-symtab)
		     (let ((offset (cdr (assoc entry-label code-symtab))))
		       (setf (slot-value funobj slot-name)
			 (cons offset funobj))
		       (vector-push offset code-vector)))
		    ((some (lambda (label) (assoc label code-symtab))
			   (mapcar #'car rest))
		     (vector-push 0 code-vector))))
	    (setf (movitz-funobj-code-vector funobj)
	      (make-movitz-vector (length code-vector)
			       :fill-pointer code-length
			       :element-type 'movitz-code
			       :initial-contents code-vector
			       :flags '(:code-vector-p)
			       :alignment 16
			       :alignment-offset 8)))))))
  (loop for (sub-function-binding) on (sub-function-binding-usage funobj) by #'cddr
      do (complete-funobj (function-binding-funobj sub-function-binding)))
  funobj)


#+ignore
(defun make-compiled-function-body-default (form funobj env top-level-p)
  (make-compiled-body-pass2 (make-compiled-function-pass1 form funobj env top-level-p)
			    env))

#+ignore
(defun old-make-compiled-function-body-default (form funobj env top-level-p &key include-programs)
  (multiple-value-bind (arg-init-code body-form need-normalized-ecx-p)
      (make-function-arguments-init funobj env form)
    (multiple-value-bind (resolved-code stack-frame-size use-stack-frame-p frame-map)
	(make-compiled-body body-form funobj env top-level-p arg-init-code include-programs)
      (multiple-value-bind (prelude-code have-normalized-ecx-p)
	  (make-compiled-function-prelude stack-frame-size env use-stack-frame-p
					  need-normalized-ecx-p frame-map
					  :forward-2op-position
					  (when (forward-2op env)
					    (new-movitz-funobj-intern-constant funobj (forward-2op env))))
	(values (install-arg-cmp (append prelude-code
					 resolved-code
					 (make-compiled-function-postlude funobj env use-stack-frame-p))
				 have-normalized-ecx-p)
		use-stack-frame-p)))))

#+ignore
(defun make-compiled-function-body-without-prelude (form funobj env top-level-p)
  (multiple-value-bind (code stack-frame-size use-stack-frame-p)
      (make-compiled-body form funobj env top-level-p)
    (if (not use-stack-frame-p)
	(append code (make-compiled-function-postlude funobj env nil))
      (values (append `((:pushl :ebp)
			(:movl :esp :ebp)
			(:pushl :esi)
			start-stack-frame-setup)
		      (case stack-frame-size
			(0 nil)
			(1 '((:pushl :edi)))
			(2 '((:pushl :edi) (:pushl :edi)))
			(t `((:subl ,(* 4 stack-frame-size) :esp))))
		      (when (tree-search code '(:ecx))
			`((:testb :cl :cl)
			  (:js '(:sub-program (normalize-ecx)
				 (:shrl 8 :ecx)
				 (:jmp 'normalize-ecx-ok)))
			  (:andl #x7f :ecx)
			  normalize-ecx-ok))
		      code
		      (make-compiled-function-postlude funobj env t))
	      use-stack-frame-p))))

#+ignore
(defun make-compiled-function-body-2req-1opt (form funobj env top-level-p)
  (when (and (= 2 (length (required-vars env)))
	     (= 1 (length (optional-vars env)))
	     (= 0 (length (key-vars env)))
	     (null (rest-var env)))
    (let* ((opt-var (first (optional-vars env)))
	   (opt-binding (movitz-binding opt-var env nil))
	   (req1-binding (movitz-binding (first (required-vars env)) env nil))
	   (req2-binding (movitz-binding (second (required-vars env)) env nil))
	   (default-form (optional-function-argument-init-form opt-binding)))
      (compiler-values-bind (&code push-default-code-uninstalled &producer default-code-producer)
	  (compiler-call #'compile-form
	    :form default-form
	    :result-mode :push
	    :env env
	    :funobj funobj)
	(cond
	 ((eq 'compile-self-evaluating default-code-producer)
	  (multiple-value-bind (code stack-frame-size use-stack-frame-p frame-map)
	      (make-compiled-body form funobj env top-level-p nil (list push-default-code-uninstalled))
	    (when (and (new-binding-located-p req1-binding frame-map)
		       (new-binding-located-p req2-binding frame-map)
		       (new-binding-located-p opt-binding frame-map))
	      (multiple-value-bind (eax-ebx-code eax-ebx-stack-offset)
		  (make-2req req1-binding req2-binding frame-map)
		(let ((stack-init-size (- stack-frame-size eax-ebx-stack-offset))
		      (push-default-code
		       (finalize-code push-default-code-uninstalled funobj env frame-map)))
		  (values (append `((:jmp '(:sub-program ()
					    (:cmpb 2 :cl)
					    (:je 'entry%2op)
					    (:cmpb 3 :cl)
					    (:je 'entry%3op)
					    (:int 100)))
				    entry%3op
				    (:pushl :ebp)
				    (:movl :esp :ebp)
				    (:pushl :esi)
				    start-stack-frame-setup
				    ,@(when (and (edx-var env) (new-binding-located-p (edx-var env) frame-map))
					`((:movl :edx (:ebp ,(stack-frame-offset
							      (new-binding-location (edx-var env) frame-map))))))
				    ,@eax-ebx-code
				    ,@(if (eql (1+ eax-ebx-stack-offset)
					       (new-binding-location opt-binding frame-map))
					  (append `((:pushl (:ebp ,(argument-stack-offset-shortcut 3 2))))
						  (make-compiled-stack-frame-init (1- stack-init-size)))
					(append (make-compiled-stack-frame-init stack-init-size)
						`((:movl (:ebp ,(argument-stack-offset-shortcut 3 2)) :edx)
						  (:movl :edx (:ebp ,(stack-frame-offset
								      (new-binding-location opt-binding
											    frame-map)))))))
				    (:jmp 'arg-init-done)
				    entry%2op
				    (:pushl :ebp)
				    (:movl :esp :ebp)
				    (:pushl :esi)
				    ,@eax-ebx-code
				    ,@(if (eql (1+ eax-ebx-stack-offset)
					       (new-binding-location opt-binding frame-map))
					  (append push-default-code
						  (make-compiled-stack-frame-init (1- stack-init-size)))
					(append (make-compiled-stack-frame-init stack-init-size)
						push-default-code
						`((:popl (:ebp ,(stack-frame-offset (new-binding-location opt-binding frame-map)))))))
				    arg-init-done)
				  code
				  (make-compiled-function-postlude funobj env t))
			  use-stack-frame-p))))))
	 (t nil))))))

(defun make-2req (binding0 binding1 frame-map)
  (let ((location-0 (new-binding-location binding0 frame-map))
	(location-1 (new-binding-location binding1 frame-map)))
    (cond
     ((and (eq :eax location-0)
	   (eq :ebx location-1))
      (values nil 0))
     ((and (eq :ebx location-0)
	   (eq :eax location-1))
      (values '((:xchgl :eax :ebx)) 0))
     ((and (eql 1 location-0)
	   (eql 2 location-1))
      (values '((:pushl :eax)
		(:pushl :ebx))
	      2))
     ((and (eq :eax location-0)
	   (eql 1 location-1))
      (values '((:pushl :ebx))
	      1))
     (t (error "make-2req confused by loc0: ~W, loc1: ~W" location-0 location-1)))))

(defconstant +enter-stack-frame-code+
    '((:pushl :ebp)
      (:movl :esp :ebp)
      (:pushl :esi)))

#+ignore
(defun make-compiled-function-body-1rest (form funobj env top-level-p)
  (when (and (null (required-vars env))
	     (null (optional-vars env))
	     (null (key-vars env))
	     (rest-var env))
    (multiple-value-bind (code stack-frame-size use-stack-frame-p frame-map)
	(make-compiled-body form funobj env top-level-p)
      (let* ((rest-binding (movitz-binding (rest-var env) env nil))
	     (edx-location (and (edx-var env)
				(new-binding-location (edx-var env) frame-map
						      :default nil)))
	     (edx-code (when edx-location
			 `((:movl :edx (:ebp ,(stack-frame-offset edx-location)))))))
	(cond
	 ((not (new-binding-located-p rest-binding frame-map))
	  (append '(entry%1op
		    entry%2op
		    entry%3op)
		  (when use-stack-frame-p
		    +enter-stack-frame-code+)
		  '(start-stack-frame-setup)
		  (make-compiled-stack-frame-init stack-frame-size)
		  edx-code
		  code
		  (make-compiled-function-postlude funobj env use-stack-frame-p)))
	 (t ;; (new-binding-located-p rest-binding frame-map)
	  (let ((rest-location (new-binding-location rest-binding frame-map)))
	    (values (append +enter-stack-frame-code+
			    '(start-stack-frame-setup)
			    (make-compiled-stack-frame-init stack-frame-size)
			    `((:movl :edi (:ebp ,(stack-frame-offset rest-location))))
			    edx-code
			    `((:testb :cl :cl)
			      (:jz 'end-stack-frame-setup)
			      (:js '(:sub-program (normalize-ecx)
				     (:shrl 8 :ecx)
				     (:jmp 'ecx-ok)))
			      (:andl #x7f :ecx)
			      ecx-ok
			      (:xorl :edx :edx)
			      (:call (:edi ,(global-constant-offset 'restify-dynamic-extent)))
			      (:movl :eax (:ebp ,(stack-frame-offset rest-location)))
			      (:jmp 'end-stack-frame-setup))
			    `(entry%1op
			      ,@+enter-stack-frame-code+
			      ,@(make-compiled-stack-frame-init stack-frame-size)
			      ,@edx-code
			      (:andl -8 :esp)
			      (:pushl :edi)
			      (:pushl :eax)
			      (:leal (:esp 1) :ecx)
			      (:movl :ecx (:ebp ,(stack-frame-offset rest-location)))
			      (:jmp 'end-stack-frame-setup))
			    `(entry%2op
			      ,@+enter-stack-frame-code+
			      ,@(make-compiled-stack-frame-init stack-frame-size)
			      ,@edx-code
			      (:andl -8 :esp)
			      (:pushl :edi)
			      (:pushl :ebx)
			      (:leal (:esp 1) :ecx)
			      (:pushl :ecx)
			      (:pushl :eax)
			      (:leal (:esp 1) :ecx)
			      (:movl :ecx (:ebp ,(stack-frame-offset rest-location)))
			      (:jmp 'end-stack-frame-setup))
			    '(end-stack-frame-setup)
			    code
			    (make-compiled-function-postlude funobj env t))
		    use-stack-frame-p))))))))
		      

#+ignore
(defun make-compiled-function-body-1req-1opt (form funobj env top-level-p)
  (when (and (= 1 (length (required-vars env)))
	     (= 1 (length (optional-vars env)))
	     (= 0 (length (key-vars env)))
	     (null (rest-var env)))
    (let* ((opt-var (first (optional-vars env)))
	   (opt-binding (movitz-binding opt-var env nil))
	   (req-binding (movitz-binding (first (required-vars env)) env nil))
	   (default-form (optional-function-argument-init-form opt-binding)))
      (compiler-values-bind (&code opt-default-code &producer opt-default-producer)
	  (compiler-call #'compile-form
	    :form default-form
	    :result-mode :push
	    :env env
	    :funobj funobj)
	(cond
	 ((eq 'compile-self-evaluating opt-default-producer)
	  (multiple-value-bind (code stack-frame-size use-stack-frame-p frame-map)
	      (make-compiled-body form funobj env top-level-p nil (list opt-default-code))
	    (declare (ignore use-stack-frame-p))
	    (let ((use-stack-frame-p t))
	      (cond
	       ((and (new-binding-located-p req-binding frame-map)
		     (new-binding-located-p opt-binding frame-map))
		(multiple-value-bind (eax-ebx-code eax-ebx-stack-offset)
		    (ecase (new-binding-location req-binding frame-map)
		      ;; might well be more cases here, but let's wait till they show up..
		      (:eax (values nil 0))
		      (1 (values '((:pushl :eax)) 1)))
		  ;; (warn "defc: ~S" opt-default-code)
		  (let ((stack-init-size (- stack-frame-size eax-ebx-stack-offset))
			(installed-default-code (finalize-code opt-default-code funobj env frame-map)))
		    (values (append `((:call (:edi ,(global-constant-offset 'decode-args-1or2)))
				      entry%2op
				      (:pushl :ebp)
				      (:movl :esp :ebp)
				      (:pushl :esi)
				      start-stack-frame-setup
				      ,@eax-ebx-code
				      ,@(if (eql (1+ eax-ebx-stack-offset)
						 (new-binding-location opt-binding frame-map))
					    (append `((:pushl :ebx))
						    (make-compiled-stack-frame-init (1- stack-init-size)))
					  (append (make-compiled-stack-frame-init stack-init-size)
						  `((:movl :ebx (:ebp ,(stack-frame-offset
									(new-binding-location opt-binding
											      frame-map)))))))
				      (:jmp 'arg-init-done)
				      entry%1op
				      (:pushl :ebp)
				      (:movl :esp :ebp)
				      (:pushl :esi)
				      ,@eax-ebx-code
				      ,@(if (eql (1+ eax-ebx-stack-offset)
						 (new-binding-location opt-binding frame-map))
					    (append installed-default-code
						    (make-compiled-stack-frame-init (1- stack-init-size)))
					  (append (make-compiled-stack-frame-init stack-init-size)
						  installed-default-code
						  `((:popl (:ebp ,(stack-frame-offset
								   (new-binding-location opt-binding
											 frame-map)))))))
				      arg-init-done)
				    code
				    (make-compiled-function-postlude funobj env t))
			    use-stack-frame-p))))
	       ((and (new-binding-located-p req-binding frame-map)
		     (not (new-binding-located-p opt-binding frame-map)))
		(multiple-value-bind (eax-code eax-stack-offset)
		    (ecase (new-binding-location req-binding frame-map)
		      (:eax (values nil 0))
		      (1 (values '((:pushl :eax)) 1)))
		  (values (append `((:call (:edi ,(global-constant-offset 'decode-args-1or2)))
				    ;; (:jmp 'decode-numargs)
				    entry%1op
				    entry%2op
				    (:pushl :ebp)
				    (:movl :esp :ebp)
				    (:pushl :esi))
				  eax-code
				  (make-compiled-stack-frame-init (- stack-frame-size eax-stack-offset))
				  code
				  (make-compiled-function-postlude funobj env t))
			  use-stack-frame-p)))
	       (t (warn "1-req-1-opt failed"))))))
	 (t nil))))))


(defun make-compiled-stack-frame-init (stack-frame-init)
  (case stack-frame-init
    (0 nil)
    (1 '((:pushl :edi)))
    (2 '((:pushl :edi) (:pushl :edi)))
    (t `((:subl ,(* 4 stack-frame-init) :esp)))))


(defvar muerte.cl:*compile-file-pathname* nil)

(defun movitz-compile-file (path &key ((:image *image*) *image*)
				   load-priority
				   (delete-file-p nil))
  (handler-bind
      (#+ignore ((or error warning) (lambda (c)
			     (declare (ignore c))
			     (format *error-output* "~&;; In file ~S:" path))))
    (unwind-protect
	(let ((*features* (image-movitz-features *image*)))
	  (multiple-value-prog1
	      (movitz-compile-file-internal path load-priority)
	    (unless (equalp *features* (image-movitz-features *image*))
	      (warn "*features* changed from ~S to ~S." (image-movitz-features *image*) *features*)
	      (setf (image-movitz-features *image*) *features*))))
      (when delete-file-p
	(assert (equal (pathname-directory "/tmp/")
		       (pathname-directory path))
	    (path)
	  "Refusing to delete file not in /tmp.")
	(delete-file path))))
  (values))

(defun movitz-compile-file-internal (path &optional (*default-load-priority*
						  (and (boundp '*default-load-priority*)
						       *default-load-priority*
						       (1+ *default-load-priority*))))
  (declare (special *default-load-priority*))
  (with-retries-until-true (retry "Restart Movitz compilation of ~S." path)
    (let* ((muerte.cl::*compile-file-pathname* path)
	   (*package* (find-package :muerte))
	   (funobj (make-instance 'movitz-funobj-pass1
		     :name (intern (format nil "file-~A" path) :muerte)
		     :lambda-list (movitz-read nil)))
	   (funobj-env (make-local-movitz-environment nil funobj
						   :type 'funobj-env
						   :declaration-context :funobj))
	   (function-env (make-local-movitz-environment funobj-env funobj
						     :type 'function-env
						     :declaration-context :funobj))
	   (file-code
	    (with-compilation-unit ()
	      (with-open-file (stream path :direction :input)
		(setf (funobj-env funobj) funobj-env)
		(loop for form = (with-movitz-syntax ()
				   (read stream nil '#0=#:eof))
		    until (eq form '#0#)
		    appending
		      (with-simple-restart (skip-toplevel-form
					    "Skip the compilation of this top-level form.")
			(compiler-call #'compile-form
			  :form form
			  :funobj funobj
			  :env function-env
			  :top-level-p t
			  :result-mode :ignore)))))))
      (cond
       ((null file-code)
	(setf (image-load-time-funobjs *image*)
	  (delete funobj (image-load-time-funobjs *image*) :key #'first)))
       (t (setf (extended-code function-env) file-code
		(need-normalized-ecx-p function-env) nil
		(function-envs funobj) (list (cons 'muerte.cl::t function-env))
		(funobj-env funobj) funobj-env)
	  (make-compiled-funobj-pass2 funobj)))
      t)))

;;;;

(defun print-code (x code)
  (let ((*print-level* 3))
    (format t "~A code:~{~&  ~A~}" x code))
  code)

(defun layout-program (pc)
  "For the program in pc, layout sub-programs at the top-level program."
  (do ((previous-subs nil)
       (pending-subs nil)
       (new-program nil))
      ((endp pc)
       (assert (not pending-subs) ()
	 "pending subs: ~S" pending-subs)
       (nreverse new-program))
    (let ((i (pop pc)))
      (multiple-value-bind (sub-prg sub-opts)
	  (instruction-sub-program i)
	(if (null sub-prg)
	    (push i new-program)
	  (destructuring-bind (&optional (label (gensym "sub-prg-label-")))
	      sub-opts
	    (let ((x (cons label sub-prg)))
	      (unless (find x previous-subs :test #'equal)
		(push x pending-subs)
		(push x previous-subs)))
	    (unless (instruction-is i :jnever)
	      (push `(,(car i) ',label)
		    new-program))))
	(when (or (instruction-uncontinues-p i)
		  (endp pc))
	  (let* ((match-label (and (eq (car i) :jmp)
				   (consp (second i))
				   (eq (car (second i)) 'quote)
				   (symbolp (second (second i)))
				   (second (second i))))
		 (matching-sub (assoc match-label pending-subs)))
	    (unless (and match-label
			 (or (eq match-label (first pc))
			     (and (symbolp (first pc))
				  (eq match-label (second pc)))))
	      (if matching-sub
		  (setf pc (append (cdr matching-sub) pc)
			pending-subs (delete matching-sub pending-subs))
		(setf pc (append (reduce #'append (nreverse pending-subs)) pc)
		      pending-subs nil)))))))))


(defun optimize-code (unoptimized-code &rest args)
  (if (not *compiler-do-optimize*)
      unoptimized-code
    (apply #'optimize-code-internal
	   (optimize-code-dirties
	    (layout-program (optimize-code-unfold-branches unoptimized-code)))
	   0 args)))

(defun optimize-code-unfold-branches (unoptimized-code)
  "This particular optimization should be done before code layout:
   (:jcc 'label) (:jmp 'foo) label  => (:jncc 'foo) label"
  (flet ((branch-instruction-label (i &optional jmp (branch-types '(:je :jne :jb :jnb :jbe :jz :jl :jnz
								    :jle :ja :jae :jg :jge :jnc :jc :js :jns)))
 	   "If i is a branch, return the label."
	   (when jmp (push :jmp branch-types))
	   (let ((i (ignore-instruction-prefixes i)))
	     (or (and (listp i) (member (car i) branch-types)
		      (listp (second i)) (member (car (second i)) '(quote muerte.cl::quote))
		      (second (second i))))))
	 (negate-branch (branch-type)
	   (ecase branch-type
	     (:jbe :ja) (:ja :jbe)
	     (:jz :jnz) (:jnz :jz)
	     (:je :jne) (:jne :je)
	     (:jc :jnc) (:jnc :jc)
	     (:jl :jge) (:jge :jl)
	     (:jle :jg) (:jg :jle))))
    (loop with next-pc = 'auto-next
			 ;; initially (warn "opt: ~{   ~A~%~}" unoptimized-code)
	for pc = unoptimized-code then (prog1 (if (eq 'auto-next next-pc) auto-next-pc next-pc)
					 (setq next-pc 'auto-next))
	as auto-next-pc = (cdr unoptimized-code) then (cdr pc)
	as p = (list (car pc))		; will be appended.
	as i1 = (first pc)		; current instruction, collected by default.
	and i2 = (second pc) and i3 = (third pc)
	while pc
 	do (when (and (branch-instruction-label i1)
		      (branch-instruction-label i2 t nil)
		      (symbolp i3)
		      (eq i3 (branch-instruction-label i1)))
	     ;; (warn "Got a sit: ~{~&~A~}" (subseq pc 0 3))
	     (setf p (list `(,(negate-branch (car i1)) ',(branch-instruction-label i2 t nil))
			   i3)
		   next-pc (nthcdr 3 pc)))
	nconc p)))

(defun optimize-code-dirties (unoptimized-code)
  "These optimizations may rearrange register usage in a way that is incompatible
with other optimizations that track register usage. So this is performed just once,
initially."
  (labels
      ((twop-p (c &optional op)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (listp c) (= 3 (length c))
		(or (not op) (eq op (first c)))
		(cdr c))))
       (twop-dst (c &optional op src)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (or (not src)
		    (equal src (first (twop-p c op))))
		(second (twop-p c op)))))
       (twop-src (c &optional op dest)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (or (not dest)
		    (equal dest (second (twop-p c op))))
		(first (twop-p c op)))))
       (register-operand (op)
	 (and (member op '(:eax :ebx :ecx :edx :edi))
	      op)))
    (loop with next-pc = 'auto-next
			 ;; initially (warn "opt: ~{   ~A~%~}" unoptimized-code)
	for pc = unoptimized-code then (prog1 (if (eq 'auto-next next-pc) auto-next-pc next-pc)
					 (setq next-pc 'auto-next))
	as auto-next-pc = (cdr unoptimized-code) then (cdr pc)
	as p = (list (car pc))		; will be appended.
	as i1 = (first pc)		; current instruction, collected by default.
	and i2 = (second pc) and i3 = (third pc)
	while pc
 	do (cond
	    ((let ((regx (register-operand (twop-src i1 :movl)))
		   (regy (register-operand (twop-dst i1 :movl))))
	       (and regx regy
		    (eq regx (twop-dst i2 :movl))
		    (eq regx (twop-src i3 :cmpl))
		    (eq regy (twop-dst i3 :cmpl))))
	     (setq p (list `(:cmpl ,(twop-src i2) ,(twop-src i1)))
		   next-pc (nthcdr 3 pc))
	     #+ignore (explain nil "4: ~S for ~S" p (subseq pc 0 4))))
	nconc p)))

(defun optimize-code-internal (unoptimized-code recursive-count &rest key-args
			       &key keep-labels stack-frame-size)
  "Peephole optimizer. Based on a lot of rather random techniques."
  (declare (ignore stack-frame-size))
  (when (<= 20 recursive-count)
    (error "Peephole-optimizer recursive count reached ~D.
There is (propably) a bug in the peephole optimizer." recursive-count))
  ;; (warn "==================OPTIMIZE: ~{~&~A~}" unoptimized-code)
  (labels
      ((explain (always format &rest args)
	 (when (or always *explain-peephole-optimizations*)
	   (warn "Peephole: ~?~&----------------------------" format args)))
       (twop-p (c &optional op)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (listp c) (= 3 (length c))
		(or (not op) (eq op (first c)))
		(cdr c))))
       (twop-dst (c &optional op src)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (or (not src)
		    (equal src (first (twop-p c op))))
		(second (twop-p c op)))))
       (twop-src (c &optional op dest)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (or (not dest)
		    (equal dest (second (twop-p c op))))
		(first (twop-p c op)))))
       #+ignore
       (isrc (c)
	 (let ((c (ignore-instruction-prefixes c)))
	   (ecase (length (cdr c))
	     (0 nil)
	     (1 (cadr c))
	     (2 (twop-src c)))))
       (idst (c)
	 (let ((c (ignore-instruction-prefixes c)))
	   (ecase (length (cdr c))
	     (0 nil)
	     (1 (cadr c))
	     (2 (twop-dst c)))))
       (non-destructuve-p (c)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (consp c)
		(member (car c) '(:testl :testb :pushl :cmpl :cmpb :frame-map)))))
       (simple-instruction-p (c)
	 (let ((c (ignore-instruction-prefixes c)))
	   (and (listp c)
		(member (car c) '(:movl :xorl :popl :cmpl :leal :andl :addl :subl)))))
       (register-indirect-operand (op base)
	 (multiple-value-bind (reg off)
	     (when (listp op)
	       (loop for x in op
		   if (integerp x) sum x into off
		   else collect x into reg
		   finally (return (values reg off))))
	   (and (eq base (car reg))
		(not (rest reg))
		off)))
       (stack-frame-operand (op)
	 (register-indirect-operand op :ebp))
       (funobj-constant-operand (op)
	 (register-indirect-operand op :esi))
       (global-constant-operand (op)
	 (register-indirect-operand op :edi))
       (global-funcall-p (op &optional funs)
	 (let ((op (ignore-instruction-prefixes op)))
	   (when (instruction-is op :call)
	     (let ((x (global-constant-operand (second op))))
	       (flet ((try (name)
			(and (eql x (slot-offset 'movitz-constant-block name))
			     name)))
		 (cond
		  ((not x) nil)
		  ((null funs) t)
		  ((atom funs) (try funs))
		  (t (some #'try funs))))))))
       (preserves-stack-location-p (i stack-location)
	 (let ((i (ignore-instruction-prefixes i)))
	   (and (not (atom i))
		(or (global-funcall-p i)
		    (instruction-is i :frame-map)
		    (branch-instruction-label i)
		    (non-destructuve-p i)
		    (and (simple-instruction-p i)
			 (not (eql stack-location (stack-frame-operand (idst i)))))))))
       (preserves-register-p (i register)
	 (let ((i (ignore-instruction-prefixes i)))
	   (and (not (atom i))
		(or (and (member register '(:edx))
			 (member (global-funcall-p i)
				 '(fast-car fast-cdr fast-car-ebx fast-cdr-ebx)))
		    (instruction-is i :frame-map)
		    (branch-instruction-label i)
		    (non-destructuve-p i)
		    (and (simple-instruction-p i)
			 (not (eq register (idst i))))))))
       (register-operand (op)
	 (and (member op '(:eax :ebx :ecx :edx :edi))
	      op))
       (true-and-equal (x &rest more)
	 (declare (dynamic-extent more))
	 (and x (dolist (y more t)
		  (unless (equal x y)
		    (return nil)))))
       #+ignore
       (uses-stack-frame-p (c)
	 (and (consp c)
	      (some #'stack-frame-operand (cdr c))))
       (load-stack-frame-p (c &optional (op :movl))
	 (stack-frame-operand (twop-src c op)))
       (store-stack-frame-p (c &optional (op :movl))
	 (stack-frame-operand (twop-dst c op)))
       (read-stack-frame-p (c)
	 (or (load-stack-frame-p c :movl)
	     (load-stack-frame-p c :cmpl)
	     (store-stack-frame-p c :cmpl)
	     (and (consp c)
		  (eq :pushl (car c))
		  (stack-frame-operand (second c)))))
       (in-stack-frame-p (c reg)
	 "Does c ensure that reg is in some particular stack-frame location?"
	 (or (and (load-stack-frame-p c)
		  (eq reg (twop-dst c))
		  (stack-frame-operand (twop-src c)))
	     (and (store-stack-frame-p c)
		  (eq reg (twop-src c))
		  (stack-frame-operand (twop-dst c)))))
       (load-funobj-constant-p (c)
	 (funobj-constant-operand (twop-src c :movl)))
       #+ignore
       (sub-program-label-p (l)
	 (and (consp l)
	      (eq :sub-program (car l))))
       (local-load-p (c)
	 (if (or (load-stack-frame-p c)
		 (load-funobj-constant-p c))
	     (twop-src c)
	   nil))
       (label-here-p (label code)
	 "Is <label> at this point in <code>?"
	 (loop for i in code
	     while (or (symbolp i)
		       (instruction-is i :frame-map))
	     thereis (eq label i)))
       (negate-branch (branch-type)
	 (ecase branch-type
	   (:jbe :ja) (:ja :jbe)
	   (:jz :jnz) (:jnz :jz)
	   (:je :jne) (:jne :je)
	   (:jc :jnc) (:jnc :jc)
	   (:jl :jge) (:jge :jl)
	   (:jle :jg) (:jg :jle)))
       (branch-instruction-label (i &optional jmp (branch-types '(:je :jne :jb :jnb :jbe :jz :jl :jnz
								  :jle :ja :jae :jg :jge :jnc :jc :js :jns)))
	 "If i is a branch, return the label."
	 (when jmp (push :jmp branch-types))
	 (let ((i (ignore-instruction-prefixes i)))
	   (or (and (listp i) (member (car i) branch-types)
		    (listp (second i)) (member (car (second i)) '(quote muerte.cl::quote))
		    (second (second i)))
	       #+ignore
	       (and (listp i)
		    branch-types
		    (symbolp (car i))
		    (not (member (car i) '(:jmp :jecxz)))
		    (char= #\J (char (symbol-name (car i)) 0))
		    (warn "Not a branch: ~A / ~A   [~A]" i (symbol-package (caadr i)) branch-types)))))
       (find-branches-to-label (start-pc label &optional (context-size 0))
	 "Context-size is the number of instructions _before_ the branch you want returned."
	 (dotimes (i context-size)
	   (push nil start-pc))
	 (loop for pc on start-pc
	     as i = (nth context-size pc)
	     as i-label = (branch-instruction-label i t)
	     if (or (eq label i-label)
		    (and (consp i-label)
			 (eq :label-plus-one (car i-label))))
	     nconc (list pc)
	     else if (let ((sub-program i-label))
		       (and (consp sub-program)
			    (eq :sub-program (car sub-program))))
	     nconc (find-branches-to-label (cddr (branch-instruction-label i t))
					   label context-size)
	     else if (and (not (atom i))
			  (tree-search i label))
	     nconc (list 'unknown-label-usage)))
       (optimize-trim-stack-frame (unoptimized-code)
	 "Any unused local variables on the stack-frame?"
	 unoptimized-code
	 ;; BUILD A MAP OF USED STACK-VARS AND REMAP THEM!	 
	 #+ignore (if (not (and stack-frame-size
				(find 'start-stack-frame-setup unoptimized-code)))
		      unoptimized-code
		    (let ((old-code unoptimized-code)
			  (new-code ()))
		      ;; copy everything upto start-stack-frame-setup
		      (loop for i = (pop old-code)
			  do (push i new-code)
			  while old-code
			  until (eq i 'start-stack-frame-setup))
		      (assert (eq (car new-code) 'start-stack-frame-setup) ()
			"no start-stack-frame-setup label, but we already checked!")
		      (loop for pos downfrom -8 by 4
			  as i = (pop old-code)
			  if (and (consp i) (eq :pushl (car i)) (symbolp (cadr i)))
			  collect (cons pos (cadr i))
			  and do (unless (find pos old-code :key #'read-stack-frame-p)
				   (cond
				    ((find pos old-code :key #'store-stack-frame-p)
				     (warn "Unused local but stored var: ~S" pos))
				    ((find pos old-code :key #'uses-stack-frame-p)
				     (warn "Unused BUT USED local var: ~S" pos))
				    (t (warn "Unused local var: ~S" pos))))
			  else do
			       (push i old-code)
			       (loop-finish))))
	 unoptimized-code)
       (frame-map-code (unoptimized-code)
	 "After each label in unoptimized-code, insert a (:frame-map <full-map> <branch-map> <sticky>)
that says which registers are known to hold which stack-frame-locations.
A branch-map is the map that is guaranteed after every branch to the label, i.e. not including
falling below the label."
	 #+ignore (warn "unmapped:~{~&~A~}" unoptimized-code)
	 (flet ((rcode-map (code)
		  #+ignore (when (instruction-is (car code) :testb)
			     (warn "rcoding ~A" code))
		  (loop with modifieds = nil
		      with registers = (list :eax :ebx :ecx :edx)
		      with local-map = nil
		      for ii in code
		      while registers
		      do (flet ((add-map (stack reg)
				  (when (and (not (member stack modifieds))
					     (member reg registers))
				    (push (cons stack reg)
					  local-map))))
			   (cond ((instruction-is ii :frame-map)
				  (dolist (m (second ii))
				    (add-map (car m) (cdr m))))
				 ((load-stack-frame-p ii)
				  (add-map (load-stack-frame-p ii)
					   (twop-dst ii)))
				 ((store-stack-frame-p ii)
				  (add-map (store-stack-frame-p ii)
					   (twop-src ii))
				  (pushnew (store-stack-frame-p ii)
					   modifieds))
				 ((non-destructuve-p ii))
				 ((branch-instruction-label ii))
				 ((simple-instruction-p ii)
				  (let ((op (idst ii)))
				    (cond
				     ((stack-frame-operand op)
				      (pushnew (stack-frame-operand op) modifieds))
				     ((symbolp op)
				      (setf registers (delete op registers))))))
				 (t #+ignore (when (instruction-is (car code) :testb)
					       (warn "stopped at ~A" ii))
				    (loop-finish))))
			 (setf registers
			   (delete-if (lambda (r)
					(not (preserves-register-p ii r)))
				      registers))
		      finally
			#+ignore (when (instruction-is (car code) :testb)
				   (warn "..map ~A" local-map))
			(return local-map))))
	   (loop with next-pc = 'auto-next
				;; initially (warn "opt: ~{   ~A~%~}" unoptimized-code)
	       for pc = unoptimized-code then (prog1 (if (eq 'auto-next next-pc) auto-next-pc next-pc)
						(setq next-pc 'auto-next))
	       as auto-next-pc = (cdr unoptimized-code) then (cdr pc)
	       as p = (list (car pc))	; will be appended.
	       as i1 = (first pc)	; current instruction, collected by default.
	       and i2 = (second pc)
	       while pc
	       do (when (and (symbolp i1)
			     (not (and (instruction-is i2 :frame-map)
				       (fourth i2))))
		    (let* ((label i1)
			   (branch-map (reduce (lambda (&optional x y)
						 (intersection x y :test #'equal))
					       (mapcar (lambda (lpc)
							 (if (eq 'unknown-label-usage lpc)
							     nil
							   (rcode-map (nreverse (subseq lpc 0 9)))))
						       (find-branches-to-label unoptimized-code label 9))))
			   (full-map (let ((rcode (nreverse (let* ((pos (loop for x on unoptimized-code
									    as pos upfrom 0
									    until (eq x pc)
									    finally (return pos)))
								   (back9 (max 0 (- pos 9))))
							      (subseq unoptimized-code
								      back9 pos)))))
				       (if (instruction-uncontinues-p (car rcode))
					   branch-map
					 (intersection branch-map (rcode-map rcode) :test #'equal)))))
		      (when (or full-map branch-map nil)
			(explain nil "Inserting at ~A frame-map ~S branch-map ~S."
				 label full-map branch-map))
		      (setq p (list label `(:frame-map ,full-map ,branch-map))
			    next-pc (if (instruction-is i2 :frame-map)
					(cddr pc)
				      (cdr pc)))))
	       nconc p)))
       (optimize-stack-frame-init (unoptimized-code)
	 "Look at the function's stack-frame initialization code, and see
          if we can optimize that, and/or immediately subsequent loads/stores."
	 (if (not (find 'start-stack-frame-setup unoptimized-code))
	     unoptimized-code
	   (let ((old-code unoptimized-code)
		 (new-code ()))
	     ;; copy everything upto start-stack-frame-setup
	     (loop for i = (pop old-code)
		 do (push i new-code)
		 while old-code
		 until (eq i 'start-stack-frame-setup))
	     (assert (eq (car new-code) 'start-stack-frame-setup) ()
	       "no start-stack-frame-setup label, but we already checked!")
	     (let* ((frame-map (loop for pos downfrom -8 by 4
				   as i = (pop old-code)
				   if (and (consp i) (eq :pushl (car i)) (symbolp (cadr i)))
				   collect (cons pos (cadr i))
				   and do (push i new-code)
				   else do
					(push i old-code)
					(loop-finish)))
		    (mod-p (loop with mod-p = nil
			       for i = `(:frame-map ,(copy-list frame-map) nil t)
			       then (pop old-code)
			       while i
			       do (let ((new-i (cond
						((let ((store-pos (store-stack-frame-p i)))
						   (and store-pos
							(eq (cdr (assoc store-pos frame-map))
							    (twop-src i))))
						 (explain nil "removed stack-init store: ~S" i)
						 nil)
						((let ((load-pos (load-stack-frame-p i)))
						   (and load-pos
							(eq (cdr (assoc load-pos frame-map))
							    (twop-dst i))))
						 (explain nil "removed stack-init load: ~S" i)
						 nil)
						((and (load-stack-frame-p i)
						      (assoc (load-stack-frame-p i) frame-map))
						 (let ((old-reg (cdr (assoc (load-stack-frame-p i)
									    frame-map))))
						   (explain nil "load ~S already in ~S."
							    i old-reg)
						   `(:movl ,old-reg ,(twop-dst i))))
						(t i))))
				    (unless (eq new-i i)
				      (setf mod-p t))
				    (when (branch-instruction-label new-i t)
				      (setf mod-p t)
				      (push `(:frame-map ,(copy-list frame-map) nil t)
					    new-code))
				    (when new-i
				      (push new-i new-code)
				      ;; (warn "new-i: ~S, fm: ~S" new-i frame-map)
				      (setf frame-map
					(delete-if (lambda (map)
						     ;; (warn "considering: ~S" map)
						     (not (and (preserves-register-p new-i (cdr map))
							       (preserves-stack-location-p new-i
											   (car map)))))
						   frame-map))
				      ;; (warn "Frame-map now: ~S" frame-map)
				      (when (store-stack-frame-p new-i)
					(loop for map in frame-map
					    do (when (= (store-stack-frame-p new-i)
							(car map))
						 (setf (cdr map) (twop-src new-i)))))))
			       while frame-map
			       finally (return mod-p))))
	       (if (not mod-p)
		   unoptimized-code
		 (append (nreverse new-code)
			 old-code)))))))
    (declare (ignorable load-funobj-constant-p isrc))
    (let* ((unoptimized-code (frame-map-code (optimize-stack-frame-init unoptimized-code)))
	   (code-modified-p nil)
	   (stack-frame-used-map (loop with map = nil
				     for i in unoptimized-code
				     do (let ((x (read-stack-frame-p i)))
					  (when x (pushnew x map)))
					(when (and (instruction-is i :leal)
						   (stack-frame-operand (twop-src i)))
					  (let ((x (stack-frame-operand (twop-src i))))
					    (when (= (tag :cons) (ldb (byte 2 0) x))
					      (pushnew (+ x -1) map)
					      (pushnew (+ x 3) map))))
				     finally (return map)))
	   (optimized-code
	    ;; This loop applies a set of (hard-coded) heuristics on unoptimized-code.
	    (loop with next-pc = 'auto-next
		;; initially (warn "opt: ~{   ~A~%~}" unoptimized-code)
		for pc = unoptimized-code then (prog1 (if (eq 'auto-next next-pc) auto-next-pc next-pc)
						 (setq next-pc 'auto-next))
		as auto-next-pc = (cdr unoptimized-code) then (cdr pc)
		as p = (list (car pc))	; will be appended.
		as original-p = p
		as i = (first pc)	; current instruction, collected by default.
		and i2 = (second pc) and i3 = (third pc) and i4 = (fourth pc) and i5 = (fifth pc)
		while pc
		do (cond
		    ((and (instruction-is i :frame-map)
			  (instruction-is i2 :frame-map)
			  (not (fourth i))
			  (not (fourth i2)))
		     (let ((map (union (second i) (second i2) :test #'equal)))
		       (explain nil "Merged maps:~%~A + ~A~% => ~A"
				(second i) (second i2) map)
		       (setq p `((:frame-map ,map))
			     next-pc (cddr pc))))
		    ((let ((x (store-stack-frame-p i)))
		       (and x (not (member x stack-frame-used-map))))
		     (setq p nil)
		     (explain nil "Removed store of unused local var: ~S" i))
		    ((and (global-funcall-p i2 '(fast-car))
			  (global-funcall-p i5 '(fast-cdr))
			  (true-and-equal (in-stack-frame-p i :eax)
					  (in-stack-frame-p i4 :eax)))
		     (let ((call-prefix (if (consp (car i2)) (car i2) nil)))
		       (cond
			((equal i3 '(:pushl :eax))
			 (explain nil "merge car,push,cdr to cdr-car,push")
			 (setf p (list i
				       `(,call-prefix :call
						      (:edi ,(global-constant-offset 'fast-cdr-car)))
				       `(:pushl :ebx))
			       next-pc (nthcdr 5 pc)))
			((and (store-stack-frame-p i3)
			      (eq :eax (twop-src i3)))
			 (explain nil "merge car,store,cdr to cdr-car,store")
			 (setf p (list i
				       `(,call-prefix :call
						      (:edi ,(global-constant-offset 'fast-cdr-car)))
				       `(:movl :ebx ,(twop-dst i3)))
			       next-pc (nthcdr 5 pc)))
			(t (error "can't deal with cdr-car here: ~{~&~A~}" (subseq pc 0 8))))))
		    ((flet ((try (place register &optional map reason)
			      "See if we can remove a stack-frame load below current pc,
                              given the knowledge that <register> is equal to <place>."
			      (let ((next-load (and place
						    (dolist (si (cdr pc))
						      (when (and (twop-p si :cmpl)
								 (equal place (twop-src si)))
							(warn "Reverse cmp not yet dealed with.."))
						      (cond
						       ((and (twop-p si :cmpl)
							     (equal place (twop-dst si)))
							(return si))
						       ((equal place (local-load-p si))
							(return si))
						       ((or (not (consp si))
							    (not (preserves-register-p si register))
							    (equal place (twop-dst si)))
							(return nil)))
						      (setf map
							(remove-if (lambda (m)
								     (not (preserves-register-p si (cdr m))))
								   map))))))
				(case (instruction-is next-load)
				  (:movl
				   (let ((pos (position next-load pc)))
				     (setq p (nconc (subseq pc 0 pos)
						    (if (or (eq register (twop-dst next-load))
							    (find-if (lambda (m)
								       (and (eq (twop-dst next-load) (cdr m))
									    (= (car m) (stack-frame-operand place))))
								     map))
							nil
						      (list `(:movl ,register ,(twop-dst next-load)))))
					   next-pc (nthcdr (1+ pos) pc))
				     (explain nil "preserved load/store .. load ~S of place ~S because ~S."
					      next-load place reason)))
				  (:cmpl
				   (let ((pos (position next-load pc)))
				     (setq p (nconc (subseq pc 0 pos)
						    (list `(:cmpl ,(twop-src next-load) ,register)))
					   next-pc (nthcdr (1+ pos) pc))
				     (explain nil "preserved load/store..cmp: ~S" p next-load))))
				(if next-load t nil))))
		       (or (when (instruction-is i :frame-map)
			     (loop for (place . register) in (second i)
;;;				 do (warn "map try ~S ~S: ~S" place register
;;;					  (try place register))
				 thereis (try `(:ebp ,place) register (second i) :frame-map)))
			   (try (or (local-load-p i)
				    (and (store-stack-frame-p i)
					 (twop-dst i)))
				(if (store-stack-frame-p i)
				    (twop-src i)
				  (twop-dst i))
				nil i))))
		    ((and (symbolp i)
			  (instruction-is i2 :frame-map)
			  (load-stack-frame-p i3)
			  (eq (twop-dst i3)
			      (cdr (assoc (load-stack-frame-p i3) (third i2))))
			  (not (assoc (load-stack-frame-p i3) (second i2))))
		     (let ((reg (cdr (assoc (load-stack-frame-p i3) (third i2)))))
		       (explain nil "factor out load from loop: ~S" i3)
		       (setq p (if (eq reg (twop-dst i3))
				   (list i3 i i2)
				 (append (error "weewf")
					 (list i3 i i2)
					 `((:movl ,reg ,(twop-dst i3)))))
			     next-pc (cdddr pc))))
		    ;; ((:jmp x) ...(no labels).... x ..)
		    ;; => (x ...)
		    ((let ((x (branch-instruction-label i t nil)))
		       (and (position x (cdr pc))
			    (not (find-if #'symbolp (cdr pc) :end (position x (cdr pc))))))
		     (explain nil "jmp x .. x: ~W"
			      (subseq pc 0 (1+ (position (branch-instruction-label i t nil)
							 pc))))
		     (setq p nil
			   next-pc (member (branch-instruction-label i t nil) pc)))
		    ;; (:jcc 'x) .... x (:jmp 'y) ..
		    ;; => (:jcc 'y) .... x (:jmp 'y) ..
		    ((let* ((from (branch-instruction-label i t))
			    (dest (member (branch-instruction-label i t)
					  unoptimized-code))
			    (to (branch-instruction-label (if (instruction-is (second dest) :frame-map)
							      (third dest)
							    (second dest))
							  t nil)))
		       (when (and from to (not (eq from to)))
			 (setq p (list `(,(car i) ',to)))
			 (explain nil "branch redirect from ~S to ~S" from to)
			 t)))
		    ;; remove branch no-ops.
		    ((and (branch-instruction-label i t)
			  (label-here-p (branch-instruction-label i t)
					(cdr pc)))
		     (explain nil "branch no-op: ~A" i)
		     (setq p nil))
		    ((and (symbolp i)
			  (null (symbol-package i))
			  (null (find-branches-to-label unoptimized-code i))
			  (not (member i keep-labels)))
		     (setq p nil
			   next-pc (cdr pc))
		     (explain nil "unused label: ~S" i))
		    ;; ((:jcc 'label) (:jmp 'y) label) => ((:jncc 'y) label)
		    ((and (branch-instruction-label i)
			  (branch-instruction-label i2 t nil)
			  (symbolp i3)
			  (eq (branch-instruction-label i) i3))
		     (setq p (list `(,(negate-branch (first i))
				     ',(branch-instruction-label i2 t nil)))
			   next-pc (nthcdr 2 pc))
		     (explain nil "collapsed double negative branch to ~S: ~A." i3 p))
		    ((and (branch-instruction-label i)
			  (instruction-is i2 :frame-map)
			  (branch-instruction-label i3 t nil)
			  (symbolp i4)
			  (eq (branch-instruction-label i) i4))
		     (setq p (list `(,(negate-branch (first i))
				     ',(branch-instruction-label i3 t nil)))
			   next-pc (nthcdr 3 pc))
		     (explain nil "collapsed double negative branch to ~S: ~A." i4 p))
		    ((and (twop-p i :movl)
			  (register-operand (twop-src i))
			  (register-operand (twop-dst i))
			  (twop-p i2 :movl)
			  (eq (twop-dst i) (twop-dst i2))
			  (register-indirect-operand (twop-src i2) (twop-dst i)))
		     (setq p (list `(:movl (,(twop-src i)
					    ,(register-indirect-operand (twop-src i2)
									(twop-dst i)))
					   ,(twop-dst i2)))
			   next-pc (nthcdr 2 pc))
		     (explain nil "(movl edx eax) (movl (eax <z>) eax) => (movl (edx <z>) eax: ~S"
			      p))
		    ((and (twop-p i :movl)
			  (instruction-is i2 :pushl)
			  (eq (twop-dst i) (second i2))
			  (twop-p i3 :movl)
			  (eq (twop-dst i) (twop-dst i3)))
		     (setq p (list `(:pushl ,(twop-src i)))
			   next-pc (nthcdr 2 pc))
		     (explain nil "(movl <z> :eax) (pushl :eax) => (pushl <z>): ~S" p))
		    ((and (instruction-uncontinues-p i)
			  (not (or (symbolp i2)
				   #+ignore (member (instruction-is i2) '(:foobar)))))
		     (do ((x (cdr pc) (cdr x)))
			 (nil)
		       (cond
			((not (or (symbolp (car x))
				  #+ignore (member (instruction-is (car x)) '(:foobar))))
			 (explain nil "Removing unreachable code ~A after ~A." (car x) i))
			(t (setf p (list i)
				 next-pc x)
			   (return)))))
		    ((and (store-stack-frame-p i)
			  (load-stack-frame-p i2)
			  (load-stack-frame-p i3)
			  (= (store-stack-frame-p i)
			     (load-stack-frame-p i3))
			  (not (eq (twop-dst i2) (twop-dst i3))))
		     (setq p (list i `(:movl ,(twop-src i) ,(twop-dst i3)) i2)
			   next-pc (nthcdr 3 pc))
		     (explain nil "store, z, load => store, move, z: ~A" p))
		    ((and (instruction-is i :movl)
			  (member (twop-dst i) '(:eax :ebx :ecx :edx))
			  (instruction-is i2 :pushl)
			  (not (member (second i2) '(:eax :ebx :ecx :edx)))
			  (equal (twop-src i) (second i2)))
		     (setq p (list i `(:pushl ,(twop-dst i)))
			   next-pc (nthcdr 2 pc))
		     (explain t "load, push => load, push reg."))
		    ((and (instruction-is i :movl)
			  (member (twop-src i) '(:eax :ebx :ecx :edx))
			  (instruction-is i2 :pushl)
			  (not (member (second i2) '(:eax :ebx :ecx :edx)))
			  (equal (twop-dst i) (second i2)))
		     (setq p (list i `(:pushl ,(twop-src i)))
			   next-pc (nthcdr 2 pc))
		     (explain nil "store, push => store, push reg: ~S ~S" i i2))
		    ((and (instruction-is i :cmpl)
			  (true-and-equal (stack-frame-operand (twop-dst i))
					  (load-stack-frame-p i3))
			  (branch-instruction-label i2))
		     (setf p (list i3
				   `(:cmpl ,(twop-src i) ,(twop-dst i3))
				   i2)
			   next-pc (nthcdr 3 pc))
		     (explain nil "~S ~S ~S => ~S" i i2 i3 p))
		    ((and (instruction-is i :pushl)
			  (instruction-is i3 :popl)
			  (store-stack-frame-p i2)
			  (store-stack-frame-p i4)
			  (eq (idst i3) (twop-src i4)))
		     (setf p (list i2
				   `(:movl ,(idst i) ,(twop-dst i4))
				   `(:movl ,(idst i) ,(idst i3)))
			   next-pc (nthcdr 4 pc))
		     (explain nil "~S => ~S" (subseq pc 0 4) p))
		    ((let ((i6 (nth 6 pc)))
		       (and (global-funcall-p i2 '(fast-car))
			    (global-funcall-p i6 '(fast-cdr))
			    (load-stack-frame-p i)
			    (eq :eax (twop-dst i))
			    (equal i i4))))
		    ((and (equal i '(:movl :ebx :eax))
			  (global-funcall-p i2 '(fast-car fast-cdr)))
		     (let ((newf (ecase (global-funcall-p i2 '(fast-car fast-cdr))
				   (fast-car 'fast-car-ebx)
				   (fast-cdr 'fast-cdr-ebx))))
		       (setq p `((:call (:edi ,(global-constant-offset newf))))
			     next-pc (nthcdr 2 pc))
		       (explain nil "Changed [~S ~S] to ~S" i i2 newf)))
		    ((and (load-stack-frame-p i) (eq :eax (twop-dst i))
			  (global-funcall-p i2 '(fast-car fast-cdr))
			  (preserves-stack-location-p i3 (load-stack-frame-p i))
			  (eql (load-stack-frame-p i)
			       (load-stack-frame-p i4)))
		     (let ((newf (ecase (global-funcall-p i2 '(fast-car fast-cdr))
				   (fast-car 'fast-car-ebx)
				   (fast-cdr 'fast-cdr-ebx))))
		       (setq p `((:movl ,(twop-src i) :ebx)
				 (:call (:edi ,(global-constant-offset newf)))
				 ,i3
				 ,@(unless (eq :ebx (twop-dst i4))
				     `((:movl :ebx ,(twop-dst i4)))))
			     next-pc (nthcdr 4 pc))
		       (explain nil "load around ~A" newf))))
		do (unless (eq p original-p) ; auto-detect whether any heuristic fired..
		     #+ignore (warn "at ~A, ~A inserted ~A" i i2 p)
		     #+ignore (warn "modified at ~S ~S ~S" i i2 i3)
		     (setf code-modified-p t))
		nconc p)))
      (if code-modified-p
	  (apply #'optimize-code-internal optimized-code (1+ recursive-count) key-args)
	(optimize-trim-stack-frame
	 (remove :frame-map (progn #+ignore (warn "maps:~{~&~A~}" unoptimized-code)
				   unoptimized-code)
		 :key (lambda (x)
			(when (consp x)
			  (car x)))))))))

;;;; Compiler internals  

(defclass binding ()
  ((name
    :initarg :name
    :accessor binding-name)
   (env
    :accessor binding-env)
   (declarations
    :initarg :declarations
    :accessor binding-declarations)))

(defmethod print-object ((object binding) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (when (slot-boundp object 'name)
      (princ (binding-name object) stream))))

(defclass constant-object-binding (binding)
  ((object
    :initarg :object
    :reader constant-object)))

(defmethod binding-lended-p ((binding constant-object-binding)) nil)

(defclass operator-binding (binding) ())

(defclass macro-binding (operator-binding)
  ((expander
    :initarg :expander
    :accessor macro-binding-expander)))

(defclass symbol-macro-binding (binding)
  ((expander
    :initarg :expander
    :accessor macro-binding-expander)))

(defclass variable-binding (binding)
  ((lended-p				; a property-list
    :initform nil
    :accessor binding-lended-p)
   (store-type				; union of all types ever stored here
    :initform nil
    ;; :initarg :store-type
    :accessor binding-store-type)))

(defclass funobj-binding (function-binding) ())
(defclass closure-binding (function-binding located-binding) ())
(defclass lexical-binding (variable-binding) ())
(defclass located-binding (lexical-binding) ())

(defclass function-binding (operator-binding located-binding)
  ((funobj
    :initarg :funobj
    :accessor function-binding-funobj)
   (parent-funobj
    :initarg :parent-funobj
    :reader function-binding-parent)))

(defclass lambda-binding (function-binding) ())

#+ignore
(defclass temporary-name (located-binding)
  ;; Is the value that this binding is bound to dynamic-extent?
  (#+ignore
   (stack-frame-allocated-p		; also a property-list
    :initform nil
    :accessor stack-frame-allocated-p)))

(defclass borrowed-binding (located-binding)
  ((reference-slot
    :initarg :reference-slot
    :accessor borrowed-binding-reference-slot)
   (target-binding
    :initarg :target-binding
    :reader borrowed-binding-target)
   (usage
    :initarg :usage
    :initform nil
    :accessor borrowed-binding-usage)))

(defclass lexical-borrowed-binding (borrowed-binding)
  ((stack-frame-distance
    :initarg :stack-frame-distance
    :reader stack-frame-distance))
  (:documentation "A closure with lexical extent borrows bindings using this class."))

(defclass indefinite-borrowed-binding (borrowed-binding)
  ((reference-slot
    :initarg :reference-slot
    :reader borrowed-binding-reference-slot)))

#+ignore
(defclass constant-reference-binding (lexical-binding)
  ((object
    :initarg :object
    :reader constant-reference-object)))

#+ignore
(defmethod print-object ((object constant-reference-binding) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (format stream "object: ~S" (constant-reference-object object)))
  object)

(defclass forwarding-binding (lexical-binding)
  ((target-binding
    :initarg :target-binding
    :accessor forwarding-binding-target)))

(defmethod binding-funobj ((binding binding))
  (movitz-environment-funobj (binding-env binding)))

(defmethod binding-funobj ((binding forwarding-binding))
  (movitz-environment-funobj (binding-env (forwarding-binding-target binding))))

(defclass function-argument (located-binding) ())
(defclass edx-function-argument (function-argument) ())

(defclass positional-function-argument (function-argument)
  ((argnum
    :initarg :argnum
    :reader function-argument-argnum)))

(defclass required-function-argument (positional-function-argument) ())

(defclass register-required-function-argument (required-function-argument) ())
(defclass fixed-required-function-argument (required-function-argument)
  ((numargs
    :initarg :numargs
    :reader binding-numargs)))
(defclass floating-required-function-argument (required-function-argument) ())

(defclass non-required-function-argument (function-argument)
  ((init-form
    :initarg init-form
    :reader optional-function-argument-init-form)
   (supplied-p-var
    :initarg supplied-p-var
    :reader optional-function-argument-supplied-p-var)))

(defclass optional-function-argument (non-required-function-argument positional-function-argument) ())

(defclass supplied-p-function-argument (function-argument) ())

(defclass rest-function-argument (positional-function-argument) ())
(defclass hidden-rest-function-argument (rest-function-argument) ())

(defclass keyword-function-argument (non-required-function-argument)
  ((keyword-name
    :initarg :keyword-name
    :reader keyword-function-argument-keyword-name)
   (rest-var-name
    :initarg :rest-var-name
    :reader keyword-function-argument-rest-var-name)))

(defclass dynamic-binding (variable-binding) ())

(defclass shadowing-binding (binding) ())

(defclass shadowing-dynamic-binding (dynamic-binding shadowing-binding)
  ((shadowed-variable
    :initarg :shadowed-variable
    :reader shadowed-variable)
   (shadowing-variable
    :initarg :shadowing-variable
    :reader shadowing-variable)))

(defun stack-frame-offset (stack-frame-position)
  (* -4 (1+ stack-frame-position)))

(defun argument-stack-offset (binding)
  (check-type binding fixed-required-function-argument)
  (argument-stack-offset-shortcut (binding-numargs binding)
				  (function-argument-argnum binding)))

(defun argument-stack-offset-shortcut (numargs argnum)
  "For a function of <numargs> arguments, locate the ebp-relative position
of argument <argnum>."
  (* 4 (- numargs -1 argnum)))

;;;

;;; New style of locating bindings. The point is to not side-effect the binding objects.

(defun new-binding-location (binding map &key (default nil default-p))
  (check-type binding (or binding (cons keyword binding)))
  (cdr (or (assoc binding map)
	   (if default-p
	       default
	     (error "No location for ~S." binding)))))

(defun make-binding-map () nil)

(defun new-binding-located-p (binding map)
  (check-type binding (or binding (cons keyword binding)))
  (and (assoc binding map) t))

(defun frame-map-size (map)
  (reduce #'max map :initial-value 0 :key (lambda (x) (if (integerp (cdr x)) (cdr x) 0))))

(define-setf-expander new-binding-location (binding map-place &environment env)
  (multiple-value-bind (temps values stores setter getter)
      (get-setf-expansion map-place env)
    (let ((new-value (gensym))
	  (binding-var (gensym)))
      (values (append temps (list binding-var))
	      (append values (list binding))
	      (list new-value)
	      `(let ((,(car stores) (progn
				      (assert (not (new-binding-located-p ,binding-var ,getter)))
				      (check-type ,new-value (or keyword (integer 0 *)))
				      (acons ,binding-var ,new-value ,getter))))
		 ,setter
		 ,new-value)
	      `(new-binding-location ,binding-var ,getter)))))

;;; Objects with dynamic extent may be located on the stack-frame, which at
;;; compile-time is represented with this structure.

;;;(defclass stack-allocated-object ()
;;;  ((size
;;;    ;; Size in words (4 octets) this object occupies in the stack-frame.
;;;    :initarg :size
;;;    :accessor size)
;;;   (location
;;;    ;; Stack-frame offset (in words) this object is allocated to.
;;;    :accessor location)))
  

;;;


(defun instruction-sub-program (instruction)
  "When an instruction contains a sub-program, return that program, and 
the sub-program options (&optional label) as secondary value."
  (and (consp instruction)
       (consp (second instruction))
       (symbolp (car (second instruction)))
       (string= 'quote (car (second instruction)))
       (let ((x (second (second instruction))))
	 (and (consp x)
	      (eq :sub-program (car x))
	      (values (cddr x)
		      (second x))))))

(defun ignore-instruction-prefixes (instruction)
  (if (and (consp instruction)
	   (listp (car instruction)))
      (cdr instruction)
    instruction))

(defun instruction-is (instruction &optional operator)
  (and (listp instruction)
       (let ((instruction (ignore-instruction-prefixes instruction)))
	 (if operator
	     (eq operator (car instruction))
	   (car instruction)))))

(defun instruction-uncontinues-p (instruction)
  "Is it impossible for control to return after instruction?"
  (member (instruction-is instruction)
	  '(:jmp :ret)))
  
(defun sub-environment-p (env1 env2)
  (cond
   ((eq env1 env2) t)
   ((null env1) nil)
   (t (sub-environment-p (movitz-environment-uplink env1) env2))))

(defun find-code-constants-and-jumpers (code &key include-programs)
  "Return code's constants (a plist of constants and their usage-counts) and jumper-sets."
  (let (jumper-sets constants)
    (labels ((process-binding (binding)
	       "Some bindings are really references to constants."
	       (typecase binding
		 (constant-object-binding
		  (let ((object (movitz-read (constant-object binding))))
		    (when (typep object 'movitz-heap-object)
		      (incf (getf constants object 0)))))
		 (forwarding-binding
		  (process-binding (forwarding-binding-target binding)))
		 (funobj-binding
		  (let ((funobj (function-binding-funobj binding)))
		    (incf (getf constants funobj 0))))
		 (closure-binding)
		 (function-binding
		  (error "No function-binding now..: ~S" binding))))
	     (process (sub-code)
	       "This local function side-effects the variables jumper-sets and constants."
	       (loop for instruction in sub-code
		   do (case (instruction-is instruction)
			((:local-function-init :load-lambda)
			 (let* ((binding (second instruction))
				(funobj (function-binding-funobj binding)))
			   (incf (getf constants funobj 0))
			   (dolist (binding (borrowed-bindings funobj))
			     (process-binding binding))))
			((:load-lexical :lend-lexical :call-lexical)
			 (process-binding (second instruction)))
			(:load-constant
			 (let ((object (movitz-read (second instruction))))
			   (when (typep object 'movitz-heap-object)
			     (incf (getf constants object 0)))))
			(:declare-label-set
			 (destructuring-bind (name set)
			     (cdr instruction)
			   (setf (getf jumper-sets name) set))))
		   do (let ((sub (instruction-sub-program instruction)))
			(when sub (process sub))))))
      (process code)
      (map nil #'process include-programs))
    (values constants jumper-sets)))

(defun layout-funobj-vector (constants jumper-sets num-borrowing-slots)
  (let* ((jumpers (loop with x
		      for set in (cdr jumper-sets) by #'cddr
		      unless (search set x)
		      do (setf x (nconc x (copy-list set)))
		      finally (return x)))
	 (num-jumpers (length jumpers)))
    (values (append jumpers
		    (make-list num-borrowing-slots :initial-element *movitz-nil*)
		    (mapcar (lambda (x) (movitz-read (car x)))
			    (sort (loop for (constant count) on constants by #'cddr
				      unless (or (eq constant *movitz-nil*)
						 (eq constant (image-t-symbol *image*)))
				      collect (cons constant count))
				  #'< :key #'cdr)))
	    num-jumpers
	    (loop for (name set) on jumper-sets by #'cddr
		collect (cons name set)))))

(defun movitz-funobj-intern-constant (funobj obj)
  ;; (error "XXXXX")
  (let ((cobj (movitz-read obj)))
    (+ (slot-offset 'movitz-funobj 'constant0)
       (* (sizeof 'word)
	  (let* ((pos (position cobj (movitz-funobj-const-list funobj)
				:start (movitz-funobj-num-jumpers funobj))))
	    (assert pos ()
	      "Couldn't find constant ~S in ~S's set of constants ~S."
	      obj funobj (movitz-funobj-const-list funobj))
	    pos)))))

(defun discover-variables (code function-env)
  "Iterate over CODE, and take note in the hash-table VAR-COUNTER which ~
   variables CODE references that are lexically bound in ENV.
   Also return the set of borrowed-bindings discovered."
  (check-type function-env function-env)
  ;; (format t "~{~&~S~}" code)
  (let ((var-counter (make-hash-table :test #'eq :size 40))
	#+ignore (funobj (movitz-environment-funobj function-env)))
    (labels ((take-note-of-binding (binding &optional storep)
	       ;; (check-type binding lexical-binding)
	       (if storep
		   (setf (gethash binding var-counter)
		     (or (gethash binding var-counter) 0))
		 (incf (gethash binding var-counter 0)))
	       (when (typep binding 'forwarding-binding)
		 (take-note-of-binding (forwarding-binding-target binding))))
	     (ensure-local-binding (binding)
	       "If binding is borrowed from another funobj, we must replace it with a borrowing-binding."
	       #+ignore (assert (eq funobj (binding-funobj binding)) ()
			  "Not local: ~S" binding)
	       binding)
	     (do-discover-variables (code env)
	       (loop for instruction in code
		   when (listp instruction)
		   do (flet ((lend-lexical (borrowing-binding dynamic-extent-p)
			       (let ((lended-binding
				      (ensure-local-binding (borrowed-binding-target borrowing-binding))))
				 (when (typep lended-binding 'forwarding-binding)
				   (setf lended-binding
				     (change-class lended-binding 'located-binding)))
				 (pushnew lended-binding
					  (potentially-lended-bindings function-env))
				 (take-note-of-binding lended-binding)
				 (symbol-macrolet ((p (binding-lended-p lended-binding)))
				   (incf (getf p :lended-count 0))
				   (setf (getf p :dynamic-extent-p) (and (getf p :dynamic-extent-p t)
									 dynamic-extent-p))))))
			(let ((load-binding (find-read-bindings instruction)))
			  (when load-binding
			    (take-note-of-binding load-binding)))
			(let ((store-binding (find-written-binding-and-type instruction)))
			  (when store-binding
			    (take-note-of-binding store-binding t)))
			(case (instruction-is instruction)
			  ((:local-function-init :load-lambda)
			   (let ((function-binding (second instruction)))
			     (take-note-of-binding function-binding)
			     (let ((closure-funobj (function-binding-funobj function-binding)))
			       (dolist (borrowing-binding (borrowed-bindings closure-funobj))
				 (lend-lexical borrowing-binding nil)))))
			  (:call-lexical
			   (destructuring-bind (binding num-args)
			       (cdr instruction)
			     (declare (ignore num-args))
			     (etypecase binding
			       (function-binding
				(take-note-of-binding (ensure-local-binding binding)))
			       (funobj-binding))))
			  (t (do-discover-variables (instruction-sub-program instruction) env)))))))
      (do-discover-variables code function-env))
    ;; any hidden-rest is always used..
    (loop for (nil . binding) in (movitz-environment-bindings function-env)
	do (when (typep binding 'hidden-rest-function-argument)
	     (incf (gethash binding var-counter 0))))
    ;; (setf (movitz-funobj-borrowed-bindings funobj) borrowed-bindings)
    (values var-counter)))

(defun assign-bindings (code function-env &optional (initial-stack-frame-position 1)
						    (frame-map (make-binding-map)))
  "Assign locations to all lexical variables in CODE. Recurses into any
   sub-environments found in CODE. A frame-map which is an assoc from
   bindings to stack-frame locations."
  ;; Then assign them to locations in the stack-frame.
  ;; (warn "assigning code:~%~{~&    ~A~}" code)
  (check-type function-env function-env)
  (assert (= initial-stack-frame-position
	     (1+ (frame-map-size frame-map))))
  (let* ((env-roof-map nil)		; memoize result of assign-env-bindings
	 (flat-program code)
	 (var-counts (discover-variables flat-program function-env)))
    (labels ((env-floor (env)
	       (cond
		((eq env function-env)
		 initial-stack-frame-position)
		((typep env 'function-env)
		 (error "SEFEW: ~S" function-env))
		;; The floor of this env is the roof of its extent-uplink.
		(t (assign-env-bindings (movitz-environment-extent-uplink env)))))
	     (assign-env-bindings (env)
	       (or (getf env-roof-map env nil)
		   (let ((stack-frame-position (env-floor env))
			 (bindings-to-locate
			  (loop for (variable . binding) in (movitz-environment-bindings env)
			      unless (cond
				      ((not (typep binding 'lexical-binding)))
				      ((typep binding 'lambda-binding))
				      ((not (plusp (gethash binding var-counts 0)))
				       (prog1 t
					 (unless (or (movitz-env-get variable 'ignore nil env nil)
						     (movitz-env-get variable 'ignorable nil env nil))
					   (warn "Unused variable: ~S" variable)))))
			      collect binding)))
		     (when (eq env function-env)
		       (setf bindings-to-locate
			 (sort bindings-to-locate #'<
			       :key (lambda (binding)
				      (etypecase binding
					(edx-function-argument 3)
					(positional-function-argument
					 (* 2 (function-argument-argnum binding)))
					(binding 100000)))))
		       ;; (warn "btl: ~S" bindings-to-locate)
		       (loop for binding in bindings-to-locate
			   while (or (typep binding 'register-required-function-argument)
				     (typep binding 'floating-required-function-argument)
				     (and (typep binding 'positional-function-argument)
					  (< (function-argument-argnum binding)
					     2)))
			   do (unless (new-binding-located-p binding frame-map)
				(setf (new-binding-location binding frame-map)
				  (post-incf stack-frame-position)))))
		     (dolist (binding bindings-to-locate)
		       (when (and (binding-lended-p binding)
				  (not (typep binding 'borrowed-binding))
				  (not (getf (binding-lended-p binding) :stack-cons-location)))
			 ;; (warn "assigning lending-cons for ~W at ~D" binding stack-frame-position)
			 (let ((cons-pos (post-incf stack-frame-position 2)))
			   (setf (new-binding-location (cons :lended-cons binding) frame-map)
			     (1+ cons-pos))
			   (setf (getf (binding-lended-p binding) :stack-cons-location)
			     cons-pos)))
		       (unless (new-binding-located-p binding frame-map)
			 (etypecase binding
			   (constant-object-binding) ; no location needed.
			   (forwarding-binding) ; will use the location of destination binding.
			   (borrowed-binding) ; location is predetermined
			   (fixed-required-function-argument
			    (setf (new-binding-location binding frame-map) :argument-stack))
			   (located-binding
			    ;; don't think twice, it's alright..
			    ;; (i.e. this is where we should be clever about assigning bindings
			    ;;  to registers and whatnot..)
			    ;; (warn "assign ~W to ~D" binding stack-frame-position)
			    (setf (new-binding-location binding frame-map)
			      (post-incf stack-frame-position))))))
		     (setf (getf env-roof-map env)
		       stack-frame-position)))))
      (loop ;; with funobj = (movitz-environment-funobj function-env)
	  for binding being the hash-keys of var-counts
	  as env = (binding-env binding)
		   ;; do (warn "bind: ~S: ~S" binding (eq function-env (find-function-env env funobj)))
	  when (sub-env-p env function-env)
	  do (assign-env-bindings (binding-env binding)))
      frame-map)))


(defun operators-present-in-code-p (code operators operands &key (operand-test #'eql)
								 (test #'identity))
  "A simple tree search for `(<one of operators> ,operand) in CODE."
  ;; (break "Deprecated operators-present-in-code-p")
  (cond
   ((atom code)
    nil)
   ((and (member (first code) operators)
	 (or (null operands)
	     (if (atom operands)
		 (funcall operand-test (second code) operands)
	       (member (second code) operands :test operand-test)))
	 (funcall test code)
	 code))
   (t (or (operators-present-in-code-p (car code) operators operands
				       :operand-test operand-test
				       :test test)
	  (operators-present-in-code-p (cdr code) operators operands
				       :operand-test operand-test
				       :test test)))))


(defun code-uses-binding-p (code binding &key (load t) store call)
  "Does extended <code> potentially read/write/call <binding>?"
  (labels ((search-funobj (funobj binding load store call)
	     ;; If this is a recursive lexical call (i.e. labels),
	     ;; the function-envs might not be bound, but then this
	     ;; code is searched already.
	     (when (slot-boundp funobj 'function-envs)
	       (some (lambda (function-env-spec)
		       (code-search (extended-code (cdr function-env-spec)) binding
				    load store call))
		     (function-envs funobj))))
	   (code-search (code binding load store call)
	     (dolist (instruction code)
	       (when (consp instruction)
		 (let ((x (or (when load
				(let ((load-binding (find-read-bindings instruction)))
				  (when load-binding
				    (binding-eql binding load-binding))))
			      (when store
				(let ((store-binding (find-written-binding-and-type instruction)))
				  (when store-binding
				    (binding-eql binding store-binding))))
			      (case (car instruction)
				(:local-function-init
				 (search-funobj (function-binding-funobj (second instruction))
						binding load store call))
				(:load-lambda
				 (or (when load
				       (binding-eql binding (second instruction)))
				     (search-funobj (function-binding-funobj (second instruction))
						    binding load store call)))
				(:call-lexical
				 (or (when call
				       (binding-eql binding (second instruction)))
				     (search-funobj (function-binding-funobj (second instruction))
						    binding load store call))))
			      (code-search (instruction-sub-program instruction)
					   binding load store call))))
		   (when x (return t)))))))
    (code-search code binding load store call)))

(defun binding-eql (x y)
  (check-type x binding)
  (check-type y binding)
  (or (eql x y)
      (and (typep x 'forwarding-binding)
	   (binding-eql (forwarding-binding-target x) y))
      (and (typep y 'forwarding-binding)
	   (binding-eql x (forwarding-binding-target y)))))

(defun tree-search (tree items)
  (etypecase tree
    (atom (if (atom items)
	      (eql tree items)
	    (member tree items)))
    (cons (or (tree-search (car tree) items)
	      (tree-search (cdr tree) items)))))

(defun operator (x)
  (if (atom x) x (car x)))

(defun result-mode-type (x)
  (etypecase x
    (symbol x)
    (cons (car x))
    (lexical-binding :lexical-binding)
    (dynamic-binding :dynamic-binding)))

(defun operands (x)
  (if (symbolp x) nil (cdr x)))

(defun funobj-assign-bindings (code env &optional (stack-frame-position 1)
						  (frame-map (make-binding-map)))
  "This wrapper around assign-bindings checks if the first instructions of CODE
are load-lexicals of the first two function arguments, and if possible these
bindings are located in the appropriate register, so no stack location is needed."
  (check-type env function-env)
  (let ((funobj (movitz-environment-funobj env))
	(scan-code code))
    ;; (warn "code: ~{~&~S~}" (subseq scan-code 0 5))
    (let ((first-location
	   (multiple-value-bind (first-load-binding first-load-destination)
	       (instruction-is-load-lexical-of-binding (first scan-code))
	     (when (and *compiler-allow-transients*
			first-load-binding
			(eq funobj (movitz-environment-funobj (binding-env first-load-binding)))
			(not (code-uses-binding-p (rest scan-code) first-load-binding
						  :load t :store t :call t)))
	       (let* ((location (case (result-mode-type first-load-destination)
				  ((:push :boolean-branch-on-false :boolean-branch-on-true)
				   (case (if (typep first-load-binding 'positional-function-argument)
					     (function-argument-argnum first-load-binding)
					   0)
				     (0 :eax)
				     (1 :ebx)))
				  ((:eax :single-value :function :ecx :edx) :eax)
				  (:ebx :ebx)
				  (t :eax))))
		 ;; (warn "loc: ~W, bind: ~S" location first-load-binding)
		 (when location
		   (when (typep first-load-binding 'register-required-function-argument)
		     ;; (warn "assigning ~W to ~W:~{~&   ~A~}" first-load-binding location (subseq code 0 12))
		     ;; (setf (binding-location first-load-binding) location)
		     (setf (new-binding-location first-load-binding frame-map) location)
		     (setf scan-code (rest scan-code))))
		 location)))))
      (multiple-value-bind (first-load-binding first-load-destination)
	  (instruction-is-load-lexical-of-binding (first scan-code))
	(when (and *compiler-allow-transients*
		   first-load-binding
		   (eq funobj (movitz-environment-funobj (binding-env first-load-binding)))
		   (not (code-uses-binding-p (rest scan-code) first-load-binding
					     :load t :store t :call t)))
	  (let* ((location (case first-load-destination
			     ((:push :boolean-branch-on-true :boolean-branch-on-false)
			      (case (if (typep first-load-binding 'positional-function-argument)
					(function-argument-argnum first-load-binding)
				      1)
				(0 :eax)
				(1 :ebx)))
			     ((:eax :single-value :function) :eax)
			     (:ebx :ebx))))
	    ;;(warn "loc2: ~W, bind2: ~S" location first-load-binding)
	    (when location
	      ;; (warn "assigning ~W to ~W.." first-load-binding location)
	      ;; (warn "assigning ~W to ~W:~{~&   ~A~}" first-load-binding location (subseq code 0 12))
	      (when (eq location first-location)
		(setf location (ecase first-location
				 (:eax :ebx)
				 (:ebx :eax))))
	      (when (typep first-load-binding 'register-required-function-argument)
		;; (setf (binding-location first-load-binding) location)
		(setf (new-binding-location first-load-binding frame-map) location)
		(setf scan-code (rest scan-code)))))))))
  (assign-bindings code env stack-frame-position frame-map))

(defconstant +dynamic-frame-marker+ #xd193)
(defconstant +dynamic-catch-marker+ #xd293)

(defun single-value-register (mode)
  (ecase mode
    ((:eax :single-value :multiple-values :function) :eax)
    ((:ebx :ecx :edx :esi :esp) mode)))

(defun result-mode-register (mode)
  (case mode
    ((:eax :single-value) :eax)
    ((:ebx :ecx :edx :esi :esp) mode)
    (t mode)))

(defun accept-register-mode (mode &optional (default-mode :eax))
  (case mode
    ((:eax :ebx :ecx :edx)
     mode)
    (t default-mode)))

(defun make-indirect-reference (base-register offset)
  "Make the shortest possible assembly indirect reference, explointing the constant edi register."
  (if (<= #x-80 offset #x7f)
      (list base-register offset)
    (let ((edi (image-nil-word *image*)))
      (cond
       ((<= #x-80 (- offset edi) #x7f)
	`(,base-register :edi ,(- offset edi)))
       ((<= #x-80 (- offset (* 2 edi)) #x7f)
	`(,base-register (:edi 2) ,(- offset (* 2 edi))))
       ((<= #x-80 (- offset (* 4 edi)) #x7f)
	`(,base-register (:edi 4) ,(- offset (* 4 edi))))
       ((<= #x-80 (- offset (* 8 edi)) #x7f)
	`(,base-register (:edi 8) ,(- offset (* 8 edi))))
       (t (list base-register offset))))))

(defun make-load-lexical (binding result-mode funobj shared-reference-p frame-map
			  &key tmp-register protect-registers)
  "When tmp-register is provided, use that for intermediate storage required when
loading borrowed bindings."
  (when (movitz-env-get (binding-name binding) 'ignore nil (binding-env binding))
    (warn "The variable ~S is used even if it was declared ignored."
	  (binding-name binding)))
  (flet ((chose-tmp-register (&optional preferred)
	   (or tmp-register
	       (unless (member preferred protect-registers)
		 preferred)
	       (first (set-difference '(:eax :ebx :ecx :edx)
				      protect-registers))
	       (error "Unable to chose a temporary register.")))
	 (install-for-single-value (lexb lexb-location result-mode indirect-p)
	   (if (integerp lexb-location)
	       (append `((:movl ,(make-indirect-reference :ebp (stack-frame-offset lexb-location))
				,(single-value-register result-mode)))
		       (when indirect-p
			 `((:movl (-1 ,(single-value-register result-mode))
				  ,(single-value-register result-mode)))))
	     (ecase lexb-location
	       (:eax
		(assert (not indirect-p))
		(ecase result-mode
		  ((:ecx :edx) `((:movl :eax ,result-mode)))
		  ((:eax :single-value) nil)))
	       ((:ebx :ecx :edx)
		(assert (not indirect-p))
		(unless (eq result-mode lexb-location)
		  (ecase result-mode
		    ((:eax :single-value) `((:movl :ebx :eax)))
		    ((:ebx :ecx :ecx) `((:movl ,lexb-location ,result-mode))))))
	       (:argument-stack
		(assert (<= 2 (function-argument-argnum lexb)) ()
		  "lexical :argument-stack argnum can't be ~A." (function-argument-argnum lexb))
		(append `((:movl (:ebp ,(argument-stack-offset lexb))
				 ,(single-value-register result-mode)))
			(when indirect-p
			  `((:movl (-1 ,(single-value-register result-mode))
				   ,(single-value-register result-mode))))))))))
    (etypecase binding
      (forwarding-binding
       (assert (not (binding-lended-p binding)) (binding)
	 "Can't lend a forwarding-binding ~S." binding)
       (make-load-lexical (forwarding-binding-target binding)
			  result-mode funobj shared-reference-p frame-map))
      (constant-object-binding
       (assert (not (binding-lended-p binding)) (binding)
	 "Can't lend a constant-reference-binding ~S." binding)
       (make-load-constant (constant-object binding)
			   result-mode
			   funobj frame-map))
      (borrowed-binding
       (let ((slot (borrowed-binding-reference-slot binding)))
	 (cond
	  (shared-reference-p
	   (ecase (result-mode-type result-mode)
	     ((:eax :ebx :ecx :edx)
	      `((:movl (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot)))
		       ,(result-mode-type result-mode))))))
	  ((not shared-reference-p)
	   (case result-mode
	     ((:single-value :eax :ebx :ecx :edx :esi)
	      (let ((tmp-register (chose-tmp-register (single-value-register result-mode))))
		`((:movl (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot)))
			 ,tmp-register)
		  (:movl (,tmp-register -1)
			 ,(single-value-register result-mode)))))
	     (:push
	      (let ((tmp-register (chose-tmp-register :eax)))
		`((:movl (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot)))
			 ,tmp-register)
		  (:pushl (,tmp-register -1)))))
	     (t (let ((tmp-register (chose-tmp-register :eax)))
		  (make-result-and-returns-glue
		   result-mode tmp-register
		   `((:movl (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot)))
			    ,tmp-register)
		     (:movl (,tmp-register -1) ,tmp-register))))))))))
      (located-binding
       (let ((binding-location (new-binding-location binding frame-map)))
	 (cond
	  ((and (binding-lended-p binding)
		(not shared-reference-p))
	   (case result-mode
	     ((:single-value :eax :ebx :ecx :edx :esi :esp)
	      (install-for-single-value binding binding-location
					(single-value-register result-mode) t))
	     (:push
	      (if (integerp binding-location)
		  `((:movl (:ebp ,(stack-frame-offset binding-location)) :eax)
		    (:pushl (:eax -1)))
		(ecase binding-location
;;;		  (:eax '((:pushl :eax)))
;;;		  (:ebx '((:pushl :ebx)))
		  (:argument-stack
		   (assert (<= 2 (function-argument-argnum binding)) ()
		     ":load-lexical argnum can't be ~A." (function-argument-argnum binding))
		   `((:movl (:ebp ,(argument-stack-offset binding)) :eax)
		     (:pushl (:eax -1)))))))
	     (t (make-result-and-returns-glue
		 result-mode :eax
		 (install-for-single-value binding binding-location :eax t)))))
	  (t (case (operator result-mode)
	       ((:single-value :eax :ebx :ecx :edx :esi :esp)
		(install-for-single-value binding binding-location
					  (single-value-register result-mode) nil))
	       (:push
		(if (integerp binding-location)
		    `((:pushl (:ebp ,(stack-frame-offset binding-location))))
		  (ecase binding-location
		    (:eax '((:pushl :eax)))
		    (:ebx '((:pushl :ebx)))
		    (:argument-stack
		     (assert (<= 2 (function-argument-argnum binding)) ()
		       ":load-lexical argnum can't be ~A." (function-argument-argnum binding))
		     `((:pushl (:ebp ,(argument-stack-offset binding))))))))
	       (:boolean-branch-on-true
		(if (integerp binding-location)
		    `((:cmpl :edi (:ebp ,(stack-frame-offset binding-location)))
		      (:jne ',(operands result-mode)))
		  (ecase binding-location
		    ((:eax :ebx)
		     `((:cmpl :edi ,binding-location)
		       (:jne ',(operands result-mode))))
		    (:argument-stack
		     `((:cmpl :edi (:ebp ,(argument-stack-offset binding)))
		       (:jne ',(operands result-mode)))))))
	       (:boolean-branch-on-false
		(if (integerp binding-location)
		    `((:cmpl :edi (:ebp ,(stack-frame-offset binding-location)))
		      (:je ',(operands result-mode)))
		  (ecase binding-location
		    ((:eax :ebx)
		     `((:cmpl :edi ,binding-location)
		       (:je ',(operands result-mode))))
		    (:argument-stack
		     `((:cmpl :edi (:ebp ,(argument-stack-offset binding)))
		       (:je ',(operands result-mode)))))))
	       (:untagged-fixnum-ecx
		(make-result-and-returns-glue
		 result-mode :ecx
		 (install-for-single-value binding binding-location :ecx nil)))
	       (t (make-result-and-returns-glue
		   result-mode :eax
		   (install-for-single-value binding binding-location :eax nil)))
	       ))))))))

(defun make-store-lexical (binding source shared-reference-p frame-map)
  (assert (not (and shared-reference-p
		    (not (binding-lended-p binding))))
      (binding)
    "funny binding: ~W" binding)
  (cond
   ((typep binding 'borrowed-binding)
    (let ((slot (borrowed-binding-reference-slot binding)))
      (if (not shared-reference-p)
	  (let ((tmp-reg (if (eq source :eax) :ebx :eax)))
	    `((:movl (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot)))
		     ,tmp-reg)
	      (:movl ,source (-1 ,tmp-reg))))
	`((:movl ,source (:esi ,(+ (slot-offset 'movitz-funobj 'constant0) (* 4 slot))))))))
   ((typep binding 'forwarding-binding)
    (assert (not (binding-lended-p binding)) (binding))
    (make-store-lexical (forwarding-binding-target binding)
			source shared-reference-p frame-map))
   ((not (new-binding-located-p binding frame-map))
    ;; (warn "Can't store to unlocated binding ~S." binding)
    nil)
   ((and (binding-lended-p binding)
	 (not shared-reference-p))
    (let ((tmp-reg (if (eq source :eax) :ebx :eax))
	  (location (new-binding-location binding frame-map)))
      (if (integerp location)
	  `((:movl (:ebp ,(stack-frame-offset location)) ,tmp-reg)
	    (:movl ,source (,tmp-reg -1)))
	(ecase location
	  (:argument-stack
	   (assert (<= 2 (function-argument-argnum binding)) ()
	     "store-lexical argnum can't be ~A." (function-argument-argnum binding))
	   `((:movl (:ebp ,(argument-stack-offset binding)) ,tmp-reg)
	     (:movl ,source (,tmp-reg -1))))))))
   (t (let ((location (new-binding-location binding frame-map)))
	(if (integerp location)
	    `((:movl ,source (:ebp ,(stack-frame-offset location))))
	  (ecase location
	    ((:eax :ebx :edx)
	     (unless (eq source location)
	       `((:movl ,source ,location))))
	    (:argument-stack
	     (assert (<= 2 (function-argument-argnum binding)) ()
	       "store-lexical argnum can't be ~A." (function-argument-argnum binding))
	     `((:movl ,source (:ebp ,(argument-stack-offset binding)))))))))))

(defun finalize-code (code funobj frame-map)
  (labels ((actual-binding (b)
	     (if (typep b 'borrowed-binding)
		 (borrowed-binding-target b)
	       b))
	   (make-lend-lexical (borrowing-binding funobj-register dynamic-extent-p)
	     (let ((lended-binding (ensure-local-binding
				    (borrowed-binding-target borrowing-binding))))
	       #+ignore (warn "LB: in ~S ~S from ~S"
			      funobj
			      lended-binding borrowing-binding)
	       (assert (eq funobj (binding-funobj lended-binding)))
	       (assert (plusp (getf (binding-lended-p (actual-binding lended-binding))
				    :lended-count 0)) ()
		 "Asked to lend ~S of ~S to ~S of ~S with no lended-count."
		 lended-binding (binding-env lended-binding)
		 borrowing-binding (binding-env borrowing-binding))
	       (assert (eq funobj-register :edx))
	       (when (getf (binding-lended-p lended-binding) :dynamic-extent-p)
		 (assert dynamic-extent-p))
	       ;; (warn "lending: ~W" lended-binding)
	       (append (make-load-lexical lended-binding :eax funobj t frame-map)
		       (unless (or (typep lended-binding 'borrowed-binding)
				   (getf (binding-lended-p lended-binding) :dynamic-extent-p))
			 (append `((:globally (:call (:edi (:edi-offset ensure-heap-cons-variable)))))
				 (make-store-lexical lended-binding :eax t frame-map)))
		       `((:movl :eax
				(,funobj-register
				 ,(+ (slot-offset 'movitz-funobj 'constant0)
				     (* 4 (borrowed-binding-reference-slot borrowing-binding)))))))))
	   (ensure-local-binding (binding)
	     (if (eq funobj (binding-funobj binding))
		 binding
	       (or (find binding (borrowed-bindings funobj)
			 :key #'borrowed-binding-target)
		   (error "Can't install non-local binding ~W." binding)))))
    (labels ((fix-edi-offset (tree)
	       (cond
		((atom tree)
		 tree)
		((eq :edi-offset (car tree))
		 (check-type (cadr tree) symbol "a Movitz constant-block label")
		 (+ (global-constant-offset (cadr tree))
		    (reduce #'+ (cddr tree))))
		(t (cons (fix-edi-offset (car tree))
			 (fix-edi-offset (cdr tree)))))))
      (loop for instruction in code
	  appending
	    (cond
	     ((atom instruction) 
	      (list instruction))
	     ((and (= 2 (length instruction))
		   (let ((operand (second instruction)))
		     (and (listp operand)
			  (symbolp (first operand))
			  (string= 'quote (first operand))
			  (listp (second operand)))))
	      ;;(break "op: ~S" (second (second instruction)))
	      ;; recurse into program-to-append..
	      (list (list (first instruction)
			  (list 'quote (finalize-code (second (second instruction))
						      funobj frame-map)))))
	   
	     (t ;; (warn "finalizing ~S" instruction)
		(case (first instruction)
		  ((:locally :globally)
		   (destructuring-bind (sub-instr)
		       (cdr instruction)
		     (let ((pf (ecase (first instruction)
				 (:locally *compiler-local-segment-prefix*)
				 (:globally *compiler-global-segment-prefix*))))
		       (list (fix-edi-offset
			      (cond
			       ((atom sub-instr)
				sub-instr)
			       ((consp (car sub-instr))
				(list* (append pf (car sub-instr))
				       (cdr sub-instr)))
			       (t (list* pf sub-instr))))))))
		  (:declare-label-set nil)
		  (:local-function-init
		   (destructuring-bind (function-binding)
		       (operands instruction)
		     #+ignore (warn "local-function-init: init ~S at ~S"
				    function-binding
				    (new-binding-location function-binding frame-map))
		     (finalize-code 
		      (let* ((sub-funobj (function-binding-funobj function-binding))
			     (lend-code (loop for bb in (borrowed-bindings sub-funobj)
					    append (make-lend-lexical bb :edx nil))))
			(cond
			 ((null lend-code)
			  ;; (warn "null lending")
			  (append (make-load-constant sub-funobj :eax funobj frame-map)
				  (make-store-lexical function-binding :eax nil frame-map)))
			 (t (append (make-load-constant sub-funobj :eax funobj frame-map)
				    `((:movl (:edi ,(global-constant-offset 'copy-funobj)) :esi)
				      (:call (:esi ,(bt:slot-offset 'movitz-funobj 'code-vector%1op)))
				      (:movl :eax :edx))
				    (make-store-lexical function-binding :eax nil frame-map)
				    lend-code))))
		      funobj frame-map)))
		  (:load-lambda
		   (destructuring-bind (function-binding register)
		       (operands instruction)
		     ;; (warn "load-lambda not completed for ~S" function-binding)
		     (finalize-code
		      (let* ((sub-funobj (function-binding-funobj function-binding))
			     (lend-code (loop for bb in (borrowed-bindings sub-funobj)
					    appending
					      (make-lend-lexical bb :edx nil))))
			(cond
			 ((null lend-code)
			  ;; (warn "null lambda lending")
			  (append (make-load-constant sub-funobj register funobj frame-map)))
			 (t (append (make-load-constant sub-funobj :eax funobj frame-map)
				    `((:movl (:edi ,(global-constant-offset 'copy-funobj)) :esi)
				      (:call (:esi ,(bt:slot-offset 'movitz-funobj 'code-vector%1op)))
				      (:movl :eax :edx))
				    lend-code
				    `((:movl :edx ,register))))))
		      funobj frame-map)))
		  (:load-constant
		   (destructuring-bind (object result-mode &key (op :movl))
		       (cdr instruction)
		     (make-load-constant object result-mode funobj frame-map :op op)))
		  (:lexical-control-transfer
		   (destructuring-bind (return-code return-mode from-env to-env &optional to-label)
		       (cdr instruction)
		     (declare (ignore return-code))
		     (let ((x (apply #'make-compiled-lexical-control-transfer
				     nil
				     return-mode from-env to-env
				     (when to-label (list to-label)))))
		       (finalize-code x funobj frame-map))))
		  (:call-lexical
		   (destructuring-bind (binding num-args)
		       (operands instruction)
		     (append (etypecase binding
			       (closure-binding
				(make-load-lexical (ensure-local-binding binding)
						   :esi funobj nil frame-map
						   :tmp-register :edx))
			       (funobj-binding
				(make-load-constant (function-binding-funobj binding)
						    :esi funobj frame-map)))
			     (make-compiled-funcall-by-esi num-args))))
		  (t (expand-extended-code instruction funobj frame-map)))))))))


(defun image-t-symbol-p (x)
  (eq x (image-t-symbol *image*)))

(deftype movitz-t ()
  `(satisfies image-t-symbol-p))

(defun make-load-constant (object result-mode funobj frame-map &key (op :movl))
  (let ((movitz-obj (movitz-read object)))
    (case op
      (:movl
       (etypecase movitz-obj
	 (movitz-nil
	  (ecase (result-mode-type result-mode)
	    (:lexical-binding
	     (make-store-lexical result-mode :edi nil frame-map))
	    (:push
	     '((:pushl :edi)))
	    ((:eax :ebx :ecx :edx)
	     `((:movl :edi ,result-mode)))
	    (:boolean-branch-on-true
	     ;; (warn "branch-on-true for nil!")
	     nil)
	    (:boolean-branch-on-false
	     ;; (warn "branch-on-false for nil!")
	     `((:jmp ',(operands result-mode))))
	    ((:multiple-values :function)
	     '((:movl :edi :eax)
	       (:clc)))
	    #+ignore
	    (t (when (eq :boolean result-mode)
		 (warn "Compiling ~S for mode ~S." object result-mode))
	       (make-result-and-returns-glue result-mode :edi nil)
	       #+ignore '((:movl :edi :eax)))))
	 (movitz-t
	  (ecase (result-mode-type result-mode)
	    (:push
	     `((:pushl (:edi ,(global-constant-offset 't-symbol)))))
	    ((:eax :ebx :ecx :edx)
	     `((:movl (:edi ,(global-constant-offset 't-symbol)) ,result-mode)))
	    (:boolean-branch-on-false
	     ;; (warn "boolean-branch-on-false T")
	     nil)
	    (:boolean-branch-on-true
	     ;; (warn "boolean-branch-on-true T")
	     `((:jmp ',(operands result-mode))))
	    ((:multiple-values :function)
	     `((:movl (:edi ,(global-constant-offset 't-symbol))
		      :eax)
	       (:clc)))
	    (:lexical-binding
	     (append `((:movl (:edi ,(global-constant-offset 't-symbol))
			      :eax))
		     (make-store-lexical result-mode :eax nil frame-map)))
	    #+ignore
	    (t (when (eq :boolean result-mode)
		 (warn "Compiling ~S for mode ~S." object result-mode))
	       (make-result-and-returns-glue result-mode :eax
					     `((:movl (:edi ,(global-constant-offset 't-symbol))
						      :eax))))))
	 (movitz-immediate-object
	  (let ((x (movitz-immediate-value movitz-obj)))
	    (ecase (result-mode-type result-mode)
	      (:lexical-binding
	       (append (make-immediate-move x :eax)
		       (make-store-lexical result-mode :eax nil frame-map)))
	      (:untagged-fixnum-eax
	       (let ((value (movitz-fixnum-value object)))
		 (check-type value (unsigned-byte 16))
		 (make-immediate-move value :eax)))
	      (:untagged-fixnum-ecx
	       (let ((value (movitz-fixnum-value object)))
		 (check-type value (unsigned-byte 16))
		 (make-immediate-move value :ecx)))
	      (:push
	       `((:pushl ,x)))
	      ((:eax :ebx :ecx :edx)
	       (make-immediate-move x result-mode))
	      ((:multiple-values :function)
	       (append (make-immediate-move x :eax)
		       '((:clc)))))))
	 (movitz-heap-object
	  (ecase (result-mode-type result-mode)
	    (:lexical-binding
	     (append `((:movl ,(new-make-compiled-constant-reference movitz-obj funobj)
			      :eax))
		     (make-store-lexical result-mode :eax nil frame-map)))
	    (:push
	     `((:pushl ,(new-make-compiled-constant-reference movitz-obj funobj))))
	    ((:eax :ebx :ecx :edx :esi)
	     `((,op ,(new-make-compiled-constant-reference movitz-obj funobj)
		    ,result-mode)))
	    ((:edi)
	     (assert (eq op :cmpl))
	     `((,op ,(new-make-compiled-constant-reference movitz-obj funobj)
		    ,result-mode)))
	    ((:function :multiple-values)
	     (assert (eq op :movl))
	     `((,op ,(new-make-compiled-constant-reference movitz-obj funobj)
		    :eax)
	       (:clc)))))))
      (t (ecase result-mode
	   ((:eax :ebx :ecx :edx :esi)
	    `((,op ,(new-make-compiled-constant-reference movitz-obj funobj)
		   ,result-mode)))
	   ((:edi)
	    (assert (eq op :cmpl))
	    `((,op ,(new-make-compiled-constant-reference movitz-obj funobj)
		   ,result-mode))))))))

(defconstant +movitz-lambda-list-keywords+
    '(muerte.cl:&OPTIONAL
      muerte.cl:&REST
      muerte.cl:&KEY
      muerte.cl:&AUX
      muerte.cl:&BODY
      muerte.cl:&WHOLE
      muerte.cl:&ALLOW-OTHER-KEYS
      muerte.cl:&ENVIRONMENT))

(defun add-bindings-from-lambda-list (lambda-list env)
  "From a (normal) <lambda-list>, add bindings to <env>."
  (let ((arg-pos 0))
    (multiple-value-bind (required-vars optional-vars rest-var key-vars auxes allow-p min-args max-args edx-var)
	(decode-normal-lambda-list lambda-list)
      (declare (ignore auxes))
      (setf (min-args env) min-args
	    (max-args env) max-args
	    (allow-other-keys-p env) allow-p)
      (flet ((shadow-when-special (formal env)
	       "Iff <formal> is special, return a fresh variable-name that takes <formal>'s place
as the lexical variable-name, and add a new shadowing dynamic binding for <formal> in <env>."
	       (if (not (movitz-env-get formal 'special nil env))
		   formal
		 (let* ((shadowed-formal (gensym (format nil "shadowed-~A-" formal)))
			(shadowing-binding (make-instance 'shadowing-dynamic-binding
					     :name shadowed-formal
					     :shadowing-variable formal
					     :shadowed-variable shadowed-formal)))
		   (movitz-env-add-binding env shadowing-binding formal)
		   (push (list formal shadowed-formal)
			 (special-variable-shadows env))
		   shadowed-formal))))
	(when edx-var
	  (movitz-env-add-binding env
			       (setf (edx-var env)
				 (make-instance 'edx-function-argument
				   :name edx-var))))
	(setf (required-vars env)
	  (loop for formal in required-vars
	      do (check-type formal symbol)
	      do (setf formal
		   (shadow-when-special formal env))
	      do (movitz-env-add-binding env (cond
					   ((< arg-pos 2)
					    (make-instance 'register-required-function-argument
					      :name formal
					      :argnum arg-pos))
					   ((and max-args (= min-args max-args))
					    (make-instance 'fixed-required-function-argument
					      :name formal
					      :argnum arg-pos
					      :numargs min-args))
					   (t (make-instance 'floating-required-function-argument
						:name formal
						:argnum arg-pos))))
	      do (incf arg-pos)
	      collect formal))
	(setf (optional-vars env)
	  (loop for spec in optional-vars
	      collect
		(multiple-value-bind (formal init-form supplied-p-parameter)
		    (decode-optional-formal spec)
		  (setf formal (shadow-when-special formal env))
		  (movitz-env-add-binding env (make-instance 'optional-function-argument
					     :name formal
					     :argnum (post-incf arg-pos)
					     'init-form init-form
					     'supplied-p-var supplied-p-parameter))
		  (when supplied-p-parameter
		    (setf supplied-p-parameter
		      (shadow-when-special supplied-p-parameter env))
		    (movitz-env-add-binding env (make-instance 'supplied-p-function-argument
					       :name supplied-p-parameter)))
		  formal)))
	(when rest-var
	  (check-type rest-var symbol)
	  (let ((formal (shadow-when-special rest-var env)))
	    (setf (rest-var env) formal)
	    (movitz-env-add-binding env (make-instance 'rest-function-argument
				       :name formal
				       :argnum (post-incf arg-pos)))))
	(setf (key-vars env)
	  (loop for spec in key-vars
	      with rest-var-name =
		(or rest-var
		    (and key-vars
			 (let ((name (gensym "hidden-rest-var-")))
			   (movitz-env-add-binding env (make-instance 'hidden-rest-function-argument
						      :name name
						      :argnum (post-incf arg-pos)))
			   name)))
	      collect
		(multiple-value-bind (formal keyword-name init-form supplied-p-parameter)
		    (decode-keyword-formal spec)
		  (setf formal (shadow-when-special formal env))
		  (movitz-env-add-binding env (make-instance 'keyword-function-argument
					     :name formal
					     'init-form init-form
					     'supplied-p-var supplied-p-parameter
					     :keyword-name keyword-name
					     :rest-var-name rest-var-name))
		  (when supplied-p-parameter
		    (setf supplied-p-parameter
		      (shadow-when-special supplied-p-parameter env))
		    (movitz-env-add-binding env (make-instance 'supplied-p-function-argument
					       :name supplied-p-parameter)))
		  formal))))))
  env)

(defun make-compiled-function-prelude-numarg-check (min-args max-args)
  "The prelude is compiled after the function's body."
  (assert (or (not max-args) (<= 0 min-args max-args)))
  (assert (<= 0 min-args (or max-args min-args) #xffff) ()
    "Lambda lists longer than #xffff are not yet implemented.")
  (let ((wrong-numargs (make-symbol "wrong-numargs")))
    (cond
     ((and (zerop min-args)		; any number of arguments is
	   (not max-args))		; acceptable, no check necessary.
      nil)
     ((not max-args)
      ;; only minimum
      (if (< min-args #x80)
	  `((:cmpb ,min-args :cl)
	    (:jb '(:sub-program (,wrong-numargs) (:int 100))))
	`((:cmpl ,(dpb min-args (byte 24 8) #x80) :ecx)
	  (:jb '(:sub-program (,wrong-numargs) (:int 100))))))
     ((and max-args (= 0 min-args max-args))
      ;; exactly zero
      `((:testb :cl :cl)
	(:jnz '(:sub-program (,wrong-numargs) (:int 100)))))
     ((and max-args (= min-args max-args))
      ;; exact number
      (cond
       ((= 1 min-args max-args)
	`((:call (:edi ,(global-constant-offset 'assert-1arg)))))
       ((= 2 min-args max-args)
	`((:call (:edi ,(global-constant-offset 'assert-2args)))))
       ((= 3 min-args max-args)
	`((:call (:edi ,(global-constant-offset 'assert-3args)))))
       ((< min-args #x80)
	`((:cmpb ,min-args :cl)
	  (:jne '(:sub-program (,wrong-numargs) (:int 100)))))
       (t `((:cmpl ,(dpb min-args (byte 24 8) #x80) :ecx)
	    (:jne '(:sub-program (,wrong-numargs) (:int 100)))))))
     ((and max-args (/= min-args max-args) (= 0 min-args))
      ;; only maximum
      (if (< max-args #x80)
	  `((:cmpb ,max-args :cl)
	    (:ja '(:sub-program (,wrong-numargs) (:int 100))))
	`((:cmpl ,(dpb max-args (byte 24 8) #x80) :ecx)
	  (:ja '(:sub-program (,wrong-numargs) (:int 100))))))
     ((and max-args (/= min-args max-args))
      ;; both max and min
      (append (if (< min-args #x80)
		  `((:cmpb ,min-args :cl)
		    (:jb '(:sub-program (,wrong-numargs) (:int 100))))
		`((:cmpl ,(dpb min-args (byte 24 8) #x80) :ecx)
		  (:jb '(:sub-program (,wrong-numargs) (:int 100)))))
	      (if (< max-args #x80)
		  `((:cmpb ,max-args :cl)
		    (:ja '(:sub-program (,wrong-numargs) (:int 100))))
		`((:cmpl ,(dpb max-args (byte 24 8) #x80) :ecx)
		  (:ja '(:sub-program (,wrong-numargs) (:int 100)))))))
     (t (error "Don't know how to compile checking for ~A to ~A arguments."
	       min-args max-args)))))

(defun make-compiled-function-prelude (stack-frame-size env use-stack-frame-p
				       need-normalized-ecx-p frame-map
				       &key forward-2op-position
					    do-check-stack-p)
  "The prelude is compiled after the function's body is."
  (when (without-function-prelude-p env)
    (return-from make-compiled-function-prelude
      (when use-stack-frame-p
	`((:pushl :ebp)
	  (:movl :esp :ebp)
	  (:pushl :esi)))))
  (let ((required-vars (required-vars env))
	(min-args (min-args env))
	(max-args (max-args env)))
    (let (#+ignore (max-used-arg (loop for (binding) in frame-map
				     when (typep binding 'positional-function-argument)
				     maximize (function-argument-argnum binding)))
	  (stack-setup-size stack-frame-size)
	  (edx-needs-saving-p (and (edx-var env)
				   (new-binding-location (edx-var env) frame-map :default nil))))
      (multiple-value-bind (eax-ebx-code eax-ebx-code-post-stackframe)
	  (let* ((map0 (find-if (lambda (bb)
				  (and (typep (car bb) '(or required-function-argument
							 optional-function-argument))
				       (= 0 (function-argument-argnum (car bb)))))
				frame-map))
		 (location-0 (cdr map0))
		 (map1 (find-if (lambda (bb)
				  (and (typep (car bb) '(or required-function-argument
							 optional-function-argument))
				       (= 1 (function-argument-argnum (car bb)))))
				frame-map))
		 (location-1 (cdr map1))
		 (edx-location
		  (and (edx-var env)
		       (new-binding-location (edx-var env) frame-map :default nil))))
	    ;; (warn "l0: ~S, l1: ~S" location-0 location-1)
	    (cond
	     ((and (eq :ebx location-0) (eq :eax location-1))
	      `((:xchgl :eax :ebx)))
	     ((and (eql 1 location-0) (eql 2 location-1))
	      (decf stack-setup-size 2)
	      (when (eql 3 edx-location)
		(decf stack-setup-size 1)
		(setf edx-needs-saving-p nil))
	      (let (before-code after-code)
		(setf before-code
		  (append
		   `((:pushl :eax)
		     (:pushl :ebx))
		   (when (eql 3 edx-location)
		     `((:pushl :edx)))
		   ;; Keep pushing any sequentially following floating requireds.
		   ;; NB: Fixed-floats are used in-place, e.g above the stack-frame,
		   ;; so no need to worry about them.
		   (loop with expected-location = 2
		       for var in (cddr required-vars)
		       as binding = (movitz-binding var env)
		       if (and expected-location
			       (typep binding 'floating-required-function-argument)
			       (new-binding-located-p binding frame-map)
			       (= expected-location
				  (new-binding-location binding frame-map)))
		       do (decf stack-setup-size)
		       and do (incf expected-location)
		       and do (setq need-normalized-ecx-p t)
		       and collect
			   `(:pushl (:ebp (:ecx 4)
					  ,(* -4 (1- (function-argument-argnum binding)))))
		       else do (setf expected-location nil)
		       and do (when (and (typep binding 'floating-required-function-argument)
					 (new-binding-located-p binding frame-map))
				(setq need-normalized-ecx-p t)
				(setf after-code
				  (append
				   after-code
				   `((:movl (:ebp (:ecx 4)
						  ,(* -4 (1- (function-argument-argnum binding))))
					    :eax)
				     (:movl :eax (:ebp ,(stack-frame-offset
							 (new-binding-location binding frame-map)))))))))))
		(values before-code after-code)))
	     (t (values (append
			 (cond
			  ((and (eq :ebx location-0)
				(eql 1 location-1))
			   (decf stack-setup-size)
			   `((:pushl :ebx)
			     (:xchgl :eax :ebx)))
			  (t (append
			      (cond
			       ((eql 1 location-0)
				(decf stack-setup-size)
				'((:pushl :eax)))
			       (t (ecase location-0
				    ((nil :eax) nil)
				    (:ebx (assert (not location-1))
					  '((:movl :eax :ebx))))))
			      (cond
			       ((eql 1 location-1)
				(decf stack-setup-size)
				'((:pushl :ebx)))
			       (t (case location-1
				    ((nil :ebx) nil)
				    (:eax `((:movl :ebx :eax)))))))))
			 (cond
			  ((or (and (or (eql 1 location-0)
					(eql 1 location-1))
				    (eql 2 edx-location))
			       (and (not (integerp location-0))
				    (not (integerp location-1))
				    (eql 1 edx-location)))
			   (decf stack-setup-size)
			   (setf edx-needs-saving-p nil)
			   `((:pushl :edx)))))
			(loop for var in (cddr required-vars)
			    as binding = (movitz-binding var env)
			    when (and (typep binding 'floating-required-function-argument)
				      (new-binding-located-p binding frame-map))
			    append
			      `((:movl (:ebp (:ecx 4)
					     ,(* -4 (1- (function-argument-argnum binding))))
				       :eax)
				(:movl :eax (:ebp ,(stack-frame-offset
						    (new-binding-location binding frame-map)))))
			    and do (setq need-normalized-ecx-p t))))))
	(assert (not (minusp stack-setup-size)))
	(let ((stack-frame-init-code
	       (append (when (and do-check-stack-p
				  *compiler-auto-stack-checks-p*
				  (not (without-check-stack-limit-p env)))
			 `(((:fs-override)
			    :bound (:edi ,(global-constant-offset 'stack-bottom)) :esp)))
		       (when use-stack-frame-p
			`((:pushl :ebp)
			  (:movl :esp :ebp)
			  (:pushl :esi))))))
	  (values
	   (append
	    (cond
	     ((and (eql 1 min-args)
		   (eql 1 max-args))
	      (append (make-compiled-function-prelude-numarg-check min-args max-args)
		      '(entry%1op)
		      stack-frame-init-code))
	     ((and (eql 2 min-args)
		   (eql 2 max-args))
	      (append (make-compiled-function-prelude-numarg-check min-args max-args)
		      '(entry%2op)
		      stack-frame-init-code))
	     ((and (eql 3 min-args)
		   (eql 3 max-args))
	      (append (make-compiled-function-prelude-numarg-check min-args max-args)
		      '(entry%3op)
		      stack-frame-init-code))
	     (forward-2op-position
	      (append `((:cmpb 2 :cl)
			(:jne 'not-two-args)
			entry%2op
			(:movl (:esi ,forward-2op-position) :edx)
			(:movl (:edx ,(slot-offset 'movitz-symbol 'function-value)) :esi)
			(:jmp (:esi ,(slot-offset 'movitz-funobj 'code-vector%2op)))
			not-two-args)
		      stack-frame-init-code
		      (make-compiled-function-prelude-numarg-check min-args max-args)))
	     (t (append stack-frame-init-code
			(make-compiled-function-prelude-numarg-check min-args max-args))))
	    '(start-stack-frame-setup)
	    eax-ebx-code
	    (case stack-setup-size
	      (0 nil)
	      (1 '((:pushl :edi)))
	      (2 '((:pushl :edi) (:pushl :edi)))
	      (3 '((:pushl :edi) (:pushl :edi) (:pushl :edi)))
	      (t `((:subl ,(* 4 stack-setup-size) :esp))))
	    (when need-normalized-ecx-p
	      (cond
	       ;; normalize arg-count in ecx..
	       ((and max-args (= min-args max-args))
		(error "huh?"))
	       ((and max-args (<= 0 min-args max-args #x7f))
		`((:andl #x7f :ecx)))
	       ((>= min-args #x80)
		`((:shrl 8 :ecx)))
	       (t (let ((normalize (make-symbol "normalize-ecx"))
			(normalize-done (make-symbol "normalize-ecx-done")))
		    `((:testb :cl :cl)
		      (:js '(:sub-program (,normalize)
			     (:shrl 8 :ecx)
			     (:jmp ',normalize-done)))
		      (:andl #x7f :ecx)
		      ,normalize-done)))))
	    (when edx-needs-saving-p
	      `((:movl :edx (:ebp ,(stack-frame-offset (new-binding-location (edx-var env) frame-map))))))
	    eax-ebx-code-post-stackframe
	    (loop for binding in (potentially-lended-bindings env)
		as lended-cons-position = (getf (binding-lended-p binding) :stack-cons-location)
		as location = (new-binding-location binding frame-map :default nil)
		when (and (not (typep binding 'borrowed-binding))
			  lended-cons-position
			  location)
		append
		  (typecase binding
		    (required-function-argument
		     ;; (warn "lend: ~W => ~W" binding lended-cons-position)
		     (etypecase location
		       ((eql :eax)
			(warn "lending EAX..")
			`((:movl :edi
				 (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			  (:movl :eax
				 (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			  (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position)))
				 :eax)))
		       ((eql :argument-stack)
			`((:movl (:ebp ,(argument-stack-offset binding)) :edx)
			  (:movl :edi
				 (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			  (:movl :edx
				 (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			  (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position)))
				 :edx)
			  (:movl :edx
				 (:ebp ,(argument-stack-offset binding)))))
		       (integer
			`((:movl (:ebp ,(stack-frame-offset location))
				 :edx)
			  (:movl :edi
				 (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr 
			  (:movl :edx
				 (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			  (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position)))
				 :edx)
			  (:movl :edx
				 (:ebp ,(stack-frame-offset location)))))))
		    (closure-binding
		     ;; (warn "lend closure-binding: ~W => ~W" binding lended-cons-position)
		     (etypecase location
		       ((eql :argument-stack)
			`((:movl (:edi ,(global-constant-offset 'unbound-function)) :edx)
			  (:movl :edi (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			  (:movl :edx (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			  (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position))) :edx)
			  (:movl :edx (:ebp ,(argument-stack-offset binding)))))
		       (integer
			`((:movl (:edi ,(global-constant-offset 'unbound-function)) :edx)
			  (:movl :edi (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			  (:movl :edx (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			  (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position))) :edx)
			  (:movl :edx (:ebp ,(stack-frame-offset location)))))))
		    #+ignore
		    (t (etypecase location
			 ((eql :argument-stack)
			  `((:movl :edi (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			    (:movl :edi (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			    (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position))) :edx)
			    (:movl :edx (:ebp ,(argument-stack-offset binding)))))
			 (integer
			  `((:movl :edi (:ebp ,(stack-frame-offset lended-cons-position))) ; cdr
			    (:movl :edi (:ebp ,(stack-frame-offset (1+ lended-cons-position)))) ; car
			    (:leal (:ebp 1 ,(stack-frame-offset (1+ lended-cons-position))) :edx)
			    (:movl :edx (:ebp ,(stack-frame-offset location))))))))))
		  need-normalized-ecx-p))))))

(defparameter *restify-stats* (make-hash-table :test #'eql))

(defparameter *ll* (make-array 20 :initial-element 0))
(defparameter *xx* (make-array 20))

(defun install-arg-cmp (code have-normalized-ecx-p)
  (loop for i in code
      collecting
	(if (not (and (listp i) (eq :arg-cmp (car i))))
	    i
	  (let ((arg-count (second i)))
	    (cond
	     (have-normalized-ecx-p
	      `(:cmpl ,arg-count :ecx))
	     ((< arg-count #x80)
	      `(:cmpb ,arg-count :cl))
	     (t `(:cmpl ,(dpb arg-count (byte 24 8) #x80) :ecx)))))))

(defun make-function-arguments-init (funobj env function-body)
  "The arugments-init is compiled before the function's body is.
Return arg-init-code, new function-body, need-normalized-ecx-p."
  (when (without-function-prelude-p env)
    (return-from make-function-arguments-init
      (values nil function-body nil)))
  (let ((need-normalized-ecx-p nil)
	(required-vars (required-vars env))
	(optional-vars (optional-vars env))
	(rest-var (rest-var env))
	(key-vars (key-vars env))
	(allow-other-keys-p (allow-other-keys-p env)))
    (when (and (not rest-var)
	       key-vars
	       (not (= 1 (length key-vars))))
      (setf rest-var
	(keyword-function-argument-rest-var-name
	 (movitz-binding (decode-keyword-formal (first key-vars)) env))))
    (values (append
	     (loop ;;  with eax-optional-destructive-p = nil
		 for optional in optional-vars
		 as optional-var = (decode-optional-formal optional)
		 as binding = (movitz-binding optional-var env)
		 as last-optional-p = (and (null key-vars)
					   (not rest-var)
					   (= 1 (- (+ (length optional-vars) (length required-vars))
						   (function-argument-argnum binding))))
		 as supplied-p-var = (optional-function-argument-supplied-p-var binding)
		 as supplied-p-binding = (movitz-binding supplied-p-var env)
		 as not-present-label = (make-symbol (format nil "optional-~D-not-present" 
							     (function-argument-argnum binding)))
		 and optional-ok-label = (make-symbol (format nil "optional-~D-ok" 
							      (function-argument-argnum binding)))
		 unless (movitz-env-get optional-var 'ignore nil env nil)
		 append
		   (compiler-values-bind (&code init-code-edx &producer producer)
		       (compiler-call #'compile-form
			 :form (optional-function-argument-init-form binding)
			 :funobj funobj
			 :env env
			 :result-mode :edx)
		     (cond
		      #+ignore
		      ((and (eq 'compile-self-evaluating producer)
			    (= 0 (function-argument-argnum binding))
			    (not supplied-p-var))
		       (append `((:store-lexical ,binding :eax)
				 (:arg-cmp 1)
				 (:jge ',optional-ok-label))
			       (compiler-call #'compile-form
				 :form (optional-function-argument-init-form binding)
				 :funobj funobj
				 :env env
				 :result-mode binding)
			       (list optional-ok-label)))
		      #+ignore
		      ((and (eq 'compile-self-evaluating producer)
			    (= 1 (function-argument-argnum binding))
			    (not eax-optional-destructive-p)
			    (not supplied-p-var))
		       (append `((:store-lexical ,binding :ebx)
				 (:arg-cmp 2)
				 (:jge ',optional-ok-label))
			       (compiler-call #'compile-form
				 :form (optional-function-argument-init-form binding)
				 :funobj funobj
				 :env env
				 :result-mode binding)
			       (list optional-ok-label)))
		      ((eq 'compile-self-evaluating producer)
		       `(,@(when supplied-p-var
			     `((:store-lexical ,supplied-p-binding :edi :type null)))
			   ,@(if (optional-function-argument-init-form binding)
				 (append init-code-edx `((:store-lexical ,binding :edx :type t)))
			       `((:store-lexical ,binding :edi :type null)))
			   (:arg-cmp ,(function-argument-argnum binding))
			   (:jbe ',not-present-label)
			   ,@(case (function-argument-argnum binding)
			       (0 `((:store-lexical ,binding :eax :type t)))
			       (1 `((:store-lexical ,binding :ebx :type t)))
			       (t (cond
				   (last-optional-p
				    `((:movl (:ebp  ,(* 4 (- (1+ (function-argument-argnum binding))
							     -1 (function-argument-argnum binding))))
					     :eax)
				      (:store-lexical ,binding :eax :type t)))
				   (t (setq need-normalized-ecx-p t)
				      `((:movl (:ebp (:ecx 4) ,(* -4 (1- (function-argument-argnum binding))))
					       :eax)
					(:store-lexical ,binding :eax :type t))))))
			   ,@(when supplied-p-var
			       `((:movl (:edi ,(global-constant-offset 't-symbol)) :eax)
				 (:store-lexical ,supplied-p-binding :eax
						 :type (eql ,(image-t-symbol *image*)))))
			   ,not-present-label))
		      (t  #+ignore (when (= 0 (function-argument-argnum binding))
				     (setf eax-optional-destructive-p t))
			 `((:arg-cmp ,(function-argument-argnum binding))
			   (:jbe ',not-present-label)
			   ,@(when supplied-p-var
			       `((:movl (:edi ,(global-constant-offset 't-symbol)) :eax)
				 (:store-lexical ,supplied-p-binding :eax
						 :type (eql ,(image-t-symbol *image*)))))
			   ,@(case (function-argument-argnum binding)
			       (0 `((:store-lexical ,binding :eax :type t)))
			       (1 `((:store-lexical ,binding :ebx :type t)))
			       (t (cond
				   (last-optional-p
				    `((:movl (:ebp  ,(* 4 (- (1+ (function-argument-argnum binding))
							     -1 (function-argument-argnum binding))))
					     :eax)
				      (:store-lexical ,binding :eax :type t)))
				   (t (setq need-normalized-ecx-p t)
				      `((:movl (:ebp (:ecx 4) ,(* -4 (1- (function-argument-argnum binding))))
					       :eax)
					(:store-lexical ,binding :eax :type t))))))
			   (:jmp ',optional-ok-label)
			   ,not-present-label
			   ,@(when supplied-p-var
			       `((:store-lexical ,supplied-p-binding :edi :type null)))
			   ,@(when (and (= 0 (function-argument-argnum binding))
					(not last-optional-p))
			       `((:pushl :ebx))) ; protect ebx
			   ,@(if (optional-function-argument-init-form binding)
				 (append '((:pushl :ecx))
					 (when (= 0 (function-argument-argnum binding))
					   `((:pushl :ebx)))
					 init-code-edx
					 `((:store-lexical ,binding :edx :type t))
					 (when (= 0 (function-argument-argnum binding))
					   `((:popl :ebx)))
					 `((:popl :ecx)))
			       (progn (error "WEgewgew")
				      `((:store-lexical ,binding :edi :type null))))
			   ,@(when (and (= 0 (function-argument-argnum binding))
					(not last-optional-p))
			       `((:popl :ebx))) ; protect ebx
			   ,optional-ok-label)))))
	     (when rest-var
	       (let* ((rest-binding (movitz-binding rest-var env))
		      (rest-position (function-argument-argnum rest-binding)))
		 (assert (or (typep rest-binding 'hidden-rest-function-argument)
			     (movitz-env-get rest-var 'dynamic-extent nil env)
			     (movitz-env-get rest-var 'ignore nil env))
		     ()
		   "&REST variable ~S must be dynamic-extent." rest-var)
		 (setq need-normalized-ecx-p t)
		 (append (make-immediate-move rest-position :edx)
			 `((:call (:edi ,(global-constant-offset 'restify-dynamic-extent)))
			   (:init-lexvar ,rest-binding
					 :init-with-register :eax
					 :init-with-type list)))))
	     (cond
	      ;; &key processing..
	      ((and (not rest-var)
		    (= 1 (length key-vars)))
	       (let* ((key-var-name (decode-keyword-formal (first key-vars)))
		      (binding (movitz-binding key-var-name env))
		      (position (function-argument-argnum
				 (movitz-binding (keyword-function-argument-rest-var-name binding) env)))
		      (supplied-p-var (optional-function-argument-supplied-p-var binding))
		      (supplied-p-binding (movitz-binding supplied-p-var env)))
		 (setq need-normalized-ecx-p t)
		 (cond
		  ((and (movitz-constantp (optional-function-argument-init-form binding))
			(< 1 position))
		   `(
		     ,@(compiler-call #'compile-self-evaluating
			 :form (eval-form (optional-function-argument-init-form binding) env nil)
			 :funobj funobj
			 :env env
			 :result-mode :ebx)
		     ,@(when supplied-p-var
			 `((:store-lexical ,supplied-p-binding :edi :type null)))
		     (:arg-cmp ,(+ 2 position))
		     (:jb 'default-done)
		     (:movl (:ebp (:ecx 4) ,(* -4 (1- position))) :eax)
		     (:load-constant ,(movitz-read (keyword-function-argument-keyword-name binding)) :eax :op :cmpl)
		     #+ignore (:cmpl (:esi ,(movitz-funobj-intern-constant
					     funobj
					     (movitz-read (keyword-function-argument-keyword-name binding))))
				     :eax)
		     ,@(if allow-other-keys-p
			   `((:jne 'default-done))
			 `((:jne '(:sub-program (unknown-key) (:int 101)))))
		     ,@(when supplied-p-var
			 `((:movl (:edi ,(global-constant-offset 't-symbol)) :eax)
			   (:store-lexical ,supplied-p-binding :eax
					   :type (eql ,(image-t-symbol *image*)))))
		     (:movl (:ebp (:ecx 4) ,(* -4 (1- (1+ position)))) :ebx)
		     default-done
		     (:store-lexical ,binding :ebx :type t)))
		  (t `((:arg-cmp ,(+ 2 position))
		       (:jb '(:sub-program (default)
			      ,@(append
				 (when supplied-p-var
				   `((:store-lexical ,supplied-p-binding :edi
						     :type null)))
				 (compiler-call #'compile-form
				   :form (optional-function-argument-init-form binding)
				   :funobj funobj
				   :env env
				   :result-mode :ebx)
				 `((:jmp 'default-done)))))
		       ,@(case position
			   (0 `((:load-constant ,(movitz-read (keyword-function-argument-keyword-name binding)) :eax :op :cmpl))
			      #+ignore `((:cmpl (:esi ,(movitz-funobj-intern-constant
							funobj
							(movitz-read (keyword-function-argument-keyword-name binding))))
						:eax)))
			   (1 `((:load-constant ,(movitz-read (keyword-function-argument-keyword-name binding)) :ebx :op :cmpl))
			      #+ignore `((:cmpl (:esi ,(movitz-funobj-intern-constant
							funobj
							(movitz-read (keyword-function-argument-keyword-name binding))))
						:ebx)))
			   (t `((:load-constant ,(movitz-read (keyword-function-argument-keyword-name binding)) :eax :op :cmpl))
			      #+ignore `((:movl (:ebp (:ecx 4) ,(* -4 (1- position))) :eax)
					 (:cmpl (:esi ,(movitz-funobj-intern-constant
							funobj
							(movitz-read (keyword-function-argument-keyword-name binding))))
						:eax))))
		       ,@(if allow-other-keys-p
			     `((:jne 'default))
			   `((:jne '(:sub-program (unknown-key) (:int 101)))))
		       ,@(when supplied-p-var
			   `((:movl (:edi ,(global-constant-offset 't-symbol)) :eax)
			     (:store-lexical ,supplied-p-binding :eax
					     :type (eql ,(image-t-symbol *image*)))))
		       ,@(case position
			   (0 nil)	; it's already in ebx
			   (t `((:movl (:ebp (:ecx 4) ,(* -4 (1- (1+ position)))) :ebx))))
		       default-done
		       (:store-lexical ,binding :ebx :type t))))))
	      (t #+ignore
		 (pushnew (movitz-print (movitz-funobj-name funobj))
			  (aref *xx* (length key-vars)))
		 (loop with rest-binding = (movitz-binding rest-var env)
		     for key-var in key-vars
		     as key-var-name = (decode-keyword-formal key-var)
		     as binding = (movitz-binding key-var-name env)
		     as supplied-p-var = (optional-function-argument-supplied-p-var binding)
		     as supplied-p-binding = (movitz-binding supplied-p-var env)
		     and keyword-ok-label = (make-symbol (format nil "keyword-~A-ok" key-var-name))
		     and keyword-not-supplied-label = (gensym)
		     do (assert binding)
		     if (not (movitz-constantp (optional-function-argument-init-form binding)))
		     append
		       `((:init-lexvar ,binding)
			 (:load-constant ,(movitz-read (keyword-function-argument-keyword-name binding)) :ecx)
			 (:load-lexical ,rest-binding :ebx)
			 (:call (:edi ,(global-constant-offset 'keyword-search)))
			 (:jz ',keyword-not-supplied-label)
			 (:store-lexical ,binding :eax :type t)
			 ,@(when supplied-p-var
			     `((:movl (:edi ,(global-constant-offset 't-symbol)) :eax)
			       (:init-lexvar ,supplied-p-binding
					     :init-with-register :eax
					     :init-with-type (eql ,(image-t-symbol *image*)))))
			 (:jmp ',keyword-ok-label)
			 ,keyword-not-supplied-label
			 ,@(when supplied-p-var
			     `((:store-lexical ,supplied-p-binding :edi :type null)))
			 ,@(compiler-call #'compile-form
			     :form (optional-function-argument-init-form binding)
			     :env env
			     :funobj funobj
			     :result-mode binding)
			 ,keyword-ok-label)
		     else append
			  (append (when supplied-p-var
				    `((:init-lexvar ,supplied-p-binding
						    :init-with-register :edi
						    :init-with-type null)))
				  (compiler-call #'compile-self-evaluating
				    :form (eval-form (optional-function-argument-init-form binding) env)
				    :env env
				    :funobj funobj
				    :result-mode :eax)
				  `((:load-constant
				     ,(movitz-read (keyword-function-argument-keyword-name binding)) :ecx)
				    (:load-lexical ,rest-binding :ebx)
				    (:call (:edi ,(global-constant-offset 'keyword-search))))
				  (when supplied-p-var
				    `((:jz ',keyword-not-supplied-label)
				      (:movl (:edi ,(global-constant-offset 't-symbol)) :ebx)
				      (:store-lexical ,supplied-p-binding :ebx
						      :type (eql ,(image-t-symbol *image*)))
				      ,keyword-not-supplied-label))
				  `((:init-lexvar ,binding
						  :init-with-register :eax
						  :init-with-type t)))))))
	    ;; shadowing variables..
	    (if (special-variable-shadows env)
		`(muerte.cl::let ,(special-variable-shadows env) ,function-body)
	      function-body)
	    need-normalized-ecx-p)))

(defun make-compiled-function-postlude (funobj env use-stack-frame-p)
  (declare (ignore funobj env))
  (let ((p '((:movl (:ebp -4) :esi)
	     (:ret))))
    (if use-stack-frame-p
	(cons '(:leave) p)
      p)))

(defun complement-boolean-result-mode (mode)
  (etypecase mode
    (keyword
     (ecase mode
       (:boolean-greater       :boolean-less-equal)
       (:boolean-less          :boolean-greater-equal)
       (:boolean-greater-equal :boolean-less)
       (:boolean-less-equal    :boolean-greater)
       (:boolean-below         :boolean-above-equal)
       (:boolean-above         :boolean-below-equal)
       (:boolean-below-equal   :boolean-above)
       (:boolean-above-equal   :boolean-below)
       (:boolean-zf=1          :boolean-zf=0)
       (:boolean-zf=0          :boolean-zf=1)
       (:boolean-cf=1          :boolean-cf=0)
       (:boolean-cf=0          :boolean-cf=1)))
    (cons
     (let ((args (cdr mode)))
       (ecase (car mode)
	 (:boolean-ecx
	  (list :boolean-ecx (second args) (first args)))
	 (:boolean-branch-on-true
	  (cons :boolean-branch-on-false args))
	 (:boolean-branch-on-false
	  (cons :boolean-branch-on-true args)))))))

(defun make-branch-on-boolean (mode label &key invert)
  (list (ecase (if invert (complement-boolean-result-mode mode) mode)
	  (:boolean-greater       :jg)	; ZF=0 and SF=OF
	  (:boolean-greater-equal :jge)	; SF=OF
	  (:boolean-less          :jl)	; SF!=OF
	  (:boolean-less-equal    :jle)	; ZF=1 or SF!=OF
	  (:boolean-below         :jb)
	  (:boolean-above         :ja)
	  (:boolean-below-equal   :jbe)
	  (:boolean-above-equal   :jae)
	  (:boolean-zf=1          :jz)
	  (:boolean-zf=0          :jnz)
	  (:boolean-cf=1          :jc)
	  (:boolean-cf=0          :jnc)
	  (:boolean-true          :jmp))
	(list 'quote label)))


(defun make-cmov-on-boolean (mode src dst &key invert)
  (list (ecase (if invert (complement-boolean-result-mode mode) mode)
	  (:boolean-greater       :cmovg) ; ZF=0 and SF=OF
	  (:boolean-greater-equal :cmovge) ; SF=OF
	  (:boolean-less          :cmovl) ; SF!=OF
	  (:boolean-less-equal    :cmovle) ; ZF=1 or SF!=OF
	  (:boolean-zf=1          :cmovz)
	  (:boolean-zf=0          :cmovnz)
	  (:boolean-cf=1          :cmovc)
	  (:boolean-cf=0          :cmovnc))
	src dst))

(defun return-satisfies-result-p (desired-result returns-provided)
  (or (eq desired-result returns-provided)
      (case desired-result
	(:ignore t)
	((:eax :single-value)
	 (member returns-provided '(:eax :multiple-values :single-value)))
	(:function
	 (member returns-provided '(:multiple-values :function)))
	(:boolean
	 (member returns-provided +boolean-modes+)))))
  
(defun make-result-and-returns-glue (desired-result returns-provided
				     &optional code
				     &key (type t) provider really-desired)
  "Returns new-code and new-returns-provided."
  (declare (optimize (debug 3)))
  (case returns-provided
    (:non-local-exit
     ;; when CODE does a non-local exit, we certainly don't need any glue.
     (return-from make-result-and-returns-glue
       (values code :non-local-exit))))
  (multiple-value-bind (new-code new-returns-provided)
      (case (result-mode-type desired-result)
	((:lexical-binding)
	 (case (result-mode-type returns-provided)
	   (:lexical-binding
	    (assert (eq desired-result returns-provided) ()
	      "Desired-result ~S produced a value in ~S for code ~W." desired-result returns-provided code)
	    (values code returns-provided))
	   ((:eax :multiple-values)
	    (values (append code
			    `((:store-lexical ,desired-result :eax
					      :type ,(type-specifier-primary type))))
		    desired-result))
	   ((:ebx)
	    (values (append code
			    `((:store-lexical ,desired-result
					      ,(result-mode-type returns-provided)
					      :type ,(type-specifier-primary type))))
		    desired-result))))
	(:ignore (values code :nothing))
	((:boolean-ecx)
	 (let ((true (first (operands desired-result)))
	       (false (second (operands desired-result))))
	   (ecase (operator returns-provided)
	     (:boolean-ecx
	      (if (equal (operands desired-result)
			 (operands returns-provided))
		  (values code desired-result)
		))
	     (:boolean-cf=1
	      (cond
	       ((and (= -1 true) (= 0 false))
		(values (append code
				`((:sbbl :ecx :ecx)))
			'(:boolean-ecx -1 0)))
	       ((and (= 0 true) (= -1 false))
		(values (append code
				`((:sbbl :ecx :ecx)
				  (:notl :ecx)))
			'(:boolean-ecx 0 -1)))
	       (t (error "Don't know modes ~S => ~S." returns-provided desired-result))))
	     (:eax
	      (make-result-and-returns-glue desired-result
					    :boolean-cf=1
					    (append code
						    `((:leal (:eax ,(- (image-nil-word *image*)))
							     :ecx)
						      (:subl 1 :ecx)))
					    :type type
					    :provider provider
					    :really-desired desired-result)))))
	(:boolean-branch-on-true
	 ;; (warn "rm :b-true with ~S." returns-provided)
	 (ecase (operator returns-provided)
	   (:boolean-branch-on-true
	    (assert (eq (operands desired-result) (operands returns-provided)))
	    (values code returns-provided))
	   ((:eax :multiple-values)
	    (values (append code
			    `((:cmpl :edi :eax)
			      (:jne ',(operands desired-result))))
		    desired-result))
	   ((:ebx :ecx :edx)
	    (values (append code
			    `((:cmpl :edi ,returns-provided)
			      (:jne ',(operands desired-result))))
		    desired-result))
	   (:nothing
	    ;; no branch, nothing is nil is false.
	    (values code desired-result))
	   (#.+boolean-modes+
	    (values (append code
			    (list (make-branch-on-boolean returns-provided (operands desired-result))))
		    desired-result))))
	(:boolean-branch-on-false
	 (ecase (operator returns-provided)
	   (:boolean-branch-on-false
	    (assert (eq (operands desired-result)
			(operands returns-provided)))
	    (values code desired-result))
	   (:nothing
	    (values (append code
			    `((:jmp ',(operands desired-result))))
		    desired-result))
	   (#.+boolean-modes+
	    (values (append code
			    (list (make-branch-on-boolean returns-provided (operands desired-result)
							  :invert t)))
		    desired-result))
	   ((:ebx :ecx :edx)
	    (values (append code
			    `((:cmpl :edi ,returns-provided)
			      (:je ',(operands desired-result))))
		    desired-result))
	   ((:eax :multiple-values)
	    (values (append code
			    `((:cmpl :edi :eax)
			      (:je ',(operands desired-result))))
		    desired-result))))
	(:untagged-fixnum-eax
	 (case returns-provided
	   (:untagged-fixnum-eax
	    (values code :untagged-fixnum-eax))
	   ((:eax :single-value :multiple-values :function)
	    (values (append code
			    `((:testb ,+movitz-fixnum-zmask+ :al)
			      (:jnz '(:sub-program (not-an-integer) (:int 107))) ;
			      (:sarl ,+movitz-fixnum-shift+ :eax)))
		    :untagged-fixnum-eax))))
	(:untagged-fixnum-ecx
	 (case returns-provided
	   (:untagged-fixnum-ecx
	    (values code :untagged-fixnum-ecx))
	   ((:eax :single-value :multiple-values :function)
	    (values (append code
			    `((:testb ,+movitz-fixnum-zmask+ :al)
			      (:jnz '(:sub-program (not-an-integer) (:int 107))) ;
			      (:movl :eax :ecx)
			      (:sarl ,+movitz-fixnum-shift+ :ecx)))
		    :untagged-fixnum-ecx))
	   (:ecx
	    (values (append code
			    `((:testb ,+movitz-fixnum-zmask+ :cl)
			      (:jnz '(:sub-program (not-an-integer) (:int 107))) ;
			      (:sarl ,+movitz-fixnum-shift+ :ecx)))
		    :untagged-fixnum-ecx))))
	((:single-value :eax)
	 (case (operator returns-provided)
	   (:untagged-fixnum-eax
	    (values (append code `((:shll ,+movitz-fixnum-shift+ :eax))) :eax))
	   (:values
	    (case (first (operands returns-provided))
	      (0 (values (append code '((:movl :edi :eax)))
			 :eax))
	      (t (values code :eax))))
	   ((:single-value :eax :function :multiple-values)
	    (values code :eax))
	   (:nothing
	    (values (append code '((:movl :edi :eax)))
		    :eax))
	   ((:ebx :ecx :edx :edi)
	    (values (append code `((:movl ,returns-provided :eax)))
		    :eax))
	   (:boolean-ecx
	    (let ((true-false (operands returns-provided)))
	      (cond
	       ((equal '(0 1) true-false)
		(values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-zero))
					      :eax)))
			:eax))
	       ((equal '(1 0) true-false)
		(values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-one))
					      :eax)))
			:eax))
	       (t (error "Don't know ECX mode ~S." returns-provided)))))
;;;	   (:boolean-ecx=0
;;;	    (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-zero))
;;;					  :eax)))
;;;		    :eax))
;;;	   (:boolean-ecx=1
;;;	    (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-one))
;;;					  :eax)))
;;;		    :eax))
	   (:boolean-cf=1
	    (values (append code
			    `((:sbbl :ecx :ecx)
			      (:movl (:edi (:ecx 4) ,(global-constant-offset 'null-cons))
				     :eax)))
		    :eax))
	   (#.+boolean-modes+
	    ;; (warn "bool for ~S" returns-provided)
	    (let ((boolean-false-label (make-symbol "boolean-false-label")))
	      (values (append code
			      '((:movl :edi :eax))
			      (if *compiler-use-cmov-p*
				  `(,(make-cmov-on-boolean returns-provided
							   `(:edi ,(global-constant-offset 't-symbol))
							   :eax
							   :invert nil))
				`(,(make-branch-on-boolean returns-provided
							   boolean-false-label
							   :invert t)
				  (:movl (:edi ,(global-constant-offset 't-symbol))
					 :eax)
				  ,boolean-false-label)))
		      :eax)))))
	((:ebx :ecx :edx :esp :esi)
	 (if (eq returns-provided desired-result)
	     (values code returns-provided)
	   (case (operator returns-provided)
	     #+ignore
	     (:untagged-fixnum-eax
	      (values (append code
			      `((:leal ((:eax 4)) ,desired-result)))
		      desired-result))
	     (:nothing
	      (values (append code
			      `((:movl :edi ,desired-result)))
		      desired-result))
	     ((:ebx :ecx :edx :esp)
	      (values (append code
			      `((:movl ,returns-provided ,desired-result)))
		      desired-result))
	     ((:eax :single-value :multiple-values :function)
	      (values (append code
			      `((:movl :eax ,desired-result)))
		      desired-result))
	     (:boolean-ecx
	      (let ((true-false (operands returns-provided)))
		(cond
		 ((equal '(0 1) true-false)
		  (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-zero))
						,desired-result)))
			  desired-result))
		 ((equal '(1 0) true-false)
		  (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-one))
						,desired-result)))
			  desired-result))
		 (t (error "Don't know ECX mode ~S." returns-provided)))))
;;;	     (:boolean-ecx=0
;;;	      (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-zero))
;;;					    ,desired-result)))
;;;		      desired-result))
;;;	     (:boolean-ecx=1
;;;	      (values (append code `((:movl (:edi (:ecx 4) ,(global-constant-offset 'boolean-one))
;;;					    ,desired-result)))
;;;		      desired-result))
	     (:boolean-cf=1
	      (values (append code
			      `((:sbbl :ecx :ecx)
				(:movl (:edi (:ecx 4) ,(global-constant-offset 'null-cons))
				       ,desired-result)))
		      desired-result))
	     (#.+boolean-modes+
	      ;; (warn "bool to ~S for ~S" desired-result returns-provided)
	      (values (append code
			      (cond
			       (*compiler-use-cmov-p*
				`((:movl :edi ,desired-result)
				  ,(make-cmov-on-boolean returns-provided
							 `(:edi ,(global-constant-offset 't-symbol))
							 desired-result)))
			       ((not *compiler-use-cmov-p*)
				(let ((boolean-false-label (make-symbol "boolean-false-label")))
				  `((:movl :edi ,desired-result)
				    ,(make-branch-on-boolean returns-provided
							     boolean-false-label
							     :invert t)
				    (:movl (:edi ,(global-constant-offset 't-symbol))
					   ,desired-result)
				    ,boolean-false-label)))))
		      desired-result)))))
	(:push
	 (case returns-provided
	   (:push (values code :push))
	   (:nothing
	    (values (append code '((:pushl :edi)))
		    :push))
	   ((:single-value :eax :multiple-values :function)
	    (values (append code `((:pushl :eax)))
		    :push))
	   ((:ebx :ecx :edx)
	    (values (append code `((:pushl ,returns-provided)))
		    :push))))
	(:values
;;;	 (warn "desired: ~W, provided: ~W" desired-result returns-provided)
	 (case (operator returns-provided)
	   (:values
	    (values code returns-provided))
	   (:multiple-values
	    (values code :values))
	   (t (values (make-result-and-returns-glue :eax returns-provided code)
		      '(:values 1)))))
	((:multiple-values :function)
	 (case (operator returns-provided)
	   ((:multiple-values :function)
	    (values code :multiple-values))
	   (:values
	    (case (first (operands returns-provided))
	      (0 (values (append code '((:movl :edi :eax) (:xorl :ecx :ecx) (:stc)))
			 :multiple-values))
	      (1 (values (append code '((:clc)))
			 :multiple-values))
	      ((nil) (values code :multiple-values))
	      (t (values (append code (make-immediate-move (first (operands returns-provided)) :ecx) '((:stc)))
			 :multiple-values))))
	   (t (values (append (make-result-and-returns-glue :eax
							    returns-provided
							    code)
			      '((:clc)))
		      :multiple-values)))))
    (unless new-returns-provided
      (multiple-value-setq (new-code new-returns-provided)
	(case (operator returns-provided)
	  (#.+boolean-modes+
	   (make-result-and-returns-glue desired-result :eax
					 (make-result-and-returns-glue :eax returns-provided code
								       :type type
								       :provider provider
								       :really-desired desired-result)
					 :type type
					 :provider provider))
	  (:untagged-fixnum-ecx
	   (case (result-mode-type desired-result)
	     ((:eax :ebx :ecx :edx)
	      (values (append code `((:leal ((:ecx ,+movitz-fixnum-factor+) :edi ,(edi-offset))
					    ,desired-result)))
		      desired-result))
	     (t (make-result-and-returns-glue desired-result :eax
					      (make-result-and-returns-glue :eax :untagged-fixnum-ecx code
									    :provider provider
									    :really-desired desired-result)
					      :provider provider))))
	  (:untagged-fixnum-eax
	   (make-result-and-returns-glue desired-result :eax
					 (make-result-and-returns-glue :eax :untagged-fixnum-eax code
								       :provider provider
								       :really-desired desired-result)
					 :provider provider)))))
    (assert new-returns-provided ()
      "Don't know how to match desired-result ~S with returns-provided ~S~@[ from ~S~]."
      (or really-desired desired-result) returns-provided provider)
    (values new-code new-returns-provided)))

(define-compiler compile-form (&all form-info &result-mode result-mode)
  "3.1.2.1 Form Evaluation. Guaranteed to honor RESULT-MODE."
  (compiler-values-bind (&all unprotected-values &code form-code &returns form-returns
			 &producer producer &type form-type)
      (compiler-call #'compile-form-unprotected :forward form-info)
    (multiple-value-bind (new-code new-returns-provided)
	(make-result-and-returns-glue result-mode form-returns form-code
				      :provider producer
				      :type form-type)
      (compiler-values (unprotected-values)
	:type form-type
	:producer producer
	:code new-code
	:returns new-returns-provided))))

(define-compiler compile-form-selected (&all form-info &result-mode result-modes)
  "3.1.2.1 Form Evaluation. Guaranteed to honor one of RESULT-MODE, which
for this call (exclusively!) is a list of the acceptable result-modes, where
the first one takes preference. Note that :non-local-exit might also be returned."
  (check-type result-modes list "a list of result-modes")
  (compiler-values-bind (&all unprotected-values &code form-code &returns form-returns
			 &producer producer &type form-type)
      (compiler-call #'compile-form-unprotected
	:result-mode (car result-modes)
	:forward form-info)
    (if (member form-returns result-modes)
	(compiler-values (unprotected-values))
      (compiler-call #'compile-form
	:result-mode (car result-modes)
	:forward form-info))))

(define-compiler compile-form-to-register (&all form-info)
  (compiler-values-bind (&all unprotected-values &code form-code &returns form-returns
			 &final-form final-form &producer producer &type form-type)
      (compiler-call #'compile-form-unprotected
	:result-mode :eax
	:forward form-info)
    (cond
     #+ignore
     ((and (typep final-form 'required-function-argument)
	   (= 1 (function-argument-argnum final-form)))
      (compiler-call #'compile-form
	:result-mode :ebx
	:forward form-info))
     ((member form-returns '(:eax :ebx :ecx :edx :edi))
      (compiler-values (unprotected-values)))
     (t (compiler-call #'compile-form
	  :result-mode :eax
	  :forward form-info)))))
  
(define-compiler compile-form-unprotected (&all all &form form &result-mode result-mode)
  "3.1.2.1 Form Evaluation. May not honor RESULT-MODE.
That is, RESULT-MODE is taken to be a suggestion, not an imperative."
  (typecase form
    (symbol (compiler-call #'compile-symbol :forward all))
    (cons   (compiler-call #'compile-cons :forward all))
    (t      (compiler-call #'compile-self-evaluating :forward all))))

(defun lambda-form-p (form)
  (and (listp form)
       (eq 'cl:lambda (first form))))

(defun function-name-p (operator)
  (or (and (symbolp operator) operator)
      (setf-name operator)))

(define-compiler compile-cons (&all all &form form &env env)
  "3.1.2.1.2 Conses as Forms"
  (let ((operator (car form)))
    (if (and (symbolp operator) (movitz-special-operator-p operator))
	(compiler-call (movitz-special-operator-compiler operator) :forward all)
      (let* ((compiler-macro-function (movitz-compiler-macro-function operator env))
	     (compiler-macro-expansion (and compiler-macro-function
					    (funcall *movitz-macroexpand-hook*
						     compiler-macro-function
						     form env))))
	(cond
	 ((and compiler-macro-function
	       (not (movitz-env-get operator 'notinline nil env))
	       (not (eq form compiler-macro-expansion)))
	  (compiler-call #'compile-form-unprotected :forward all :form compiler-macro-expansion))
	 ((movitz-constantp form env)
	  (compiler-call #'compile-constant-compound :forward all))
	 ((lambda-form-p operator)	; 3.1.2.1.2.4
	  (compiler-call #'compile-lambda-form :forward all))
	 ((symbolp operator)
	  (cond
	   ((movitz-special-operator-p operator)
	    (compiler-call (movitz-special-operator-compiler operator) :forward all))
	   ((movitz-macro-function operator env)
	    (compiler-call #'compile-macro-form :forward all))
	   ((movitz-operator-binding operator env)
	    (compiler-call #'compile-apply-lexical-funobj :forward all))
	   (t (compiler-call #'compile-apply-symbol :forward all))))
	 (t (error "Don't know how to compile compound form ~A" form)))))))

(define-compiler compile-compiler-macro-form (&all all &form form &env env)
  (compiler-call #'compile-form-unprotected
    :forward all
    :form (funcall *movitz-macroexpand-hook*
		   (movitz-compiler-macro-function (car form) env)
		   form env)))

(define-compiler compile-macro-form (&all all &form form &env env)
  "3.1.2.1.2.2 Macro Forms"
  (let* ((operator (car form))
	 (macro-function (movitz-macro-function operator env)))
    (compiler-call #'compile-form-unprotected
      :forward all
      :form (funcall *movitz-macroexpand-hook* macro-function form env))))

(define-compiler compile-lexical-macro-form (&all all &form form &env env)
  "Compiles MACROLET and SYMBOL-MACROLET forms."
  (compiler-call #'compile-form-unprotected
    :forward all
    :form (funcall *movitz-macroexpand-hook*
		   (macro-binding-expander (movitz-operator-binding form env))
		   form env)))

(defun like-compile-macroexpand-form (form env)
  (typecase form
    ;; (symbol (compile-macroexpand-symbol form funobj env top-level-p result-mode))
    (cons   (like-compile-macroexpand-cons form env))
    (t      (values form nil))))

(defun like-compile-macroexpand-cons (form env)
  "3.1.2.1.2 Conses as Forms"
  (let* ((operator (car form))
	 (notinline (movitz-env-get operator 'notinline nil env))
	 (compiler-macro-function (movitz-compiler-macro-function operator env))
	 (compiler-macro-expansion (and compiler-macro-function
					(funcall *movitz-macroexpand-hook*
						 compiler-macro-function
						 form env))))
    (cond
     ((and (not notinline)
	   compiler-macro-function
	   (not (eq form compiler-macro-expansion)))
      (values compiler-macro-expansion t))
     ((symbolp operator)
      (cond
       ((movitz-macro-function operator env)
	(values (funcall *movitz-macroexpand-hook*
			 (movitz-macro-function operator env)
			 form env)
		t))
       (t form)))
     (t form))))

(defun make-compiled-stack-restore (stack-displacement result-mode returns)
  "Return the code required to reset the stack according to stack-displacement,
result-mode, and returns (which specify the returns-mode of the immediately
preceding code). As secondary value, returns the new :returns value."
  (flet ((restore-by-pop (scratch)
	   (case stack-displacement
	     (1 `((:popl ,scratch)))
	     (2 `((:popl ,scratch) (:popl ,scratch))))))
    (if (zerop stack-displacement)
	(values nil returns)
      (ecase (result-mode-type result-mode)
	(:function
	 (values nil returns))
	((:multiple-values :values)
	 (ecase returns
	   (:multiple-values
	    (values `((:leal (:esp ,(* 4 stack-displacement)) :esp))
		    :multiple-values))
	   ((:single-value :eax :ebx)
	    (values `((:addl ,(* 4 stack-displacement) :esp))
		    :multiple-values)))) ; assume this addl will set CF=0
	((:single-value :eax :ebx :ecx :edx :push :lexical-binding
	  :boolean :boolean-branch-on-false :boolean-branch-on-true)
	 (ecase returns
	   (#.+boolean-modes+
	    (values (or (restore-by-pop :eax)
			`((:leal (:esp ,(* 4 stack-displacement)) :esp))) ; preserve all flags
		    returns))
	   (:ebx
	    (values (or (restore-by-pop :eax)
			`((:addl ,(* 4 stack-displacement) :esp)))
		    :ebx))
	   ((:multiple-values :single-value :eax)
	    (values (or (restore-by-pop :ebx)
			`((:addl ,(* 4 stack-displacement) :esp)))
		    :eax))))
	(:ignore
	 (values (or (restore-by-pop :eax)
		     `((:addl ,(* 4 stack-displacement) :esp)))
		 :nothing))))))
    
(define-compiler compile-apply-symbol (&form form &funobj funobj &env env
					     &result-mode result-mode)
  "3.1.2.1.2.3 Function Forms"
  (destructuring-bind (operator &rest arg-forms)
      form
    #+ignore (when (and (eq result-mode :function)
			(eq operator (movitz-print (movitz-funobj-name funobj))))
	       (warn "Tail-recursive call detected."))
    (pushnew (cons operator muerte.cl::*compile-file-pathname*)
	     (image-called-functions *image*)
	     :key #'first)
    (multiple-value-bind (arguments-code stack-displacement arguments-modifies)
	(make-compiled-argument-forms arg-forms funobj env)
      (multiple-value-bind (stack-restore-code new-returns)
	  (make-compiled-stack-restore stack-displacement result-mode :multiple-values)
	(compiler-values ()
	  :returns new-returns
	  :functional-p nil
	  :modifies arguments-modifies
	  :code (append arguments-code
			(if (and t (eq operator (movitz-print (movitz-funobj-name funobj)))) ; recursive?
			    (make-compiled-funcall-by-esi (length arg-forms))
			  (make-compiled-funcall-by-symbol operator (length arg-forms) funobj))
			stack-restore-code))))))
	  
(define-compiler compile-apply-lexical-funobj (&all all &form form &funobj funobj &env env
						    &result-mode result-mode)
  "3.1.2.1.2.3 Function Forms"
  (destructuring-bind (operator &rest arg-forms)
      form
    (let ((binding (movitz-operator-binding operator env)))
      (multiple-value-bind (arguments-code stack-displacement)
	  (make-compiled-argument-forms arg-forms funobj env)
	(multiple-value-bind (stack-restore-code new-returns)
	    (make-compiled-stack-restore stack-displacement result-mode :multiple-values)
	  (compiler-values ()
	    :returns new-returns
	    :functional-p nil
	    :code (append arguments-code
			  (if (eq funobj (function-binding-funobj binding))
			      (make-compiled-funcall-by-esi (length arg-forms)) ; call ourselves
			    `((:call-lexical ,binding ,(length arg-forms))))
			  stack-restore-code)))))))

(defun make-compiled-funcall-by-esi (num-args)
  (case num-args
    (1 `((:call (:esi ,(slot-offset 'movitz-funobj 'code-vector%1op)))))
    (2 `((:call (:esi ,(slot-offset 'movitz-funobj 'code-vector%2op)))))
    (3 `((:call (:esi ,(slot-offset 'movitz-funobj 'code-vector%3op)))))
    (t (append (if (< num-args #x80)
		   `((:movb ,num-args :cl))
		 (make-immediate-move (dpb num-args (byte 24 8) #x80) :ecx))
					; call new ESI's code-vector
	       `((:call (:esi ,(slot-offset 'movitz-funobj 'code-vector))))))))
  
(defun make-compiled-funcall-by-symbol (apply-symbol num-args funobj)
  (declare (ignore funobj))
  (check-type apply-symbol symbol)
  `((:load-constant ,(movitz-read apply-symbol) :edx) ; put function symbol in EDX
    (:movl (:edx ,(slot-offset 'movitz-symbol 'function-value))
	   :esi)			; load new funobj from symbol into ESI
    ,@(make-compiled-funcall-by-esi num-args)))

(defun make-compiled-funcall-by-funobj (apply-funobj num-args funobj)
  (declare (ignore funobj))
  (check-type apply-funobj movitz-funobj)
  (compiler-values ()
    :returns :multiple-values
    :functional-p :nil
    :code `(				; put function funobj in ESI
	    (:load-constant ,apply-funobj :esi)
	    ,@(make-compiled-funcall-by-esi num-args))))

(defun make-compiled-argument-forms (argument-forms funobj env)
  "Return code as primary value, and stack displacement as secondary value.
Return the set of modified lexical bindings third. Fourth, a list of the individual
compile-time types of each argument. Fifth: The combined functional-p."
  ;; (incf (aref *args* (min (length argument-forms) 9)))
  (case (length argument-forms)	;; "optimized" versions for 0, 1, 2, and 3 aruments.
    (0 (values nil 0 nil () t))
    (1 (compiler-values-bind (&code code &type type &functional-p functional-p)
	   (compiler-call #'compile-form
	     :form (first argument-forms)
	     :funobj funobj
	     :env env
	     :result-mode :eax)
	 (values code 0 t (list (type-specifier-primary type)) functional-p)))
    (2 (multiple-value-bind (code functional-p modified first-values second-values)
	   (make-compiled-two-forms-into-registers (first argument-forms) :eax
						   (second argument-forms) :ebx
						   funobj env)
	 (values code 0 modified
		 (list (type-specifier-primary (compiler-values-getf first-values :type))
		       (type-specifier-primary (compiler-values-getf second-values :type)))
		 functional-p)))
    (t (let* ((arguments-self-evaluating-p t)
	      (arguments-are-load-lexicals-p t)
	      (arguments-lexical-variables ())
	      (arguments-modifies nil)
	      (arguments-functional-p t)
	      (arguments-types nil)
	      (producers nil)
	      (stack-pos 0)
	      (arguments-code
	       (loop for form in (nthcdr 2 argument-forms)
		   appending
		     (compiler-values-bind (&code code &producer producer &modifies modifies &type type
					    &functional-p functional-p)
			 (compiler-call #'compile-form
			   :form form
			   :funobj funobj
			   :env env
			   :result-mode :push
			   :with-stack-used (post-incf stack-pos))
		       ;; (incf (stack-used arg-env))
		       (unless functional-p
			 (setf arguments-functional-p nil))
		       (push producer producers)
		       (push (type-specifier-primary type)
			     arguments-types)
		       (setf arguments-modifies
			 (modifies-union arguments-modifies modifies))
		       (case producer
			 (compile-self-evaluating)
			 (compile-lexical-variable
			  (setf arguments-self-evaluating-p nil)
			  (assert (eq :load-lexical (caar code)) ()
			    "comp-lex-var produced for ~S~% ~S" form code)
			  (pushnew (second code) arguments-lexical-variables))
			 (t (setf arguments-self-evaluating-p nil
				  arguments-are-load-lexicals-p nil)))
		       code))))
	 (multiple-value-bind (code01 functionalp01 modifies01 all0 all1)
	     (make-compiled-two-forms-into-registers (first argument-forms) :eax
						     (second argument-forms) :ebx
						     funobj env)
	   (unless functionalp01
	     (setf arguments-functional-p nil))
	   (let ((final0 (compiler-values-getf all0 :final-form))
		 (final1 (compiler-values-getf all1 :final-form))
		 (types (list* (type-specifier-primary (compiler-values-getf all0 :type))
			       (type-specifier-primary (compiler-values-getf all1 :type))
			       (nreverse arguments-types))))
	     (cond
	      ((or arguments-self-evaluating-p
		   (and (typep final0 'lexical-binding)
			(typep final1 'lexical-binding)))
	       (values (append arguments-code code01)
		       ;; restore stack..
		       (+ -2 (length argument-forms))
		       nil
		       types
		       arguments-functional-p))
	      ((and arguments-are-load-lexicals-p
		    (typep final0 '(or lexical-binding movitz-object))
		    (typep final1 '(or lexical-binding movitz-object)))
	       (values (append arguments-code code01)
		       (+ -2 (length argument-forms))
		       nil
		       types
		       arguments-functional-p))
	      ((and (typep final0 '(or lexical-binding movitz-object))
		    (typep final1 '(or lexical-binding movitz-object))
		    (not (modifies-member final0 arguments-modifies))
		    (not (modifies-member final1 arguments-modifies)))
	       (values (append arguments-code code01)
		       (+ -2 (length argument-forms))
		       nil
		       types
		       arguments-functional-p))
	      ((and arguments-are-load-lexicals-p
		    (not (operators-present-in-code-p code01
						      '(:store-lexical)
						      arguments-lexical-variables)))
	       (values (append arguments-code code01)
		       (+ -2 (length argument-forms))
		       nil
		       types
		       arguments-functional-p))
	      (t ;; (warn "fail: ~S by ~S" argument-forms (nreverse producers))
	       (let ((stack-pos 0))
		 (values (append (compiler-call #'compile-form
				   :form (first argument-forms)
				   :funobj funobj
				   :env env
				   :top-level-p nil
				   :result-mode :push
				   :with-stack-used (post-incf stack-pos))
				 ;; (prog1 nil (incf (stack-used arg-env)))
				 (compiler-call #'compile-form
				   :form (second argument-forms)
				   :funobj funobj
				   :env env
				   :top-level-p nil
				   :result-mode :push
				   :with-stack-used (post-incf stack-pos))
				 ;; (prog1 nil (incf (stack-used arg-env)))
				 (loop for form in (nthcdr 2 argument-forms)
				     appending
				       (compiler-call #'compile-form
					 :form form
					 :funobj funobj
					 :env env
					 :result-mode :push
					 :with-stack-used (post-incf stack-pos)))
				 `((:movl (:esp ,(* 4 (- (length argument-forms) 1))) :eax)
				   (:movl (:esp ,(* 4 (- (length argument-forms) 2))) :ebx)))
			 ;; restore-stack.. don't mess up CF!
			 (prog1 (length argument-forms)
			   #+ignore (assert (= (length argument-forms) (stack-used arg-env))))
			 (modifies-union modifies01 arguments-modifies)
			 types
			 arguments-functional-p))))))))))

(defun program-is-load-lexical-of-binding (prg)
  (and (not (cdr prg))
       (instruction-is-load-lexical-of-binding (car prg))))

(defun instruction-is-load-lexical-of-binding (instruction)
  (and (listp instruction)
       (eq :load-lexical (car instruction))
       (destructuring-bind (binding destination &key &allow-other-keys)
	   (operands instruction)
	 (values binding destination))))

(defun make-compiled-two-forms-into-registers (form0 reg0 form1 reg1 funobj env)
  "Returns first: code that does form0 into reg0, form1 into reg1.
second: whether code is functional-p,
third: combined set of modified bindings
fourth: all compiler-values for form0, as a list.
fifth:  all compiler-values for form1, as a list."
  (assert (not (eq reg0 reg1)))
  (compiler-values-bind (&all all0 &code code0 &functional-p functional0
			 &final-form final0 &type type0)
      (compiler-call #'compile-form
	:form form0
	:funobj funobj
	:env env
	:result-mode reg0)
    (compiler-values-bind (&all all1 &code code1 &functional-p functional1
			   &final-form final1 &type type1)
	(compiler-call #'compile-form
	  :form form1
	  :funobj funobj
	  :env env
	  :result-mode reg1)
      (values (cond
	       ((and (typep final0 'binding)
		     (not (code-uses-binding-p code1 final0 :load nil :store t)))
		(append (compiler-call #'compile-form-unprotected
			  :form form0
			  :result-mode :ignore
			  :funobj funobj
			  :env env)
			code1
			`((:load-lexical ,final0 ,reg0 :protect-registers (,reg1)))))
	       ((program-is-load-lexical-of-binding code1)
		(destructuring-bind (src dst &key protect-registers shared-reference-p)
		    (cdar code1)
		  (assert (eq reg1 dst))
		  (append code0
			  `((:load-lexical ,src ,reg1
					   :protect-registers ,(union protect-registers
								      (list reg0))
					   :shared-reference-p ,shared-reference-p)))))
	       ;; XXX if we knew that code1 didn't mess up reg0, we could do more..
	       (t #+ignore (when (and (not (tree-search code1 reg0))
				      (not (tree-search code1 :call)))
			     (warn "got b: ~S ~S for ~S: ~{~&~A~}" form0 form1 reg0 code1))
		  (append (compile-form form0 funobj env nil :push)
			  (compiler-call #'compile-form
			    :form form1
			    :funobj funobj
			    :env env
			    :result-mode reg1
			    :with-stack-used 1)
			  `((:popl ,reg0)))))
	      (and functional0 functional1)
	      t
	      (compiler-values-list (all0))
	      (compiler-values-list (all1))))))

(define-compiler compile-symbol (&all all &form form &env env &result-mode result-mode)
  "3.1.2.1.1 Symbols as Forms"
  (if (movitz-constantp form env)
      (compiler-call #'compile-self-evaluating
	:forward all
	:form (eval-form form env))
    (let ((binding (movitz-binding form env)))
      (cond
       ((typep binding 'lexical-binding)
	#+ignore (make-compiled-lexical-variable form binding result-mode env)
	(compiler-call #'compile-lexical-variable :forward all))
       ((typep binding 'symbol-macro-binding)
	(compiler-call #'compile-form-unprotected
	  :forward all
	  :form (funcall *movitz-macroexpand-hook* (macro-binding-expander (movitz-binding form env)) form env)))
       (t (compiler-call #'compile-dynamic-variable :forward all))))))

#+old-compiler
(defun ensure-local-binding (binding funobj env)
  "Make sure that we have a binding that is local to funobj."
  (if (eq funobj (binding-funobj binding))
      binding
    (let* ((function-env (find-function-env env funobj))
	   (local-binding (make-instance 
			      (ecase (function-env-extent function-env)
				(:indefinite-extent 'indefinite-borrowed-binding)
				;; XXXX
				(:dynamic-extent 'indefinite-borrowed-binding)
				(:lexical-extent 'lexical-borrowed-binding))
			    :name (binding-name binding)
			    :target-binding binding)))
      (movitz-environment-add-binding function-env (binding-name binding) local-binding)
      local-binding)))

(define-compiler compile-lexical-variable (&form variable &result-mode result-mode &env env)
  (let ((binding (movitz-binding variable env)))
    (check-type binding lexical-binding)
    (case (operator result-mode)
      (:ignore
       (compiler-values ()))
      (t (let ((returns (ecase (result-mode-type result-mode)
			  ((:function :multiple-values :eax)
			   :eax)
			  (:lexical-binding
			   :eax)
			  ((:ebx :ecx :edx :esi :push
			    :untagged-fixnum-eax
			    :untagged-fixnum-ecx
			    :boolean-branch-on-true
			    :boolean-branch-on-false)
			   result-mode)
			  (:boolean
			   :boolean=zf=0))))
	   (compiler-values ()
	     :code (make-compiled-lexical-load binding returns)
	     :final-form binding
	     :type `(binding-type ,binding)
	     :returns returns
	     :functional-p t))))))

(defun make-compiled-lexical-load (binding result-mode &rest key-args)
  "Do what is necessary to load lexical binding <binding>."
  `((:load-lexical ,binding ,result-mode ,@key-args)))

(define-compiler compile-dynamic-variable (&form form &env env &result-mode result-mode)
  "3.1.2.1.1.2 Dynamic Variables"
  (if (eq :ignore result-mode)
      (compiler-values ())
    (let ((binding (movitz-binding form env)))
      (cond
       ((not binding)
	(unless (movitz-env-get form 'special nil env)
	  (cerror "Compile like a special." "Undeclared variable: ~S." form))
	(compiler-values ()
	  :returns :eax
	  :functional-p t
	  :modifies nil
	  :final-form form
	  :code `((:load-constant ,form :eax)
		  (:call (:edi ,(global-constant-offset 'dynamic-load))))))
       (t (check-type binding dynamic-binding)
	  (compiler-values ()
	    :returns :eax
	    :functional-p t
	    :modifies nil
	    :final-form form
	    :code `((:load-constant ,form :eax)
		    (:call (:edi ,(global-constant-offset 'dynamic-load))))))))))

(define-compiler compile-lambda-form (&form form)
  "3.1.2.2.4 Lambda Forms"
  (error "Don't know how to compile lambda form ~A" form))

(define-compiler compile-constant-compound (&all all &form form &env env &top-level-p top-level-p)
  (compiler-call #'compile-self-evaluating
    :forward all
    :form (eval-form form env top-level-p)))

(defun register32-to-low8 (register)
  (ecase register
    (:eax :al)
    (:ebx :bl)
    (:ecx :cl)
    (:edx :dl)))

(defun make-immediate-move (value destination-register)
  (cond
   ((zerop value)
    `((:xorl ,destination-register ,destination-register)))
   ((= value (image-nil-word *image*))
    `((:movl :edi ,destination-register)))
   ((<= #x-80 (- value (image-nil-word *image*)) #x7f)
    `((:leal (:edi ,(- value (image-nil-word *image*))) ,destination-register)))
   ((<= #x-80 (- value (* 2 (image-nil-word *image*))) #x7f)
    `((:leal (:edi (:edi 1) ,(- value (* 2 (image-nil-word *image*)))) ,destination-register)))
   ((<= #x-80 (- value (* 3 (image-nil-word *image*))) #x7f)
    `((:leal (:edi (:edi 2) ,(- value (* 3 (image-nil-word *image*)))) ,destination-register)))
   ((<= #x-80 (- value (* 5 (image-nil-word *image*))) #x7f)
    `((:leal (:edi (:edi 4) ,(- value (* 5 (image-nil-word *image*)))) ,destination-register)))
   ((<= #x-80 (- value (* 9 (image-nil-word *image*))) #x7f)
    `((:leal (:edi (:edi 8) ,(- value (* 9 (image-nil-word *image*)))) ,destination-register)))
   ((<= 0 value #xff)
    `((:xorl ,destination-register ,destination-register)
      (:movb ,value ,(register32-to-low8 destination-register))))
   (t `((:movl ,value ,destination-register)))))

(define-compiler compile-self-evaluating (&form form &result-mode result-mode &funobj funobj)
  "3.1.2.1.3 Self-Evaluating Objects"
  (let* ((object (or (quote-form-p form) form))
	 (movitz-obj (image-read-intern-constant *image* object))
	 (funobj-env (funobj-env funobj))
	 (binding (or (cdr (assoc movitz-obj (movitz-environment-bindings funobj-env)))
		      (let ((binding (make-instance 'constant-object-binding
				       :name movitz-obj
				       :object movitz-obj)))
			(setf (binding-env binding) funobj-env)
			(push (cons movitz-obj binding)
			      (movitz-environment-bindings funobj-env))
			binding))))
    (compiler-values-bind (&all self-eval)
	(compiler-values (nil :abstract t)
	  :producer (default-compiler-values-producer)
	  :type  `(eql ,movitz-obj)
	  :final-form binding
	  :functional-p t)	
      (if (eq :ignore (operator result-mode))
	  (compiler-values (self-eval)
	    :returns :nothing
	    :type nil)
	(compiler-values (self-eval)
	  :code `((:load-lexical ,binding ,result-mode))
	  :returns result-mode)))))

(define-compiler compile-implicit-progn (&all all &form forms &top-level-p top-level-p
					      &result-mode result-mode)
  "Compile all the elements of the list <forms> as a progn."
  (check-type forms list)
  (case (length forms)
    (0 (compiler-values ()))
    (1 (compiler-call #'compile-form-unprotected
	 :forward all
	 :form (first forms)))
    (t (loop with no-side-effects-p = t
	   with progn-codes = nil
	   for (sub-form . more-forms-p) on forms
	   as current-result-mode = (if more-forms-p :ignore result-mode)
	   do (compiler-values-bind (&code code &returns sub-returns-mode
				     &functional-p no-sub-side-effects-p
				     &type type &final-form final-form &producer sub-producer)
		  (compiler-call (if (not more-forms-p)
				     #'compile-form-unprotected
				   #'compile-form)
		    :defaults all
		    :form sub-form
		    :top-level-p top-level-p
		    :result-mode current-result-mode)
		(assert sub-returns-mode ()
		  "~S produced no returns-mode for form ~S." sub-producer sub-form)
		(unless no-sub-side-effects-p
		  (setf no-side-effects-p nil))
		(push (if (and no-sub-side-effects-p (eq current-result-mode :ignore))
			  nil
			code)
		      progn-codes)
		(when (not more-forms-p)
		  (return (compiler-values ()
			    :returns sub-returns-mode
			    :functional-p no-side-effects-p
			    :final-form final-form
			    :type type
			    :code (reduce #'append (nreverse progn-codes))))))))))


(defun new-make-compiled-constant-reference (obj funobj)
  (let ((movitz-obj (movitz-read obj)))
    (if (eq movitz-obj (image-t-symbol *image*))
	(make-indirect-reference :edi (global-constant-offset 't-symbol))
      (etypecase movitz-obj
	(movitz-nil :edi)
	(movitz-immediate-object (movitz-immediate-value movitz-obj))
	(movitz-heap-object 
	 (make-indirect-reference :esi (movitz-funobj-intern-constant funobj movitz-obj)))))))

(defun make-compiled-lexical-control-transfer (return-code return-mode from-env to-env
					       &optional (to-label (exit-label to-env)))
  "<return-code> running in <from-env> produces <return-mode>, and we need to
generate code that transfers control (and unwinds dynamic bindings, runs unwind-protect
cleanup-forms etc.) to <to-env> with <return-code>'s result intact."
  (check-type to-env lexical-exit-point-env)
  (multiple-value-bind (stack-distance num-dynamic-slots unwind-protects)
      (stack-delta from-env to-env)
    (assert stack-distance)
    (assert (null unwind-protects) ()
      "Lexical unwind-protect not implemented.")
    (cond
     ((and (eq t stack-distance)
	   (zerop num-dynamic-slots))
      (compiler-values ()
	:returns :non-local-exit
	:code (append return-code
		      (unless (eq :function (exit-result-mode to-env))
			`((:load-lexical ,(save-esp-variable to-env) :esp)))
		      `((:jmp ',to-label)))))
     ((eq t stack-distance)
      (compiler-values ()
	:returns :non-local-exit
	:code (append return-code
		      (compiler-call #'special-operator-with-cloak
			:env to-env
			:result-mode (exit-result-mode to-env)
			:form `(muerte::with-cloak (,return-mode)
				 (muerte::dynamic-unwind ,num-dynamic-slots)))
		      `((:load-lexical ,(save-esp-variable to-env) :esp)
			(:jmp ',to-label)))))
     ((zerop num-dynamic-slots)
      (compiler-values ()
	:returns :non-local-exit
	:code (append return-code
		      (make-compiled-stack-restore stack-distance
						   (exit-result-mode to-env)
						   return-mode)
		      `((:jmp ',to-label)))))
     ((plusp num-dynamic-slots)
      ;; (warn "num-dynamic-slots: ~S" num-dynamic-slots)
      (compiler-values ()
	:returns :non-local-exit
	:code (append return-code
		      (compiler-call #'special-operator-with-cloak
			:env to-env
			:result-mode (exit-result-mode to-env)
			:form `(muerte::with-cloak (,return-mode)
				 (muerte::dynamic-unwind ,num-dynamic-slots)))
		      (make-compiled-stack-restore stack-distance
						   (exit-result-mode to-env)
						   return-mode)
		      `((:jmp ',to-label)))))
     (t (error "unknown!")))))

(defun stack-delta (inner-env outer-env)
  "Calculate the amount of stack-space used (in 32-bit stack slots) at the time
of <inner-env> since <outer-env>,
the number of intervening dynamic-slots (special bindings, unwind-protects, and catch-tags),
and a list of any intervening unwind-protect environment-slots."
  (labels 
      ((stack-distance-add (x y)
	 (if (and (integerp x) (integerp y))
	     (+ x y)
	   t))
       (find-stack-delta (env stack-distance num-dynamic-slots unwind-protects)
	 (cond
	  ((eq outer-env env)
	   ;; Each dynamic-slot is 4 stack-distances, so let's check that..
	   (unless (>= stack-distance (* 4 num-dynamic-slots))
	     (print-stack-delta inner-env outer-env))
	   (assert (>= stack-distance (* 4 num-dynamic-slots)) ()
	     "The stack-distance ~D is smaller than number of dynamic-slots ~D, which is inconsistent."
	     stack-distance num-dynamic-slots)
	   (values stack-distance num-dynamic-slots unwind-protects))
	  ((null env)
	   (values nil 0 nil))
	  (t (find-stack-delta (movitz-environment-uplink env)
			       (stack-distance-add stack-distance (stack-used env))
			       (+ num-dynamic-slots (num-dynamic-slots env))
			       (if (typep env 'unwind-protect-env)
				   (cons env unwind-protects)
				 unwind-protects))))))
    (find-stack-delta inner-env 0 0 nil)))

(defun print-stack-delta (inner-env outer-env)
  (labels ((print-stack-delta (env)
	     (cond
	      ((or (eq outer-env env)
		   (null env)))
	      (t (format t "~&Env: ~S used: ~S, slots: ~S"
			 env (stack-used env) (num-dynamic-slots env))
		 (print-stack-delta (movitz-environment-uplink env))))))
    (print-stack-delta inner-env)))

;;;;;;;
;;;;;;; Extended-code declarations
;;;;;;;

(defvar *extended-code-find-read-binding*
    (make-hash-table :test #'eq))

(defmacro define-find-read-bindings (name lambda-list &body body)
  (let ((defun-name (intern
		     (with-standard-io-syntax
		       (format nil "~A-~A" 'find-read-bindings name)))))
    `(progn
       (setf (gethash ',name *extended-code-find-read-binding*) ',defun-name)
       (defun ,defun-name (instruction)
	 (destructuring-bind ,lambda-list
	     (cdr instruction)
	   ,@body)))))

(defun find-read-bindings (extended-instruction)
  "Return zero, one or two bindings that this instruction reads."
  (when (listp extended-instruction)
    (let* ((operator (car extended-instruction))
	   (finder (gethash operator *extended-code-find-read-binding*)))
      (when finder
	(funcall finder extended-instruction)))))

(defvar *extended-code-find-write-binding-and-type*
    (make-hash-table :test #'eq))

(defmacro define-find-write-binding-and-type (name lambda-list &body body)
  (let ((defun-name (intern
		     (with-standard-io-syntax
		       (format nil "~A-~A" 'find-write-binding-and-type name)))))
    `(progn
       (setf (gethash ',name *extended-code-find-write-binding-and-type*) ',defun-name)
       (defun ,defun-name ,lambda-list ,@body))))

(defun find-written-binding-and-type (extended-instruction)
  (when (listp extended-instruction)
    (let* ((operator (car extended-instruction))
	   (finder (gethash operator *extended-code-find-write-binding-and-type*)))
      (when finder
	(funcall finder extended-instruction)))))

(defvar *extended-code-expanders*
    (make-hash-table :test #'eq))

(defmacro define-extended-code-expander (name lambda-list &body body)
  (let ((defun-name (intern
		     (with-standard-io-syntax
		       (format nil "~A-~A" 'extended-code-expander- name)))))
    `(progn
       (setf (gethash ',name *extended-code-expanders*) ',defun-name)
       (defun ,defun-name ,lambda-list ,@body))))

(defun expand-extended-code (extended-instruction funobj frame-map)
  (if (not (listp extended-instruction))
      (list extended-instruction)
    (let* ((operator (car extended-instruction))
	   (expander (gethash operator *extended-code-expanders*)))
      (if expander
	  (funcall expander extended-instruction funobj frame-map)
	(list extended-instruction)))))

(defun ensure-local-binding (binding funobj)
  "When referencing binding in funobj, ensure we have the binding local to funobj."
  (cond
   ((not (typep binding 'binding))
    binding)
   ((eq funobj (binding-funobj binding))
    binding)
   (t (or (find binding (borrowed-bindings funobj)
		:key (lambda (binding)
		       (borrowed-binding-target binding)))
	  (error "Can't install non-local binding ~W." binding)))))

;;;;;;;
;;;;;;; Extended-code handlers
;;;;;;;


;;;;;;;;;;;;;;;;;; Load-lexical

(define-find-write-binding-and-type :load-lexical (instruction)
  (destructuring-bind (source destination &key &allow-other-keys)
      (cdr instruction)
    (when (typep destination 'binding)
      (values destination source))))

(define-find-read-bindings :load-lexical (source destination &key &allow-other-keys)
  (declare (ignore destination))
  (check-type source binding)
  source)

(define-extended-code-expander :load-lexical (instruction funobj frame-map)
  (destructuring-bind (source destination &key shared-reference-p tmp-register protect-registers)
      (cdr instruction)
    (make-load-lexical (ensure-local-binding source funobj)
		       (ensure-local-binding destination funobj)
		       funobj shared-reference-p frame-map
		       :tmp-register tmp-register
		       :protect-registers protect-registers)))


;;;;;;;;;;;;;;;;;; Lisp-move

(define-find-write-binding-and-type :lmove (instruction)
  (destructuring-bind (source destination)
      (cdr instruction)
    (values destination source)))

(define-find-read-bindings :lmove (source destination)
  (declare (ignore destination))
  (values source))

;;;;;;;;;;;;;;;;;; Store-lexical

(define-find-write-binding-and-type :store-lexical (instruction)
  (destructuring-bind (destination source &key (type (error "No type")) &allow-other-keys)
      (cdr instruction)
    (declare (ignore source))
    (check-type destination binding)
    (values destination type)))

(define-find-read-bindings :store-lexical (destination source &key &allow-other-keys)
  (declare (ignore destination))
  (when (typep source 'binding)
    source))

(define-extended-code-expander :store-lexical (instruction funobj frame-map)
  (destructuring-bind (destination source &key shared-reference-p type)
      (cdr instruction)
    (declare (ignore type))
    (make-store-lexical (ensure-local-binding destination funobj)
			(ensure-local-binding source funobj)
			shared-reference-p frame-map)))

;;;;;;;;;;;;;;;;;; Init-lexvar

(define-find-write-binding-and-type :init-lexvar (instruction)
  (destructuring-bind (binding &key init-with-register init-with-type
				    protect-registers protect-carry)
      (cdr instruction)
    (declare (ignore protect-registers protect-carry))
    (when init-with-register
      (assert init-with-type)
      (values binding init-with-type))))

(define-extended-code-expander :init-lexvar (instruction funobj frame-map)
  (destructuring-bind (binding &key protect-registers protect-carry
				    init-with-register init-with-type)
      (cdr instruction)
    (declare (ignore protect-carry))	; nothing modifies carry anyway.
    (assert (eq binding (ensure-local-binding binding funobj)))
    (cond
     ((binding-lended-p binding)
      (let ((cons-position (getf (binding-lended-p binding)
				 :stack-cons-location))
	    (tmp-register (find-if (lambda (r)
				     (and (not (member r protect-registers))
					  (not (eq r init-with-register))))
				   '(:edx :ecx  :ebx :eax)))
	    (init-register (or init-with-register :edi)))
	(when init-with-register
	  (assert (not (null init-with-type))))
	(assert tmp-register ()		; solve this with push eax .. pop eax if ever needed.
	  "Unable to find a tmp-register for ~S." instruction)
	`((:leal (:ebp ,(1+ (stack-frame-offset (1+ cons-position))))
		 ,tmp-register)
	  (:movl :edi (,tmp-register 3)) ; cdr
	  (:movl ,init-register (,tmp-register -1)) ; car
	  (:movl ,tmp-register
		 (:ebp ,(stack-frame-offset
			 (new-binding-location binding frame-map)))))))
     (init-with-register
      (make-store-lexical binding init-with-register nil frame-map)))))

;;;;;;;;;;;;;;;;;; car

(define-extended-code-expander :car (instruction funobj frame-map)
  (declare (ignore funobj frame-map))
  (destructuring-bind (x dst)
      (cdr instruction)
    (etypecase x
      (binding
       `((:load-lexical ,x :eax)
	 (:call (:edi ,(global-constant-offset 'fast-car)))
	 ,@(when (not (eq dst :eax))
	     `((:movl :eax ,dst)))))
      (symbol
       (append (case x
		 (:eax
		  `((:call (:edi ,(global-constant-offset 'fast-car)))))
		 (:ebx
		  `((:call (:edi ,(global-constant-offset 'fast-car-ebx)))))
		 (t `((:movl ,x :eax)
		      (:call (:edi ,(global-constant-offset 'fast-car))))))
	       (when (not (eq dst :eax))
		 `((:movl :eax ,dst))))))))
