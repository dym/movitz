;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      more-macros.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Jun  7 15:05:57 2002
;;;;                
;;;; $Id: more-macros.lisp,v 1.2 2004/01/19 11:23:47 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/setf)
(provide :muerte/more-macros)

(in-package muerte)

(defmacro pop (&environment env place)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't pop a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars)))
      `(let ,(mapcar #'list tmp-vars tmp-var-init-forms)
	 (let ((,store-var ,getter-form))
	   (prog1
	       (car ,store-var)
	     (setq ,store-var (cdr ,store-var))
	     ,setter-form))))))

(define-compiler-macro pop (&whole form &environment env place)
  (if (and (symbolp place)
	   (typep (movitz::movitz-binding place env) 'movitz::lexical-binding))
      `(with-inline-assembly (:returns :ebx)
	 (:compile-form (:result-mode :eax) ,place)
	 (:globally (:call (:edi (:edi-offset fast-cdr-car))))
	 (:lexical-store ,place :eax))
      #+ignore
      `(prog1 (car ,place)
	 (setq ,place (cdr ,place)))
    form))

(defmacro push (&environment env item place)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't push a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (item-var (gensym "push-item-")))
      `(let ((,item-var ,item)
	     ,@(mapcar #'list tmp-vars tmp-var-init-forms))
	 (let ((,store-var (cons ,item-var ,getter-form)))
	   ,setter-form)))))

#+ignore
(define-compiler-macro push (&whole form &environment env item place)
  (if (and (symbolp place)
	   (not (typep (movitz::movitz-binding place env) 'movitz::symbol-macro-binding)))
      `(setq ,place (cons ,item ,place))
    form))
  
(defmacro pushnew (&environment env item place &key (key ''identity) (test ''eq) test-not)
  (when test-not
    (error "Test-not not supported."))
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't pushnew a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (item-var (gensym "push-item-")))
      `(let ((,item-var ,item)
	     ,@(mapcar #'list tmp-vars tmp-var-init-forms))
	 (let ((old-value ,getter-form))
	   (if (not (member ,item-var old-value :key ,key :test ,test))
	       (let ((,store-var (cons ,item-var old-value)))
		 ,setter-form)
	     old-value))))))
  
(defmacro remf (&environment env place indicator)
  (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
      (get-setf-expansion place env)
    (assert (= 1 (length store-vars)) ()
      "Can't remf a place with ~D cells." (length store-vars))
    (let ((store-var (first store-vars))
	  (indicator-var (gensym "remf-indicator-")))
      `(let (,@(mapcar #'list tmp-vars tmp-var-init-forms)
	     (,indicator-var ,indicator))
	 (let ((p ,getter-form))
	   (cond
	    ((null p) nil)
	    ((eq ,indicator-var (car p))
	     (let ((,store-var (cddr p)))
	       ,setter-form)
	     t)
	    (t (do ((x (cdr p) (cddr x))
		    (y (cddr p) (cddr y)))
		   ((null y) nil)
		 (when (eq ,indicator-var (car y))
		   (setf (cdr x) (cddr y))
		   (return t))))))))))

(define-compiler-macro dotimes (&whole form-decline (var count-form &optional result-form)
				&body declarations-and-body)
  (if (not (movitz:movitz-constantp count-form))
      form-decline
    (let ((count (movitz::eval-form count-form)))
      (check-type count (integer 0 *))
      (cond
       ((= 0 count)
	nil)
       ((= 1 count)
	`(let ((,var 0))
	   ,@declarations-and-body
	   ,result-form))
       (t `(do ((,var 0 (1+ ,var)))
	       ((>= ,var ,count-form) ,result-form)
	     (declare (type (integer 0 ,count-form) ,var))
	     ,@declarations-and-body))))))

(defmacro dotimes ((var count-form &optional result-form) &body declarations-and-body)
  (let ((count-var (gensym)))
    `(do ((,count-var ,count-form)
	  (,var 0 (1+ ,var)))
	 ((<= ,count-var ,var) ,result-form)
       ,@declarations-and-body)))

(defmacro dolist ((var list-form &optional result-form) &body declarations-and-body)
  (let ((cons-var (gensym "dolist-cons-var-"))
	(loop-tag (gensym "dolist-loop-tag-")))
    (multiple-value-bind (body declarations)
	(movitz::parse-declarations-and-body declarations-and-body 'muerte.cl:declare)
      `(let ((,cons-var ,list-form) ,var)
	 (declare ,@declarations)
	 (block nil
	   (tagbody
	     ,loop-tag
	     (when ,cons-var
	       (setq ,var (pop ,cons-var))
	       ,@body
	       (go ,loop-tag)))
	   ,result-form))
      #+ignore
      `(do* ((,cons-var ,list-form (cdr ,cons-var))
	     (,var (car ,cons-var) (car ,cons-var)))
	   ((null ,cons-var) ,result-form)
	 ,@declarations-and-body))))


(defmacro letf* (bindings &body body &environment env)
  "Does what one might expect, saving the old values and setting the generalized
  variables to the new values in sequence.  Unwind-protects and get-setf-method
  are used to preserve the semantics one might expect in analogy to let*,
  and the once-only evaluation of subforms."
  (labels ((do-bindings
            (bindings)
            (cond ((null bindings) body)
                  (t (multiple-value-bind (dummies vals newval setter getter)
			 (get-setf-expansion (caar bindings) env)
                       (let ((save (gensym)))
                         `((let* (,@(mapcar #'list dummies vals)
                                  (,(car newval) ,(cadar bindings))
                                  (,save ,getter))
                             (unwind-protect
                               (progn ,setter
                                      ,@(do-bindings (cdr bindings)))
                               (setq ,(car newval) ,save)
                               ,setter)))))))))
    (car (do-bindings bindings))))

(defmacro with-letf (clauses &body body)
  "Each clause is (<place> &optional <value-form> <prev-var>).
Execute <body> with alternative values for each <place>.
Note that this scheme does not work well with respect to multiple threads.
XXX This should actually be using get-setf-expansion etc. to deal with
proper evaluation of the places' subforms."
  (let ((place-value-save (loop for (place . value-save) in clauses
			      if value-save
			      collect (list place `(progn ,(first value-save))
					    (or (second value-save) (gensym)))
			      else collect (list place nil (gensym)))))
    `(let (,@(loop for (place nil save-var) in place-value-save
		 collect `(,save-var ,place)))
       (unwind-protect
	   (progn (setf ,@(loop for (place value) in place-value-save
			      append `(,place ,value)))
		  ,@body)
	 (setf ,@(loop for (place nil save) in place-value-save
		     append `(,place ,save)))))))

(defmacro with-alternative-fdefinitions (clauses &body body)
  "Each clause is (<name> <definition>). Execute <body> with alternative
fdefinitions for each <name>. Note that this scheme does not work well with
respect to multiple threads."
  (let ((tmp-name-def (loop for (name def) in clauses
			  collect (list (gensym) name def))))
    `(let (,@(loop for (tmp name) in tmp-name-def collect `(,tmp (fdefinition ',name))))
       (macrolet ((previous-fdefinition (&whole form name)
		    (case name
		      ,@(loop for (tmp name) in tmp-name-def
			    collect `(,name ',tmp))
		      (t form))))
	 (unwind-protect
	     (progn (setf ,@(loop for (nil name def) in tmp-name-def
				append `((fdefinition ',name) ,def)))
		    ,@body)
	   (setf ,@(loop for (tmp name) in tmp-name-def
		       append `((fdefinition ',name) ,tmp))))))))

(defmacro eof-or-lose (stream eof-errorp eof-value)
  `(if ,eof-errorp
       (error 'end-of-file :stream ,stream)
       ,eof-value))




  
  
