;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      setf.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Feb  8 20:43:20 2001
;;;;                
;;;; $Id: setf.lisp,v 1.2 2004/01/19 11:23:47 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/setf)

(in-package muerte)

(defmacro define-setf-expander (access-fn lambda-list &body docstring-declarations-body)
  `(progn
     (define-setf-expander-compile-time ,access-fn ,lambda-list
       ,docstring-declarations-body)
     ',access-fn))
  

(eval-when (:compile-toplevel)
  (defun get-setf-expansion (place &optional environment)
    (let* ((name (and (consp place)
		      (movitz::translate-program (car place) :cl :muerte.cl)))
	   (expander (and name (movitz::movitz-env-get name :setf-expander nil environment))))
      (if expander
	  (funcall expander place environment)
	(multiple-value-bind (expansion expanded-p)
	    (movitz::movitz-macroexpand-1 place environment)
	  (cond
	   (expanded-p
	    (when (eq expansion place)
	      (warn "exp place are eq! ~S" place))
	    (get-setf-expansion expansion environment))
	   ((symbolp place)
	    (let ((store-var (gensym "store-var-")))
	      (values nil nil (list store-var) `(setq ,place ,store-var) place)))
	   ((assert (consp place)))
	   (t (multiple-value-bind (tmp-vars tmp-var-init-forms arglist)
		  (loop for sub-form in (cdr place)
		      as tmp-var = (gensym "tmp-var-")
		      if (movitz:movitz-constantp sub-form environment)
		      collect sub-form into arglist
		      else collect tmp-var into tmp-vars
		      and collect sub-form into tmp-var-init-forms
		      and collect tmp-var into arglist
		      finally (return (values tmp-vars tmp-var-init-forms arglist)))
		(let ((store-var (gensym "store-var-")))
		  (values tmp-vars
			  tmp-var-init-forms
			  (list store-var)
			  `(funcall #'(setf ,(car place)) ,store-var ,@arglist)
			  (list* (car place) arglist)))))))))))


;;;(defsetf subseq (sequence start &optional end) (new-sequence)
;;;  `(progn (replace ,sequence ,new-sequence
;;;		   :start1 ,start :end1 ,end)
;;;	  ,new-sequence))
;;;
;;; ==>>>
;;;
;;;(define-setf-expander subseq (sequence start &optional end)
;;;  (let ((tmp-sequence (gensym "tmp-sequence"))
;;;	(tmp-start (gensym "tmp-start"))
;;;	(tmp-end (gensym "tmp-end"))
;;;	(store-var (gensym "store-var"))
;;;	(init-forms (list sequence start end)))
;;;    (let ((sequence tmp-sequence)
;;;	  (start tmp-start)
;;;	  (end tmp-end))
;;;      (values (list tmp-sequence tmp-start tmp-end)
;;;	      init-forms
;;;	      (list store-var)
;;;	      `(progn
;;;		 (replace ,sequence ,store-var :start1 ,start :end1 ,end)
;;;		 ,store-var)
;;;	      `(subseq ,tmp-sequence ,tmp-start ,tmp-end)))))

(defmacro defsetf (access-fn &rest more-args)
  ;; long form
  (destructuring-bind (lambda-list store-variables &body body)
      more-args
    (let ((movitz-lambda (movitz::translate-program lambda-list :cl :muerte.cl)))
      (multiple-value-bind (wholevars envvars reqvars optionalvars restvar keys auxes)
	  (movitz::decode-macro-lambda-list movitz-lambda)
	(assert (null restvar))
	(assert (null envvars))
	(assert (null wholevars))
	(assert (null auxes))
	(assert (null keys))
	(let* ((req-tmps (mapcar (lambda (x) (list x (gensym)))
				 reqvars))
	       (opt-vars (mapcar #'movitz::decode-optional-formal
				 optionalvars))
	       (opt-tmps (mapcar (lambda (x) (list x (gensym)))
				 opt-vars))
	       (tmp-lets (append (mapcar (lambda (rt)
					   (list (second rt) '(gensym)))
					 req-tmps)
				 (mapcar (lambda (rt)
					   (list (second rt) '(gensym)))
					 opt-tmps)
				 `((init-form (list ,@reqvars ,@opt-vars)))
				 (mapcar (lambda (rt)
					   (list rt '(gensym)))
					 store-variables)))
	       (lambda-lets (append req-tmps opt-tmps)))
	  `(define-setf-expander ,access-fn ,movitz-lambda
	     (let ,tmp-lets
	       (let ,lambda-lets
		 (values (list ,@(mapcar #'second req-tmps)
			       ,@(mapcar #'second opt-tmps))
			 init-form
			 (list ,@store-variables)
			 (progn ,@body)
			 (list ',access-fn
			       ,@(mapcar #'first req-tmps)
			       ,@(mapcar #'first opt-tmps)))))))))))


(defmacro define-modify-macro (name lambda-list function &optional documentation)
  (check-type function symbol "A function name")
  (let ((movitz-lambda (movitz::translate-program lambda-list :cl :muerte.cl)))
    (multiple-value-bind (wholevars envvars reqvars optionalvars restvar)
	(movitz::decode-macro-lambda-list movitz-lambda)
      (declare (ignore wholevars envvars))
      `(defmacro ,name (&environment env place ,@movitz-lambda)
	 ,documentation
	 (multiple-value-bind (tmp-vars tmp-var-init-forms store-vars setter-form getter-form)
	     (get-setf-expansion place env)
	   (assert (= 1 (length store-vars)) ()
	     "Don't know how to modify a place with ~D cells."
	     (length store-vars))
	   `(let ,(mapcar #'list tmp-vars tmp-var-init-forms)
	      ;; We love backquote..
	      (let ((,(first store-vars) (,',function
					  ,getter-form
					  ,,@reqvars
					  ,,@(mapcar 'movitz::decode-optional-formal optionalvars)
					  ,@,restvar
					  )))
		,setter-form)))))))


(define-compiler-macro setf (&environment env &rest pairs)
  (let ((num-pairs (length pairs)))
    (cond
     ((= 2 num-pairs)
      (destructuring-bind (place new-value-form)
	  pairs
	;; 5.1.2 Kinds of Places
	(cond
	 #+ignore
	 ((nth-value 1 (movitz::movitz-macroexpand-1 place env))
	  ;; 5.1.2.7 Macro forms as places
	  ;; ..and 5.1.2.8 Symbol Macros as places.
	  `(setf ,(movitz::movitz-macroexpand-1 place env) ,new-value-form))
	 ((symbolp place)		; 5.1.2.1 Variable Names as Places
	  (multiple-value-bind (expansion expanded-p)
	      (movitz::movitz-macroexpand-1 place env)
	    (if expanded-p
		`(setf ,expansion ,new-value-form)
	      `(setq ,place ,new-value-form))))
	 (t (multiple-value-bind (tmp-vars tmp-forms store-vars setter-form)
		(get-setf-expansion place env)
	      #+ignore
	      (warn "tmp-vars: ~W, tmp-forms: ~W, store-vars: ~W, setter-form: ~W"
		    tmp-vars tmp-forms store-vars setter-form)
	      (case (length store-vars)
		(0 `(progn ,@tmp-forms ,new-value-form nil))
		(1 `(let (,@(loop for tmp-var in tmp-vars 
				for tmp-form in tmp-forms
				collect `(,tmp-var ,tmp-form))
			  (,(first store-vars) ,new-value-form))
		      (declare (ignorable ,@tmp-vars))
		      ,setter-form))
		(t `(let ,(loop for tmp-var in tmp-vars 
			      for tmp-form in tmp-forms
			      collect `(,tmp-var ,tmp-form))
		      (multiple-value-bind ,store-vars
			  ,new-value-form
			,setter-form))))))
	 #+ignore
	 ((listp place)			; 5.1.2.9 Other Compound Forms as Places
	  (let ((place-operator (first place))
		(place-args (rest place)))
	    (multiple-value-bind (newvalue-form newvalue-lets)
		(if (movitz:movitz-constantp new-value-form)
		    (values new-value-form nil)
		  (let ((newvalue-var (gensym "setf-newvalue")))
		    (values newvalue-var
			    (list (list newvalue-var new-value-form)))))
	      (multiple-value-bind (place-forms place-lets)
		  (loop for pa in place-args
		      as var = (gensym "setf-var")
		      if (movitz:movitz-constantp pa)
		      collect pa into forms
		      else
		      collect var into forms
		      and collect (list var pa) into lets
		      finally (return (values forms lets)))
		`(let (,@place-lets ,@newvalue-lets)
		   (,(movitz::movitz-env-setf-operator-name (movitz::translate-program place-operator
										:cl :muerte.cl))
		    ,newvalue-form
		    ,@place-forms)))))))))
     ((evenp num-pairs)
      (cons 'progn
	    (loop for (place newvalue) on pairs by #'cddr
		collect `(setf ,place ,newvalue))))
     (t (error "Odd number of arguments to SETF.")))))

