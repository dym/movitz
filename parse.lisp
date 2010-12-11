;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      parse.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov 24 16:49:17 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: parse.lisp,v 1.11 2009-12-03 21:48:34 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(in-package movitz)

(defun declare-form-p (form &optional (declare-symbol 'muerte.cl::declare))
  (and (consp form)
       (eq declare-symbol (car form))))

(defun parse-declarations-and-body (forms &optional (declare-symbol 'muerte.cl::declare))
  "From the list of FORMS, return first the list of non-declaration forms, ~
   second the list of declaration-specifiers."
  (loop if (declare-form-p (car forms) declare-symbol)
     append (cdr (pop forms)) into declarations
     else return (values forms declarations)))

(defun parse-docstring-declarations-and-body (forms &optional (declare-symbol 'muerte.cl::declare))
  "From the list of FORMS, return first the non-declarations forms, second the declarations, ~
   and third the documentation string."
  (loop with docstring = nil
     if (declare-form-p (car forms) declare-symbol)
     append (cdr (pop forms)) into declarations
     else if (and (stringp (car forms))
		  (cdr forms))
     do (setf docstring (pop forms))
     else return (values forms declarations docstring)))

(defun parse-macro-lambda-list (lambda-list)
  (let* ((whole-var (when (eq '&whole (car lambda-list))
                      (pop lambda-list)
                      (pop lambda-list)))
         (env-var nil)
         (operator-var (gensym "operator-"))
         (destructuring-lambda-list
          (do ((l lambda-list)
               (r nil))
              ((atom l)
               (cons operator-var
                     (nreconc r l)))
            (let ((x (pop l)))
              (if (eq x '&environment)
                  (setf env-var (pop l))
                  (push x r)))))
         (ignore-env-var
          (when (not env-var)
            (gensym "ignore-env-"))))
    (values destructuring-lambda-list
            whole-var
            (or env-var
                ignore-env-var)
            (when ignore-env-var
              (list ignore-env-var))
            (list operator-var))))

(defun unfold-circular-list (list)
  "If LIST is circular (through cdr), return (a copy of) the non-circular portion of LIST, and the index (in LIST) of the cons-cell pointed to by (cdr (last LIST))."
  (flet ((find-cdr (l c end)
	   (loop for x on l as i upfrom 0 to end
	       thereis (and (eq c x) i))))
    (loop for x on list as i upfrom 0
	as cdr-index = (find-cdr list (cdr x) i)
	until cdr-index
	finally (return (values (loop repeat (1+ i) collect (pop list))
				cdr-index)))))

(defun symbol-package-fix-cl (symbol)
  *package*)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (defun muerte::translate-program 
      (program from-package to-package &key remove-double-quotes-p
					    (quote-symbol 'muerte.cl::quote)
					    when)
    "In PROGRAM, exchange symbols in FROM-PACKAGE with external symbols
in TO-PACKAGE, whenever such symbols exists in TO-PACAKGE.
Doubly quoted forms are copied verbatim (sans the quotes)."
    (setf from-package (find-package from-package))
    (setf to-package (find-package to-package))
    (flet ((translate-symbol (s)
	     (if (not (eq s (find-symbol (symbol-name s) from-package)))
                 s
	       (multiple-value-bind (symbol status)
		   (find-symbol (symbol-name s) to-package)
		 (when (or (and (find-symbol (symbol-name s) to-package)
				(not (find-symbol (symbol-name s) from-package)))
			   (and (find-symbol (symbol-name s) from-package)
				(not (find-symbol (symbol-name s) to-package))))
		   (error "blurgh ~S" s))
		 (or symbol s) #+ignore (if (eq :external status) symbol s)))))
      (cond
       ((symbolp program)		; single symbol?
	(translate-symbol program))
       ((simple-vector-p program)
	(map 'vector
	  (lambda (x) (translate-program x from-package to-package
					 :quote-symbol quote-symbol
					 :when when))
	  program))
       ((atom program)			; atom?
	program)
       ((ignore-errors (null (list-length program))) ; circular list?
	(multiple-value-bind (unfolded-program cdr-index)
	    (unfold-circular-list program)
	  (let ((translated-program (muerte::translate-program unfolded-program from-package to-package
								      :when when
								      :remove-double-quotes-p remove-double-quotes-p
								      :quote-symbol quote-symbol)))
	    (setf (cdr (last translated-program))
	      (nthcdr cdr-index translated-program))
	    translated-program)))
       ((and (eq :translate-when (first program))
	     (or (string= t (second program))
		 (and when (eq when (second program)))))
	(muerte::translate-program (third program) (fourth program) (fifth program) :when when))
       ((and (eq :translate-when (first program))
	     (eq nil (second program)))
	(third program))
       ((symbolp (car program))
	(cons (translate-symbol (car program))
	      (muerte::translate-program (cdr program) from-package to-package
					 :when when
					 :remove-double-quotes-p remove-double-quotes-p
					 :quote-symbol quote-symbol)))
       ((consp (car program))
	(cons (muerte::translate-program (car program) from-package to-package
					 :when when
					 :remove-double-quotes-p remove-double-quotes-p
					 :quote-symbol quote-symbol)
	      (muerte::translate-program (cdr program) from-package to-package
					 :when when
					 :remove-double-quotes-p remove-double-quotes-p
					 :quote-symbol quote-symbol)))
       (t (cons (car program)
		(muerte::translate-program (cdr program) from-package to-package
					   :when when
					   :remove-double-quotes-p remove-double-quotes-p
					   :quote-symbol quote-symbol))))))
  (defun muerte::movitz-program (program)
    (translate-program program :common-lisp :muerte.cl))
  (defun muerte::host-program (program)
    (translate-program program :muerte.cl :common-lisp)))


(defun decode-normal-lambda-list (lambda-list &optional host-symbols-p)
  "3.4.1 Ordinary Lambda Lists.
Returns the requireds, &optionals, &rests, &keys, and &aux formal variables,
a boolean signalling whether &allow-other-keys was present, and then
the minimum and maximum number of arguments (or nil if max is infinite).
Finally, whether &key was present or not."
  ;; Movitz extension: &edx <var> may appear first in lambda-list
  (let ((edx-var nil))
    (when (eq 'muerte::&edx (first lambda-list))
      (pop lambda-list)
      (setf edx-var (pop lambda-list)))
    
    ;; We use sort of a unidirectional state-machine to traverse the
    ;; LAMBDA-LIST, stuffing the formals we encounter into different
    ;; slots according to the current state.
    (macrolet ((optional () '(second program))
	       (rest-var () '(third program))
	       (key () '(fourth program))
	       (aux () '(fifth program))
	       (allow-other-keys () '(if host-symbols-p
				      '&allow-other-keys
				      'muerte.cl::&allow-other-keys)))
      (loop for formal in lambda-list
	  with program = (if host-symbols-p
			     '(requireds &optional &rest &key &aux)
			   '(requireds muerte.cl::&optional muerte.cl::&rest
			     muerte.cl::&key muerte.cl::&aux))
	  with state = program
		       ;; (first state) is "current" state,
		       ;; (rest state) is the set of possible next states.
	  with results = (list nil)	; this property-list-to-be collects the results.
	  with allow-other-keys-p = nil
	  if (member formal (rest state))
	  do (progn			; proceed to next state
	       (push (first state) results)
	       (push nil results)	; place for next state's results
	       (setf state (member formal (rest state))))
	  else if (and (eq (first state) (key))
		       (eq formal (allow-other-keys))
		       (not allow-other-keys-p))
	  do (setf allow-other-keys-p t)
	  else do (push formal (car results))
	  finally
	    (push (first state) results)
	  finally
	    (let ((requireds (nreverse (getf results 'requireds)))
		  (optionals (nreverse (getf results (optional))))
		  (rests     (nreverse (getf results (rest-var))))
		  (keys      (nreverse (getf results (key))))
		  (auxes     (nreverse (getf results (aux)))))
	      (when (> (length rests) 1)
		(error "There can only be one &REST formal parameter."))
	      (let* ((keys-p (not (eq :missing ; &key present?
				      (getf results (key) :missing))))
		     (maxargs (and (null rests) ; max num. of arguments, or nil.
				   (not keys-p)
				   (not allow-other-keys-p)
				   (+ (length requireds)
				      (length optionals))))
		     (minargs (length requireds)))
		(return (values requireds
				optionals
				(first rests)
				keys
				auxes
				allow-other-keys-p
				minargs
				maxargs
				edx-var
				(cond
				 ((or (not keys-p)
				      (eql maxargs minargs))
				  nil)
				 ((assert (not maxargs) ()
					  "Weird maxargs ~S for ~S." maxargs lambda-list))
				 ((evenp (+ (length requireds) (length optionals)))
				  :even)
				 (t :odd))
				keys-p))))))))

(defun decode-optional-formal (formal)
  "3.4.1.2 Specifiers for optional parameters.
Decode {var | (var [init-form [supplied-p-parameter]])}
Return the variable, init-form, and suplied-p-parameter."
  (etypecase formal
    (symbol (values formal nil nil))
    (cons (values (first formal) (second formal) (third formal)))))

(defun decode-keyword-formal (formal)
  "3.4.1.4 Specifiers for keyword parameters.
Parse {var | ({var | (keyword-name var)} [init-form [supplied-p-parameter]])}
Return the variable, keyword-name, init-form and supplied-p-parameter, if any."
  (etypecase formal
    (null
     (error "Illegal keyword formal: ~S" formal))
    (symbol
     (values formal
	     (intern (string formal) :keyword)
	     nil
	     nil))
    (cons
     (if (consp (car formal))
	 (values (cadar formal) (caar formal) (second formal) (third formal))
       (values (car formal)
	       (intern (string (car formal)) :keyword)
	       (second formal)
	       (third formal))))))

(defun decode-aux-formal (formal)
  "Return variable-name and init-form."
  (etypecase formal
    (symbol (values formal nil))
    (cons (values (first formal) (second formal)))))

(defun list-normal-lambda-list-variables (lambda-list)
  "Return the list of variables that <lambda-list> defines."
  (multiple-value-bind (requireds optionals rest keys auxes)
      (decode-normal-lambda-list lambda-list)
    (append requireds
	    (mapcar #'decode-optional-formal optionals)
	    (mapcar #'decode-keyword-formal keys)
	    (mapcar #'decode-optional-formal auxes)
	    (list rest))))

(defun lambda-list-simplify (lambda-list)
  "Return a version of lambda-list with only the variables for &optional and &key formals."
  (multiple-value-bind (requireds optionals rest keys auxes x y z edx-var)
      (decode-normal-lambda-list lambda-list)
    (declare (ignore x y z))
    (append (when edx-var
	      `(muerte::&edx ,edx-var))
	    requireds
	    (when optionals
	      '(muerte.cl::&optional))
	    (mapcar #'decode-optional-formal optionals)
	    (when rest
	      (append '(muerte.cl::&rest) (list rest)))
	    (when (member 'muerte.cl::&key lambda-list)
	      '(muerte.cl::&key))
	    (mapcar #'decode-keyword-formal keys)
	    (when auxes
	      '(muerte.cl::&aux))
	    (mapcar #'decode-optional-formal auxes))))
	    

(defun decode-macro-lambda-list (lambda-list)
  "3.4.4 Macro Lambda Lists.
Does not deal with destructuring."
  (flet ((state-keywords (state)
	   (case state
	     (:env '(muerte.cl::&environment))
	     (:rest-or-body '(muerte.cl::&rest muerte.cl::&body))
	     (t (list state)))))
    (loop for (formal . next-formal) on lambda-list
	with state = '(nil muerte.cl::&whole :env reqvars :env muerte.cl::&optional :env
		       :rest-or-body :env muerte.cl::&key :env muerte.cl::&aux :env)
		     ;; (first state) is "current" state,
		     ;; (rest state) is the set of possible next states.
		     ;; nil means an indetermined state, where we need a lambda keyword.
	with results = nil		; this property-list-to-be collects the results.
	with allow-other-keys-p = nil
	if (member formal (rest state) :test #'member :key #'state-keywords)
	do (progn
;;;	     (push (first state) results) ; the plist indicator
;;;	     (push nil results)		; plist place for next state's results
	     (setf state (member formal (rest state) :test #'member :key #'state-keywords)))
	else if (and (eq (first state) 'muerte.cl::&key)
		     (eq formal 'muerte.cl::&allow-other-keys)
		     (not allow-other-keys-p)) do
	  (setf allow-other-keys-p t)
	else if (null (first state)) do	; at indetermined-state?
	  (cond
	   ((member 'reqvars state)	; have we not yet passed reqvars state?
	    (setf state (member 'reqvars state)) ; .. then jump to reqvars state.
	    (push formal (getf results 'reqvars)))
	   (t				; we have passed reqvars state..
	    (error "Illegal formal ~S in lambda-list ~S. Expected one of ~S."
		   formal lambda-list
		   (mapcan #'state-keywords
			   (remove-duplicates (remove nil state))))))
	else do
	     (push formal (getf results (first state)))
	and do
	    (case (first state)
	      ((muerte.cl::&whole :env)	; these only take one formal, so we must force state
	       (setf state (cons nil (rest state))))) ; .. to proceed, to an indetermined state.
	unless (listp next-formal) do	; deal with lambda lists that ends like (a b c . d).
	  (progn (push next-formal (getf results 'muerte.cl::&rest))
		 (loop-finish))
	finally
	  (let ((reqvars   (nreverse (getf results 'reqvars)))
		(envvars   (nreverse (getf results :env)))
		(wholevars (nreverse (getf results 'muerte.cl::&whole)))
		(optionals (nreverse (getf results 'muerte.cl::&optional)))
		(rests     (nreverse (getf results :rest-or-body)))
		(keys      (nreverse (getf results 'muerte.cl::&key)))
		(auxes     (nreverse (getf results 'muerte.cl::&aux))))
	    (when (> (length rests) 1)
	      (error "There can only be one &REST formal parameter in lambda-list ~S."
		     lambda-list))
	    (when (> (length envvars) 1)
	      (error "There can only be one &ENVIRONMENT formal parameter, found ~S." envvars))
	    (when (> (length wholevars) 1)
	      (error "There can only be one &WHOLE formal parameter, found ~S." wholevars))
	    (return (values (first wholevars)
			    (first envvars)
			    reqvars
			    optionals
			    (first rests)
			    keys
			    auxes
			    allow-other-keys-p))))))

(defun parse-d-bind-lambda-list (lambda-list proceed-scan)
  (multiple-value-bind (whole env requireds optionals rest keys)
      (decode-macro-lambda-list lambda-list)
    (declare (ignore keys whole env))
    (let ((scan-var (gensym "d-bind-scan-")))
      (append `((,scan-var ,proceed-scan))
	      (loop for required in requireds
		  append (parse-d-bind-formal required `(pop ,scan-var)))
	      (loop for optional in optionals
		  with var and init-form and supplied-p-parameter
		  do (multiple-value-setq (var init-form supplied-p-parameter)
		       (decode-optional-formal optional))
		  when supplied-p-parameter
		  collect
		    `(,supplied-p-parameter (if ,scan-var t nil))
		  append
		    (parse-d-bind-formal var (if init-form
						 `(if ,scan-var (pop ,scan-var) ,init-form)
					       `(pop ,scan-var))))
	      (when rest
		`((,rest ,scan-var)))))))

(defun parse-d-bind-formal (formal proceed-scan)
  (etypecase formal
    (null
     (let ((dummy-var (gensym "d-bind-dummy-")))
       `((,dummy-var ,proceed-scan))))
    (symbol
     `((,formal ,proceed-scan)))
    (list
     (parse-d-bind-lambda-list formal proceed-scan))))

(defun compute-function-block-name (function-name)
  (cond
   ((symbolp function-name) function-name)
   ((and (consp function-name)
	 (symbolp (cadr function-name)))
    (cadr function-name))
   (t (error "Unknown kind of function-name: ~S" function-name))))
  
