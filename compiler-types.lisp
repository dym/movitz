;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      compiler-types.lisp
;;;; Description:   Compile-time type computation and manipulation.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Sep 10 00:40:07 2003
;;;;                
;;;; $Id: compiler-types.lisp,v 1.27 2008-04-27 19:14:54 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defun type-specifier-num-values (type-specifier)
  "How many values does type-specifier represent?"
  (cond
   ((atom type-specifier)
    1)
   ((not (eq 'values (car type-specifier)))
    1)
   ((not (cdr type-specifier))
    0)
   ((null (intersection '(&optional &rest) (rest type-specifier)))
    (length (cdr type-specifier)))))

(defun type-specifier-nth-value (number type-specifier)
  "Return the type of the n'th value of a result type-specifier."
  (check-type number (integer 0 255))
  (cond
   ((or (atom type-specifier)
	(not (eq 'values (car type-specifier))))
    (if (= 0 number)
	type-specifier
      'null))
   ((null (cdr type-specifier))
    'null)				; Zero values => primary value is NIL
   (t (multiple-value-bind (reqs opts rest)
	  (decode-normal-lambda-list (cdr type-specifier) t)
	(cond
	 ((< number (length reqs))
	  (nth number reqs))
	 ((< number (+ (length reqs) (length opts)))
	  (let ((x (nth (- number (length reqs)) opts)))
	    (if (eq x t) t `(or null ,x))))
	 (rest
	  (if (eq rest t) t `(or null ,rest)))
	 (t 'null))))))

(defun type-specifier-primary (type-specifier)
  (type-specifier-nth-value 0 type-specifier))

(defun type-specifier-singleton (type-specifier)
  "If type-specifier is a singleton type, return a singleton list
with the single member of <type-specifier>."
  (multiple-value-call #'encoded-type-singleton
    (type-specifier-encode type-specifier)))
      
;;; A numscope is a subset of the integers.

(defun make-numscope (&optional minimum maximum)
  (check-type minimum (or number null))
  (check-type maximum (or number null))
  (list (cons minimum maximum)))

(defun numscope-minimum (numscope)
  (loop for sub-range in numscope
      if (not (car sub-range))
      return nil
      minimize (car sub-range)))

(defun numscope-maximum (numscope)
  (loop for sub-range in numscope
      if (not (cdr sub-range))
      return nil
      minimize (car sub-range)))

(defun numscope-memberp (numscope x)
  "Is <x> in numscope?"
  (dolist (sub-range numscope nil)
    (cond
     ((and (not (car sub-range)) (not (cdr sub-range)))
      (return t))
     ((not (car sub-range))
      (when (<= x (cdr sub-range))
	(return t)))
     ((not (cdr sub-range))
      (when (<= (car sub-range) x)
	(return t)))
     ((<= (car sub-range) x (cdr sub-range))
      (return t)))))

(defun numscope-add-range (numscope min max &optional (epsilon 1))
  "Add [min .. max] to numscope."
  (assert (or (null min) (null max) (<= min max)))
  (if (null numscope)
      (list (cons min max))
    (let ((new-min min)
	  (new-max max)
	  (new-numscope ()))
      (dolist (sub-range numscope)
	(cond
	 ((and (not (car sub-range))
	       (not (cdr sub-range)))
	  (setf new-min nil
		new-max nil))
	 ((not (car sub-range))
	  (if (and (cdr sub-range) new-min (<= (cdr sub-range) (- new-min epsilon)))
	      (push sub-range new-numscope)
	    (setf new-min nil
		  new-max (and new-max (max new-max (cdr sub-range))))))
	 ((not (cdr sub-range))
	  (if (and (car sub-range) new-max (<= (+ new-max epsilon) (car sub-range)))
	      (push sub-range new-numscope)
	    (setf new-min (and new-min (min new-min (car sub-range)))
		  new-max nil)))
	 ((cond				; is <new-min, new-max> overlapping sub-range?
	   ((and (not new-min) (not new-max)) t)
	   ((not new-min) (<= (car sub-range) (+ epsilon new-max)))
	   ((not new-max) (<= new-min (+ epsilon (cdr sub-range))))
	   ((<= (- new-min epsilon) (car sub-range) (+ new-max epsilon)) t)
	   ((<= (- new-min epsilon) (cdr sub-range) (+ new-max epsilon)) t)
	   ((<= (car sub-range) new-min (cdr sub-range))))
	  (setf new-min (and new-min (min new-min (car sub-range)))
		new-max (and new-max (max new-max (cdr sub-range)))))
	 (t ;; (warn "Unaffected sub-range: ~A for ~D-~D" sub-range new-min new-max)
	    (push sub-range new-numscope))))
      (sort (cons (cons new-min new-max) new-numscope)
	    (lambda (x y)
	      (and x y (< x y)))
	    :key (lambda (x) (or (car x) (cdr x)))))))

(defun numscope-subtract-range (numscope min max &optional (epsilon 1))
  "Remove [min .. max] from numscope."
  (cond
   ((null numscope)
    ;; nothing minus anything is still nothing.
    nil)
   ((and (not min) (not max))
    ;; anything minus everything is nothing.
    nil)
   (t (let ((new-numscope ()))
	(dolist (sub-range numscope)
	  (let ((a (or (not min) (and (car sub-range) ; subtrahend extends below sub-range-min?
				      (<= min (car sub-range)))))
		(b (or (not max) (and (cdr sub-range) ; subtrahend extends above sub-range-max?
				      (<= (cdr sub-range) max))))
		(c (and max (car sub-range) ; subtrahend ends below sub-range?
			(<= max (+ (car sub-range) epsilon))))
		(d (and min (cdr sub-range) ; subtrahend starts above sub-range?
			(<= (+ (cdr sub-range) epsilon) min))))
	    #+ignore (warn "abcd: ~S ~S ~S ~S" a b c d)
	    (cond
	     ((and a b)
	      ;; sub-range is eclipsed by the subtrahend.
	      nil)
	     ((or c d)
	      ;; sub-range is disjoint from subtrahend.
	      (setf new-numscope
		(numscope-add-range new-numscope (car sub-range) (cdr sub-range) epsilon)))
	     ((and (not a) (not b) (not c) (not d))
	      ;; subtrahend is eclipsed by sub-range, which is split in two pieces.
	      (setf new-numscope
		(numscope-add-range new-numscope (car sub-range) (- min epsilon) epsilon))
	      (setf new-numscope
		(numscope-add-range new-numscope (+ max epsilon) (cdr sub-range) epsilon)))
	     ((and a (not c))		; (warn "left prune ~D with [~D - ~D]" new-numscope min max)
	      (setf new-numscope
		(numscope-add-range new-numscope (+ max epsilon) (cdr sub-range) epsilon)))
	     ((and (not d) b)		; (warn "right prune ~D with [~D-~D]" sub-range min max)
	      (setf new-numscope
		(numscope-add-range new-numscope (car sub-range) (- min epsilon) epsilon)))
	     (t (break "I am confused!")))))
	new-numscope))))

(defun numscope-complement (numscope &optional (epsilon 1))
  (let ((new-numscope (make-numscope nil nil)))
    (dolist (sub-range numscope)
      (setf new-numscope
	(numscope-subtract-range new-numscope (car sub-range) (cdr sub-range) epsilon)))
    new-numscope))

(defun numscope-union (range0 range1 &optional (epsilon 1))
  (dolist (sub-range range0 range1)
    (setf range1 (numscope-add-range range1 (car sub-range) (cdr sub-range) epsilon))))

(defun numscope-intersection (range0 range1 &optional (epsilon 1))
  (if (or (null range0) (null range1))
      nil
    ;; <Krystof> (A n B) = ~(~A u ~B)
    (numscope-complement (numscope-union (numscope-complement range0 epsilon)
					 (numscope-complement range1 epsilon)
					 epsilon)
			 epsilon)))

(defun numscope-equalp (range0 range1)
  ;; Numscopes should always be kept on canonical form.
  (equal range0 range1))

(defun numscope-subsetp (range0 range1)
  "Is range0 included in range1?"
  (numscope-equalp range1 (numscope-union range0 range1)))

(defun numscope-allp (range)
  "Does this numscope include every number?"
  (let ((x (car range)))
    (and x (not (car x)) (not (cdr x)))))
    

(defun numscope-combine (function range0 range1)
  (let ((result ()))
    (dolist (sub-range0 range0)
      (dolist (sub-range1 range1)
	(setf result
	  (numscope-union result
			  (funcall function
				   (car sub-range0) (cdr sub-range0)
				   (car sub-range1) (cdr sub-range1))))))
    result))

(defun numscope-plus (range0 range1)
  "Return the numscope that covers the sum of any element of range0
and any element of range1."
  (numscope-combine (lambda (min0 max0 min1 max1)
		      (make-numscope (and min0 min1 (+ min0 min1))
				     (and max0 max1 (+ max0 max1))))
		    range0 range1))

;;;

(defparameter *tb-bitmap*
  '(hash-table character function cons keyword symbol vector array integer ratio complex :tail)
  "The union of these types must be t.")

(defun basic-typep (x type)
  (ecase type
    (hash-table
     (and (typep x 'movitz-struct)
	  (eq (muerte::movitz-find-class 'muerte.cl:hash-table)
	      (slot-value x 'class))))
    (complex
     (and (typep x 'movitz-struct)
	  (eq (muerte::movitz-find-class 'muerte.cl:complex)
	      (slot-value x 'class))))
    (character
     (typep x 'movitz-character))
    (function
     (typep x 'movitz-funobj))
    (cons
     (typep x 'movitz-cons))
    (symbol
     (typep x 'movitz-symbol))
    ((vector array)
     (typep x 'movitz-basic-vector))
    (fixnum
     (typep x 'movitz-fixnum))
    (bignum
     (typep x 'movitz-bignum))
    (ratio
     (typep x 'movitz-ratio))))

(defun type-code (first-type &rest types)
  "Find the code (a bitmap) for (or ,@types)."
  (declare (dynamic-extent types))
  (if (eq t first-type)
      -1
    (labels ((code (x)
	       (if (not x)
		   0
		 (let ((pos (position x *tb-bitmap*)))
		   (assert pos (x) "Type ~S not recognized." x)
		   (let ((code (ash 1 pos)))
		     (case x
		       (symbol (logior code (code 'keyword)))
		       (array  (logior code (code 'vector)))
		       ;; (number (logior code (code 'integer)))
		       (t code)))))))
      (reduce #'logior (mapcar #'code types)
	      :initial-value (code first-type)))))

(defun encoded-type-decode (code integer-range members include complement)
  (cond
   ((let ((mask (1- (ash 1 (position :tail *tb-bitmap*)))))
      (= mask (logand mask code)))
    (not complement))
   (t (let ((sub-specs include))
	(loop for x in *tb-bitmap* as bit upfrom 0
	    do (when (logbitp bit code)
		 (push x sub-specs)))
	(when (not (null members))
	  (push (cons 'member members) sub-specs))
	(when (numscope-allp integer-range)
	  (pushnew 'integer sub-specs))
	(when (and (not (member 'integer sub-specs))
		   integer-range)
	  (dolist (sub-range integer-range)
	    (push (list 'integer
			(or (car sub-range) '*)
			(or (cdr sub-range) '*))
		  sub-specs)))
	(cond
	 ((null sub-specs)
	  (if complement t nil))
	 ((not (cdr sub-specs))
	  (if (not complement)
	      (car sub-specs)
	    (list 'not (car sub-specs))))
	 (t (if (not complement)
		(cons 'or sub-specs)
	      (list 'not (cons 'or sub-specs)))))))))
		  
(defun type-values (codes &key integer-range members include complement)
  ;; Members: A list of objects explicitly included in type.
  ;; Include: A list of (non-encodable) type-specs included in type.
  (check-type include list)
  (check-type members list)
  (check-type integer-range list)
  (when (eq 'and (car include))
    (break "foo"))
  (let ((new-intscope integer-range)
	(new-members ()))
    (dolist (member members)		; move integer members into integer-range
      (let ((member (movitz-read member)))
	(etypecase member
	  (movitz-fixnum
	   (setf new-intscope
	     (numscope-union new-intscope	    
			     (make-numscope (movitz-fixnum-value member)
					    (movitz-fixnum-value member)))))
	  (movitz-object
	   (pushnew member new-members :test #'movitz-eql)))))
    (let ((new-code (logior (if (atom codes)
				(type-code codes)
			      (apply #'type-code codes))
			    (if (numscope-allp new-intscope)
				(type-code 'integer)
			      0))))
      (values new-code
	      (if (type-code-p 'integer new-code)
		  (make-numscope nil nil)
		new-intscope)
	      new-members
	      include
	      complement))))

(defun star-is-t (x)
  (if (eq x '*) t x))

(defun type-code-p (basic-type code)
  "is <type-code> included in <code>?"
  (let ((x (type-code basic-type)))
    (= x (logand x code))))

(defun encoded-typep (errorp undecided-value x code integer-range members include complement)
  "Is the movitz-object x included in the encoded-type?"
  (let ((x (or (= -1 code)
	       (and (member x members :test #'movitz-eql) t)
	       (cond
		((typep x 'movitz-null)
		 (type-code-p 'symbol code))
		((basic-typep x 'fixnum)
		 (or (type-code-p 'integer code)
		     (and integer-range
			  (numscope-memberp integer-range (movitz-fixnum-value x)))))
		((basic-typep x 'bignum)
		 (or (type-code-p 'integer code)
		     (and integer-range
			  (numscope-memberp integer-range (movitz-bignum-value x)))))
		(t (dolist (bt '(symbol character function cons hash-table vector ratio complex)
			     (error "Cant decide typep for ~S." x))
		     (when (basic-typep x bt)
		       (return (type-code-p bt code))))))
	       (if (not include)
		   nil
		 (if errorp
		     (error "Can't decide typep for ~S because it includes ~S." x include)
		   (return-from encoded-typep undecided-value))))))
    (if complement (not x) (and x t))))

(defun encoded-types-and (code0 integer-range0 members0 include0 complement0
			  code1 integer-range1 members1 include1 complement1)
  (cond
   ((or (encoded-emptyp code0 integer-range0 members0 include0 complement0)
	(encoded-emptyp code1 integer-range1 members1 include1 complement1))
    (type-values nil))
   ((encoded-allp code0 integer-range0 members0 include0 complement0)
    (values code1 integer-range1 members1 include1 complement1))
   ((encoded-allp code1 integer-range1 members1 include1 complement1)
    (values code0 integer-range0 members0 include0 complement0))
   ((and (not complement0) (not complement1))
    (cond
     ((and (null include0) (null include1))
      (values (logand code0 code1)
	      (when (or integer-range0 integer-range1)
		(numscope-intersection integer-range0 integer-range1))
	      (remove-if (lambda (x)
			   (not (encoded-typep t nil x code0 integer-range0 members0 include0 nil)))
			 members1)
	      nil nil))
     ((and (encoded-emptyp code0 nil members0 include0 complement0)
	   (encoded-emptyp code1 nil members1 nil complement1)
	   (flet ((integer-super-p (x)
		    (member x '(rational real number t))))
	     (every #'integer-super-p include1)))
      (type-values () :integer-range integer-range0))
     ((and (encoded-emptyp code0 nil members0 nil complement0)
	   (encoded-emptyp code1 nil members1 include1 complement1)
	   (flet ((integer-super-p (x)
		    (member x '(rational real number t))))
	     (every #'integer-super-p include0)))
      (type-values () :integer-range integer-range1))
     ((and (= code0 code1) (equal integer-range0 integer-range1)
	   (equal members0 members1) (equal include0 include1)
	   (eq complement0 complement1))
      (values code0 integer-range0 members0 include0 complement0))
     ((and include0 (null include1))
      ;; (and (or a b c) d) => (or (and a d) (and b d) (and c d))
      (values (logand code0 code1)
	      (when (or integer-range0 integer-range1)
		(numscope-intersection integer-range0 integer-range1))
	      (intersection members0 members1)
	      (mapcar (lambda (sub0)
			`(and ,sub0 ,(encoded-type-decode code1 integer-range1 members1 include1 nil)))
		      include0)
	      nil))
     ((and (null include0) include1)
      ;; (and (or a b c) d) => (or (and a d) (and b d) (and c d))
      (values (logand code0 code1)
	      (when (or integer-range0 integer-range1)
		(numscope-intersection integer-range0 integer-range1))
	      (intersection members0 members1)
	      (mapcar (lambda (sub1)
			`(and ,sub1 ,(encoded-type-decode code0 integer-range0 members0 include0 nil)))
		      include1)
	      nil))
     (t ;; (warn "and with two includes: ~S ~S" include0 include1)
	(type-values () :include `((and ,(encoded-type-decode code0 integer-range0 members0
							      include0 complement0)
					,(encoded-type-decode code1 integer-range1 members1
							      include1 complement1)))))))
   ((and complement0 complement1)
    (multiple-value-bind (code integer-range members include complement)
	(encoded-types-or code0 integer-range0 members0 include0 (not complement0)
			  code1 integer-range1 members1 include1 (not complement1))
      (values code integer-range members include (not complement))))
   (t (type-values () :include `((and ,(encoded-type-decode code0 integer-range0 members0
							    include0 complement0)
				      ,(encoded-type-decode code1 integer-range1 members1
							    include1 complement1)))))))

(defun encoded-types-or (code0 integer-range0 members0 include0 complement0
			 code1 integer-range1 members1 include1 complement1)
  (cond
   ((or (encoded-allp code0 integer-range0 members0 include0 complement0)
	(encoded-allp code1 integer-range1 members1 include1 complement1))
    (type-values t))
   ((encoded-emptyp code0 integer-range0 members0 include0 complement0)
    (values code1 integer-range1 members1 include1 complement1))
   ((encoded-emptyp code1 integer-range1 members1 include1 complement1)
    (values code0 integer-range0 members0 include0 complement0))
   ((and (not complement0) (not complement1))
    (let* ((new-inumscope (numscope-union integer-range0 integer-range1))
	   (new-code (logior code0 code1 (if (numscope-allp new-inumscope)
					     (type-code 'integer)
					   0))))
      (values new-code
	      (if (type-code-p 'integer new-code)
		  nil
		new-inumscope)
	      (remove-if (lambda (x)
			   (or (encoded-typep nil t x code0 integer-range0 nil include0 nil)
			       (encoded-typep nil t x code1 integer-range1 nil include1 nil)))
			 (union members0 members1 :test #'movitz-eql))
	      (union include0 include1 :test #'equal)
	      nil)))
   ((and (not complement0) complement1)
    (values code0
	    integer-range0
	    members0
	    (cons (encoded-type-decode code1 integer-range1 members1 include1 complement1)
		  include0)
	    nil))
   (t (error "Not implemented: ~S or ~S"
	     (encoded-type-decode code0 integer-range0 members0 include0 complement0)
	     (encoded-type-decode code1 integer-range1 members1 include1 complement1)))))


(defun type-specifier-encode (type-specifier)
  "Encode a type-specifier to internal representation."
  (let ((type-specifier (translate-program type-specifier :muerte.cl :cl)))
    (cond
     ((atom type-specifier)
      (case type-specifier
	(fixnum
	 (type-specifier-encode `(signed-byte ,+movitz-fixnum-bits+)))
	(bignum
	 (type-specifier-encode `(or (integer * ,(1- +movitz-most-negative-fixnum+))
				     (integer ,(1+ +movitz-most-positive-fixnum+) *))))
	((t nil cons symbol keyword function array vector integer hash-table character)
	 (type-values type-specifier))
	(null
	 (type-values () :members '(nil)))
	(list
	 (type-values 'cons :members '(nil)))
	(sequence
	 (type-values '(vector cons) :members '(nil)))
	(t (let ((deriver (and (boundp '*image*)
			       (gethash type-specifier muerte::*compiler-derived-typespecs*))))
	     (if deriver
		 (type-specifier-encode (funcall deriver))
	       (type-values () :include (list type-specifier)))))))
     ((listp type-specifier)
      (check-type (car type-specifier) symbol)
      (case (car type-specifier)
	(satisfies
	 (type-values () :include (list type-specifier)))
	(member
	 (apply #'member-type-encode (cdr type-specifier)))
	(eql
	 (member-type-encode (second type-specifier)))
	(and
	 (if (not (cdr type-specifier))
	     (type-values t)
	   (multiple-value-bind (code integer-range members include complement)
	       (type-specifier-encode (second type-specifier))
	     (dolist (sub-specifier (cddr type-specifier))
	       (multiple-value-setq (code integer-range members include complement)
		 (multiple-value-call #'encoded-types-and code integer-range members include complement
				      (type-specifier-encode sub-specifier))))
	     (values code integer-range members include complement))))
	(or
	 (if (not (cdr type-specifier))
	     (type-values nil)
	   (multiple-value-bind (code integer-range members include complement)
	       (type-specifier-encode (second type-specifier))
	     (dolist (sub-specifier (cddr type-specifier))
	       (multiple-value-setq (code integer-range members include complement)
		 (multiple-value-call #'encoded-types-or code integer-range members include complement
				      (type-specifier-encode sub-specifier))))
	     (values code integer-range members include complement))))
	(not
	 (assert (= 2 (length type-specifier)))
	 (multiple-value-bind (code integer-range members include complement)
	     (type-specifier-encode (second type-specifier))
	   (cond
	    ((encoded-allp code integer-range members include complement)
	     (type-specifier-encode nil))
	    ((encoded-emptyp code integer-range members include complement)
	     (type-specifier-encode t))
	    (t (values code integer-range members include (not complement))))))
	(integer
	 (flet ((integer-limit (s n)
		  (let ((x (if (nthcdr n s)
			       (nth n s)
			     '*)))
		    (cond
		     ((integerp x) x)
		     ((eq x '*) nil)
		     (t (error "Not an in integer limit: ~S" x))))))
	   (type-values () :integer-range (make-numscope (integer-limit type-specifier 1)
							 (integer-limit type-specifier 2)))))
	(cons
	 (let ((car (star-is-t (if (cdr type-specifier) (second type-specifier) '*)))
	       (cdr (star-is-t (if (cddr type-specifier) (third type-specifier) '*))))
	   (if (and (eq t car) (eq t cdr))
	       (type-values 'cons)
	     (type-values () :include (list type-specifier)))))
	((array vector binding-type)
	 (type-values () :include (list type-specifier)))
	(t (let ((deriver (and (boundp '*image*)
			       (gethash (translate-program (car type-specifier)
							   :cl :muerte.cl)
					muerte::*compiler-derived-typespecs*))))
	     (assert deriver (type-specifier)
	       "Unknown type ~S." type-specifier)
	     (type-specifier-encode (apply deriver (cdr type-specifier))))))))))

(defun member-type-encode (&rest member-objects)
  "Encode a member type-specifier holding member-objects."
  (declare (dynamic-extent members))
  (multiple-value-bind (code integer-range members include complement)
      (type-specifier-encode nil)
    (dolist (x member-objects)
      (let ((member (movitz-read x)))
	(multiple-value-setq (code integer-range members include complement)
	  (multiple-value-call #'encoded-types-or
	    code integer-range members include complement
	    (etypecase member
	      (movitz-fixnum
	       (type-values () :integer-range (make-numscope (movitz-fixnum-value member)
							     (movitz-fixnum-value member))))
	      (movitz-object
	       (type-values () :members (list member))))))))
    (values code integer-range members include complement)))

(defun encoded-emptyp (code integer-range members include complement)
  "Return wether we know the encoded type is the empty set.
If it isn't, also return wether we _know_ it isn't empty."
  (let ((x (and (= 0 code) (not integer-range) (null members) t)))
    (cond
     ((and x (null include) (not complement))
      (values t t))
     ((and (null include) complement)
      (cond
       ((encoded-allp code integer-range members include nil)
	(warn "Seeing an encoded (not t), should be ()")
	(values t t))
       (t (values nil t))))
     ((not (null include))
      (values nil nil)))))

(defun encoded-allp (code integer-range members include complement)
  "Return wether we know the encoded type is the all-inclusive set.
If it isn't, also return wether we _know_ it isn't."
  (cond
   ((let ((mask (1- (ash 1 (position :tail *tb-bitmap*)))))
      (= mask (logand mask code)))
    (values (if complement nil t) t))
   ((and complement
	 (encoded-emptyp code integer-range members include complement))
    (values t t))
   ((null include)
    (values nil t))
   (t (values nil nil))))

(defun encoded-numscope (code integer-range)
  (if (type-code-p 'integer code)
      (make-numscope nil nil)
    integer-range))

(defun encoded-subtypep (code0 integer-range0 members0 include0 complement0
			 code1 integer-range1 members1 include1 complement1)
  "Is every member of 0 also a member of 1?"
  (macrolet ((result-is (subtypep decisivep)
	       `(return-from encoded-subtypep (values ,subtypep ,decisivep))))
    (block encoded-subtypep
      (cond
       ((encoded-allp code1 integer-range1 members1 include1 complement1)
	;; type1 is t.
	(result-is t t))
       ((encoded-emptyp code0 integer-range0 members0 include0 complement0)
	;; type0 is nil, which is a subtype of anything.
	(result-is t t))
       ((and (encoded-emptyp code1 integer-range1 members1 include1 complement1)
	     #+ignore (not (encoded-emptyp code0 integer-range0 members0 include0 complement0)))
	;; type1 is nil and type0 isn't.
	(result-is nil t))
       ((and (encoded-allp code0 integer-range0 members0 include0 complement0)
	     (multiple-value-bind (all1 confident)
		 (encoded-allp code1 integer-range1 members1 include1 complement1)
	       (and (not all1) confident)))
	;; type0 is t, and type1 isn't.
	(result-is nil t))
       ((and (not complement0) (not complement1))
	(dolist (st *tb-bitmap*)
	  (when (type-code-p st code0)
	    (unless (type-code-p st code1)
	      (result-is nil t))))
	(unless (numscope-subsetp (encoded-numscope code0 integer-range0)
				  (encoded-numscope code1 integer-range1))
	  (result-is nil t))
	(dolist (m members0)
	  (ecase (encoded-typep nil :unknown m code1 integer-range1 members1 include1 nil)
	    ((nil)
	     (result-is nil t))
	    ((:unknown)
	     (result-is nil nil))
	    ((t) nil)))
	(if include0
	    (result-is nil nil)
	  (result-is t t)))
       ((and complement0 complement1)
	(encoded-subtypep code1 integer-range1 members1 include1 nil
			  code0 integer-range0 members0 include0 nil))
       (t (result-is nil nil))))))

(defun encoded-type-singleton (code intscope members include complement)
  "If the encoded type is a singleton, return that element in a list."
  (cond
   ((or complement include (not (= 0 code)))
    nil)
   ((and (= 1 (length members))
	 (= 0 code) (null intscope) (null include) (not complement))
    members)
   ((and (= 1 (length intscope))
	 (caar intscope)
	 (eql (caar intscope)
	      (cdar intscope)))
    (list (movitz-read (caar intscope))))
   ((and (null members) (null intscope))
    (break "Not singleton, nulloton."))))

(defun movitz-subtypep (type0 type1)
  "Compile-time subtypep."
  (multiple-value-call #'encoded-subtypep
    (type-specifier-encode type0)
    (type-specifier-encode type1)))

(defun encoded-integer-types-add (code0 integer-range0 members0 include0 complement0
				  code1 integer-range1 members1 include1 complement1)
  "Return the integer type that can result from adding a member of type0 to a member of type1."
  ;; (declare (ignore members0 members1))
  (cond
   ((or include0 include1 members0 members1 (/= 0 code0) (/= 0 code1))
    ;; We can't know..
    'number)
   ((or complement0 complement1)
    (break "adding complement types..?"))
   (t (let ((integer-range (numscope-plus (encoded-numscope code0 integer-range0)
					  (encoded-numscope code1 integer-range1))))
	(encoded-type-decode (if (not (numscope-allp integer-range))
				 0
			       (type-code 'integer))
			     integer-range
			     nil nil nil)))))
