;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2004,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      lists.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Dec  5 18:40:11 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: lists.lisp,v 1.3 2004/02/03 09:57:49 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/cons)
(provide :muerte/lists)

(in-package muerte)

(defun first (x)
  (declare (type list x))
  (car x))

(defun rest (x)
  (declare (type list x))
  (cdr x))

;; Compiler-macros for first and rest in basic-macros.lisp.

(defun second  (x) (cadr x))
(defun third   (x) (caddr x))
(defun fourth  (x) (car (nthcdr 3 x)))
(defun fifth   (x) (car (nthcdr 4 x)))
(defun sixth   (x) (car (nthcdr 5 x)))
(defun seventh (x) (car (nthcdr 6 x)))
(defun eighth  (x) (car (nthcdr 7 x)))
(defun ninth   (x) (car (nthcdr 8 x)))
(defun tenth   (x) (car (nthcdr 9 x)))

(defun (setf second)  (value list) (setf (cadr list) value))
(defun (setf third)   (value list) (setf (caddr list) value))
(defun (setf fourth)  (value list) (setf (car (nthcdr 3 list)) value))
(defun (setf fifth)   (value list) (setf (car (nthcdr 4 list)) value))
(defun (setf sixth)   (value list) (setf (car (nthcdr 5 list)) value))
(defun (setf seventh) (value list) (setf (car (nthcdr 6 list)) value))
(defun (setf eighth)  (value list) (setf (car (nthcdr 7 list)) value))
(defun (setf ninth)   (value list) (setf (car (nthcdr 8 list)) value))
(defun (setf tenth)   (value list) (setf (car (nthcdr 9 list)) value))

(define-primitive-function fast-endp ()
  "Actual ENDP code."
  (with-inline-assembly (:returns :boolean-zf=1)
    (:leal (:eax -1) :ecx)
    (:cmpl :edi :eax)
    (:je 'done)				; NIL, ZF=1
    (:testb 7 :cl)
    
    (:jnz '(:sub-program () (:int 66)))
    (:testl :edi :edi)			; ZF=0
    done
    (:ret)))

(defun endp (x)
  (endp x))				; compiler-macro

(defun assoc (item alist &key (test 'eql) (key 'identity))
  (numargs-case
   (2 (item alist)
      (dolist (a alist)
	(when (eql item (car a))
	  (return a))))
   (t (item alist &key (test 'eql) (key 'identity))
      (with-funcallable (key)
	(with-funcallable (test)
	  (dolist (a alist)
	    (when (test item (key (car a)))
	      (return a))))))))

(defun rassoc (item alist &key (test 'eql) (key 'identity))
  (numargs-case
   (2 (item alist)
      (dolist (a alist)
	(when (eql item (cdr a))
	  (return a))))
   (t (item alist &key (test 'eql) (key 'identity))
      (with-funcallable (key)
	(with-funcallable (test)
	  (dolist (a alist)
	    (when (test item (key (cdr a)))
	      (return a))))))))

(defun list-length (x)
  (do ((n 0 (+ n 2))			;Counter.
       (fast x (cddr fast))		;Fast pointer: leaps by 2.
       (slow x (cdr slow)))		;Slow pointer: leaps by 1.
      (nil)
    ;; If fast pointer hits the end, return the count.
    (when (endp fast) (return n))
    (when (endp (cdr fast)) (return (+ n 1)))
    ;; If fast pointer eventually equals slow pointer,
    ;;  then we must be stuck in a circular list.
    ;; (A deeper property is the converse: if we are
    ;;  stuck in a circular list, then eventually the
    ;;  fast pointer will equal the slow pointer.
    ;;  That fact justifies this implementation.)
    (when (and (eq fast slow) (> n 0)) (return nil))))

(defun member (item list &key (key 'identity) (test 'eql))
  (numargs-case
   (2 (item list)
      (do ((p list (cdr p)))
	  ((endp p) nil)
	(when (eql item (car p))
	  (return p))))
   (t (item list &key (key 'identity) (test 'eql))
      (with-funcallable (key)
	(with-funcallable (test)
	  (do ((p list (cdr p)))
	      ((endp p) nil)
	    (when (test item (key (car p)))
	      (return p))))))))

(defun last (list &optional (n 1))
  ;; from the hyperspec..
  (check-type n integer)		; (integer 0))
  (do ((l list (cdr l))
       (r list)
       (i 0 (+ i 1)))
      ((atom l) r)
    (if (>= i n) (pop r))))

(defun nthcdr (n list)
  (do ()
      ((= 0 n) list)
    (decf n)
    (setf list (cdr list))))

(defun nth (n list)
  (car (nthcdr n list)))

(defun (setf nth) (value n list)
  (setf (car (nthcdr n list)) value))

(defun tree-equal (tree-1 tree-2 &key (test 'equal))
  (cond
   ((atom tree-1)
    (and (atom tree-2)
	 (funcall test tree-1 tree-2)))
   ((atom tree-2)
    nil)
   (t (and (tree-equal (car tree-1) (car tree-2) :test test)
	   (tree-equal (cdr tree-1) (cdr tree-2) :test test)))))


(defun nconc (&rest lists)
  (declare (dynamic-extent lists))
  (case (length lists)
    (0 nil)
    (1 (first lists))
    (t (let ((start  (do ((x lists (cdr x)))
			 ((or (endp x) (car x)) x))))
	 (if (atom (car start))
	     (car start)
	   (do* ((x (cdr start) (cdr x))
		 (y (car start)))
	       ((endp x) (car start))
	     (let ((z (car x)))
	       (setf (cdr (last y)) z)
	       (when (consp z)
		 (setq y z)))))))))

(defun append (&rest lists)
  (declare (dynamic-extent lists))
  (case (length lists)
    (0 nil)
    (1 (first lists))
    (t (do ((copied-result nil)
	    (previous-copy nil)
	    (x lists (cdr x))
	    (x+ (cdr lists) (cdr x+)))
	   ((endp x+) (cond
		       (previous-copy
			(setf (cdr (last previous-copy))
			  (car x))
			copied-result)
		       (copied-result
			(setf (cdr (last copied-result))
			  (car x))
			copied-result)
		       (t (car x))))
	 (when (consp (car x))
	   (let ((copy (copy-list (car x))))
	     (if previous-copy
		 (setf (cdr (last previous-copy)) copy)
	       (setf copied-result copy))
	     (setf previous-copy copy)))))))

(defun copy-list (list)
  (if (null list)
      nil
    (do* ((new-list (cons (pop list) nil))
	  (new-tail new-list (cdr new-tail)))
	((null list) new-list)
      (setf (cdr new-tail) (cons (pop list) nil)))))

(defun list (&rest objects)
  (numargs-case
   (1 (x) (cons x nil))
   (2 (x y)
      (cons x (cons y nil)))
   (3 (x y z)
      (cons x (cons y (cons z nil))))
   (t (&rest objects)
      (declare (dynamic-extent objects))
      (copy-list objects))))

(defun list* (first-object &rest more-objects)
  (numargs-case
   (1 (x) x)
   (2 (x y) (cons x y))
   (3 (x y z) (cons x (cons y z)))
   (t (first-object &rest more-objects)
      (declare (dynamic-extent more-objects))
      (if (null more-objects)
	  first-object
	(do* ((new-list (cons first-object nil))
	      (new-tail new-list (cdr new-tail)))
	    ((null (cdr more-objects))
	     (setf (cdr new-tail) (car more-objects))
	     new-list)
	  (setf (cdr new-tail) (cons (pop more-objects) nil)))))))

(defun make-list (size &key initial-element)
  (do ((list nil (cons initial-element list))
       (c size (1- c)))
      ((<= c 0) list)))

(defun getf (plist indicator &optional default)
  (do ((p plist (cddr p)))
      ((null p) default)
    (when (eq indicator (car p))
      (return (cadr p)))))

;;;(defun (setf getf) (value plist indicator &optional default)
;;;  (error "Must be implemented as a macro.."))

(defsetf getf (plist indicator &optional default) (new-value)
  `(do ((p ,plist (cddr p)))
       ((null p)
	(print ',plist)
	(print (setf ,plist (list* ,indicator ,new-value ,plist)))
	,new-value)
     (when (eq ,indicator (car p))
       (return (setf (cadr p) ,new-value)))))

(defun putf (plist indicator new-value)
  (do ((p plist (cddr p)))
      ((null p)
       (list* indicator new-value plist))
    (when (eq indicator (car p))
      (setf (cadr p) new-value)
      (return plist))))

(define-setf-expander getf (place indicator &optional default &environment env)
  (multiple-value-bind (temps values stores setter getter)
      (get-setf-expansion place env)
    (let ((new-value (gensym))
	  (indicator-var (gensym))
	  (default-var (if default (gensym))))
      (values `(,@temps ,indicator-var ,@(if default (list default-var)))
	      `(,@values ,indicator ,@(if default (list default)))
	      `(,new-value)
	      `(let ((,(car stores) (putf ,getter ,indicator-var ,new-value)))
		 ,setter
		 ,new-value)
	      `(getf ,getter ,indicator-var ,@(if default (list default-var)))))))

(defun get-properties (plist indicator-list)
  "=> indicator, value, tail"
  (do ((p plist (cddr p)))
      ((endp p)
       (values nil nil nil))
    (when (member (car p) indicator-list)
      (return (values (car p) (cadr p) p)))))

(defun mapcar (function first-list &rest more-lists)
  (declare (dynamic-extent more-lists))
  (cond
   ((null more-lists)
    ;; 1 list
    (do ((result nil)
	 (p first-list (cdr p)))
	((endp p) (nreverse result))
      (push (funcall function (car p))
	    result)))
   ((null (cdr more-lists))
    ;; two lists
    (do ((result nil)
	 (p1 first-list (cdr p1))
	 (p2 (car more-lists) (cdr p2)))
	((or (endp p1) (endp p2)) (nreverse result))
      (push (funcall function (car p1) (car p2))
	    result)))
   ((null (cddr more-lists))
    ;; three lists
    (do ((result nil)
	 (p1 first-list (cdr p1))
	 (p2 (car more-lists) (cdr p2))
	 (p3 (cadr more-lists) (cdr p2)))
	((or (endp p1) (endp p2) (endp p3)) (nreverse result))
      (push (funcall function (car p1) (car p2) (car p3))
	    result)))
   (t (error "mapcar not fully implemented."))))

(defun mapc (function first-list &rest more-lists)
  (numargs-case
   (2 (function first-list)
      (with-funcallable (map function)
	(dolist (item first-list)
	  (map item))
	first-list))
   (3 (function first-list second-list)
      (with-funcallable (map function)
	(do ((p first-list (cdr p))
	     (q second-list (cdr q)))
	    ((or (endp p) (endp q)))
	  (map (car p) (car q)))
	first-list))
   (t (function &rest lists)
      (declare (dynamic-extent lists))
      (let ((first-list (car lists)))
	(unless (some 'null lists)
	  (prog ()
	   loop
	    (apply (lambda (function &rest apply-cars)
		     (declare (dynamic-extent apply-cars))
		     (do ((p apply-cars (cdr p)))
			 ((endp p))
		       (setf (car p) (caar p)))
		     (apply function apply-cars))
		   function lists)
	    (do ((p lists (cdr p)))
		((endp p) (go loop))
	      (let ((x (cdar p)))
		(unless x (return))
		(setf (car p) x)))))
	first-list))))


(defun nbutlast (list &optional (n 1))
  (let ((start-right (nthcdr n list)))
    (if (endp start-right)
	nil
      (do ((right (cdr start-right) (cdr right))
	   (left list (cdr left)))
	  ((endp right)
	   (setf (cdr left) nil)
	   list)))))

(defun butlast (list &optional (n 1))
  (ldiff list (last list n)))

(defun tailp (object list)
  ;; From the hyperspec..
  (do ((list list (cdr list)))
      ((atom list) (eql list object))
    (if (eql object list)
	(return t))))

(defun ldiff (list object)
  ;; From the hyperspec..
  (do ((list list (cdr list))
       (r '() (cons (car list) r)))
      ((atom list)
       (if (eql list object) (nreverse r) (nreconc r list)))
    (when (eql object list)
      (return (nreverse r)))))

(defun nreconc (list tail)
  (if (null list)
      tail
    (prog1 (nreverse list)
      (setf (cdr list) tail))))

(defun set-difference (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  "Return the elements of list-1 that do not appear in list-2."
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (remove-if (lambda (list-1-element)
		 (member (funcall key list-1-element) list-2 :key key :test test))
	       list-1)))

(defun nset-difference (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  "Return the elements of list-1 that do not appear in list-2."
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (delete-if (lambda (list-1-element)
		 (member (funcall key list-1-element) list-2 :key key :test test))
	       list-1)))

(defun intersection (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  "intersection returns a list that contains every element that occurs in both list-1 and list-2."
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (remove-if (lambda (list-1-element)
		 (not (member (funcall key list-1-element) list-2 :key key :test test)))
	       list-1)))

(defun nintersection (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  "intersection returns a list that contains every element that occurs in both list-1 and list-2."
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (delete-if (lambda (list-1-element)
		 (not (member (funcall key list-1-element) list-2 :key key :test test)))
	       list-1)))

(defun union (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  (remove-duplicates (append list-1 list-2)
		     :key key
		     :test (if test-not
			       (complement test-not)
			     test)))

(defun nunion (list-1 list-2 &key (key 'identity) (test 'eql) test-not)
  (delete-duplicates (nconc list-1 list-2)
		     :key key
		     :test (if test-not
			       (complement test-not)
			     test)))

  
  
