;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      hash-tables.lisp
;;;; Description:   Hash-tables implementation.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Feb 19 19:09:05 2001
;;;;                
;;;; $Id: hash-tables.lisp,v 1.4 2004/10/11 13:52:37 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------


(require :muerte/basic-macros)
(require :muerte/basic-functions)
(require :muerte/typep)
(require :muerte/defstruct)
(require :muerte/integers)
(require :muerte/equalp)
(require :muerte/arrays)
(require :muerte/characters)
(require :muerte/lists)
(provide :muerte/hash-tables)

(in-package muerte)

(defstruct (hash-table (:constructor make-hash-table-object))
  test
  bucket
  sxhash)

(defun make-hash-table (&key (test 'eql) (size 47) rehash-size rehash-threshold)
  (declare (ignore rehash-size rehash-threshold))
  (multiple-value-bind (test sxhash)
      (ecase (if (typep test 'compiled-function)
		 (funobj-name test)
	       test)
	(eq (values #'eq #'sxhash-eq))
	(eql (values #'eql #'sxhash-eql))
	(equal (values #'equal #'sxhash)))
    (make-hash-table-object
     :test test
     :bucket (make-array (* 2 size) :initial-element '#.movitz::+undefined-hash-key+)
     :sxhash sxhash)))

(defun hash-table-count (hash-table)
  (do* ((bucket (hash-table-bucket hash-table))
	(length (length bucket))
	(count 0)
	(i 0 (+ i 2)))
      ((>= i length) count)
    (unless (eq (svref bucket i) '#.movitz::+undefined-hash-key+)
      (incf count))))

(defun hash-table-iterator (bucket index)
  (when index
    (do ((length (array-dimension bucket 0)))
	((>= index length) nil)
      (unless (eq (svref bucket index)
		  '#.movitz::+undefined-hash-key+)
	(return (+ index 2)))
      (incf index 2))))

(defmacro with-hash-table-iterator ((name hash-table) &body declarations-and-body)
  (let ((bucket-var (gensym "bucket-var-"))
	(bucket-index-var (gensym "bucket-index-var-")))
    `(let* ((,bucket-var (hash-table-bucket ,hash-table))
	    (,bucket-index-var 0))
       (macrolet ((,name ()
		    `(when (setq ,',bucket-index-var
			     (hash-table-iterator ,',bucket-var ,',bucket-index-var))
		       (values t
			       (svref ,',bucket-var (- ,',bucket-index-var 2))
			       (svref ,',bucket-var (- ,',bucket-index-var 1))))))
	 ,@declarations-and-body))))

(defun sxhash-subvector (vector start end &optional (limit 8))
  (let ((result 0))
    (dotimes (i (min limit (- end start)))
      (incf result result)
      (incf result
	    (let* ((element (aref vector (+ start i)))
		   (element-hash (sxhash-limited element (- limit 1))))
	      (if (evenp i)
		  element-hash
		(* 7 element-hash)))))
    (ldb (byte 16 0)
	 (+ (* #x10ad (- end start))
	    result))))

(defun sxhash-limited (object limit)
  (if (not (plusp limit))
      0
    (typecase object
      (cons
       (logxor (sxhash-limited (car object) (- limit 2))
	       (sxhash-limited (cdr object) (1- limit))))
      (character
       (char-code (char-upcase object)))
      (vector
       (sxhash-subvector object 0 (length object) limit))
      (t (sxhash-eq object)))))

(defun sxhash (object)
  "Returns a hash code for object."
  (sxhash-limited object 8))

(defun sxhash-eq (object)
  (typecase object
    (null 0)
    (symbol
     (movitz-accessor-u16 object movitz-symbol hash-key))
    (t (with-inline-assembly (:returns :eax)
	 (:compile-form (:result-mode :eax) object)
	 (:andl #.(cl:logxor #xffffffff movitz::+movitz-fixnum-zmask+) :eax)))))

(defun sxhash-eql (object)
  (sxhash-eq object))
       
(defun gethash (key hash-table &optional default)
  (let* ((test (hash-table-test hash-table))
	 (bucket (hash-table-bucket hash-table))
	 (bucket-length (length bucket))
	 (start-i2 (rem (ash (funcall (hash-table-sxhash hash-table) key) 1) bucket-length))
	 (i2 start-i2))
    (do () (nil)
      (let ((k (svref%unsafe bucket i2)))
	(cond
	 ((eq '#.movitz::+undefined-hash-key+ k)
	  (return (values default nil)))
	 ((funcall test key k)
	  (return (values (svref%unsafe bucket (1+ i2)) t)))))
      (when (>= (incf i2 2) bucket-length)
	(setf i2 0)))))

(defun gethash-singleton (hash-table key0)
  "Assuming hash-tables keys are lists whose elements compare by EQ,
look up key0 as if it was in a singleton list (key0)."
  (let* ((bucket (hash-table-bucket hash-table))
	 (bucket-length (array-dimension bucket 0))
	 (start-i2 (rem (ash (sxhash-eq key0) 1) bucket-length))
	 (i2 start-i2))
    (do () (nil)
      (let ((k (svref%unsafe bucket i2)))
	(cond
	 ((eq '#.movitz::+undefined-hash-key+ k)
	  (return nil))
	 ((eq key0 (car k))
	  (return (svref%unsafe bucket (1+ i2))))))
      (when (>= (incf i2 2) bucket-length)
	(setf i2 0)))))

(defun gethash-doubleton (hash-table key0 key1)
  "Assuming hash-tables keys are lists whose elements compare by EQ,
look up key0 and key1 as if they were in a doubleton list (key0 key1)."
  (let* ((bucket (hash-table-bucket hash-table))
	 (bucket-length (array-dimension bucket 0))
	 (start-i2 (rem (ash (logxor (sxhash-eq key0) (sxhash-eq key1)) 1)
			bucket-length))
	 (i2 start-i2))
    (do () (nil)
      (let ((k (svref%unsafe bucket i2)))
	(cond
	 ((eq '#.movitz::+undefined-hash-key+ k)
	  (return nil))
	 ((and (eq key0 (car k)) (eq key1 (cadr k)))
	  (return (svref%unsafe bucket (1+ i2))))))
      (when (>= (incf i2 2) bucket-length)
	(setf i2 0)))))


(defun (setf gethash) (value key hash-table &optional (default nil))
  (declare (ignore default))
  (do* ((test (hash-table-test hash-table))
	(bucket (hash-table-bucket hash-table))
	(bucket-length (length bucket))
	(index2 (rem (ash (funcall (hash-table-sxhash hash-table) key) 1) bucket-length))
	(c 2 (+ c 2)))
      ((>= c bucket-length)
       (error "Hash-table bucket is full, needs rehashing, which isn't implemented."))
    (let ((k (svref%unsafe bucket index2)))
      (when (or (eq '#.movitz::+undefined-hash-key+ k)
		(funcall test k key))
	(return (setf (svref%unsafe bucket index2) key
		      (svref%unsafe bucket (1+ index2)) value))))
    (when (>= (incf index2 2) bucket-length)
      (setf index2 0))))

(defun gethash-string (key-string start end hash-table &optional default (key 'identity))
  (let ((bucket (hash-table-bucket hash-table)))
    (with-subvector-accessor (key-string-ref key-string start end)
      (do* ((bucket-length (length bucket))
	    (index2 (rem (* 2 (sxhash-subvector key-string start end 8))
			 bucket-length)
		    (rem (+ 2 index2) bucket-length)))
	  ((eq '#.movitz::+undefined-hash-key+
	       (svref%unsafe bucket index2))
	   (values default nil))
	(when ;; (string= key-string (svref bucket index2) :start1 start :end1 end))
	    (let* ((bs (svref bucket index2))
		   (bs-length (length bs)))
	      (and (= bs-length (- end start))
		   (do ((bs-index 0 (1+ bs-index))
			(key-index start (1+ key-index)))
		       ((>= key-index end) t)
		     (unless (and (< bs-index bs-length)
				  (char= (funcall key (key-string-ref key-index))
					 (schar bs bs-index)))
		       (return nil)))))
	  (return (values (svref%unsafe bucket (1+ index2)) t)))))))

(defun remhash (key hash-table)
  (do* ((bucket (hash-table-bucket hash-table))
	(bucket-length (length bucket))
	(index2 (rem (* 2 (sxhash key)) bucket-length)
		(rem (+ 2 index2) bucket-length))
	(i 0 (+ i 2)))
      ((>= i bucket-length) nil)
    (let ((x (svref bucket index2)))
      (when (or (eq '#.movitz::+undefined-hash-key+ x)
		(funcall (hash-table-test hash-table) x key))
	(setf (svref bucket index2) '#.movitz::+undefined-hash-key+)
	;; Now we must rehash any entries that might have been
	;; displaced by the one we have now removed.
	(do ((i (rem (+ index2 2) bucket-length)
		(rem (+ i 2) bucket-length)))
	    ((= i index2))
	  (let ((k (svref bucket i)))
	    (when (eq x '#.movitz::+undefined-hash-key+)
	      (return))
	    (let ((v (svref bucket (1+ i))))
	      (setf (svref bucket i) '#.movitz::+undefined-hash-key+) ; remove
	      (setf (gethash k hash-table) v)))) ; insert (hopefully this is safe..)
	(return t)))))

(defun clrhash (hash-table)
  (do* ((bucket (hash-table-bucket hash-table))
	(bucket-length (length bucket))
	(i 0 (+ i 2)))
      ((>= i bucket-length) hash-table)
    (setf (svref bucket i) '#.movitz::+undefined-hash-key+)))

(defun maphash (function hash-table)
  (with-hash-table-iterator (get-next-entry hash-table)
    (do () (nil)
      (multiple-value-bind (entry-p key value)
	  (get-next-entry)
	(if (not entry-p)
	    (return nil)
	  (funcall function key value))))))
	
