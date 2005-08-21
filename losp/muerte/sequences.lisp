;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      sequences.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 11 14:19:23 2001
;;;;                
;;;; $Id: sequences.lisp,v 1.22 2005/08/21 17:56:44 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/sequences)
  
(in-package muerte)

(deftype index (&optional (step 1))
  `(integer 0 ,(- #x1fffffff step)))

(defun sequencep (x)
  (or (typep x 'vector)
      (typep x 'cons)))

(defmacro sequence-dispatch (sequence-var (type0 &body forms0) (type1 &body forms1))
  (cond
   ((and (eq 'list type0) (eq 'vector type1))
    `(if (typep ,sequence-var 'list)
	 (progn ,@forms0)
       (progn (check-type ,sequence-var vector)
	      ,@forms1)))
   ((and (eq 'vector type0) (eq 'list type1))
    `(if (not (typep ,sequence-var 'list))
	 (progn (check-type ,sequence-var vector)
		,@forms0)
       (progn ,@forms1)))
   (t (error "sequence-dispatch only understands list and vector types, not ~W and ~W."
	     type0 type1))))

(defun sequence-double-dispatch-error (seq0 seq1)
  (error "The type-set (~A, ~A) has not been implemented in this sequence-double-dispatch."
	 (type-of seq0)
	 (type-of seq1)))

(defmacro sequence-double-dispatch ((seq0 seq1) &rest clauses)
  `(case (logior (if (typep ,seq0 'list) 2 0)
		 (if (typep ,seq1 'list) 1 0))
     ,@(loop for ((type0 type1) . forms) in clauses
	   as index = (logior (ecase type0 (list 2) (vector 0))
			      (ecase type1 (list 1) (vector 0)))
	   collect
	     `(,index ,@forms))
     (t (sequence-double-dispatch-error ,seq0 ,seq1))))

(defun length (sequence)
  (etypecase sequence
    (list
     (do ((x sequence (cdr x))
	  (length 0 (1+ length)))
	 ((null x) length)
       (declare (index length))))
    (indirect-vector
     (memref sequence (movitz-type-slot-offset 'movitz-basic-vector 'data)
	     :index 2))
    ((simple-array * 1)
     (macrolet
	 ((do-it ()
	    `(with-inline-assembly (:returns :eax)
	       (:compile-form (:result-mode :ebx) sequence)
	       (:movl (:ebx (:offset movitz-basic-vector num-elements))
		      :eax)
	       (:testl ,(logxor #xffffffff (1- (expt 2 14))) :eax)
	       (:jnz 'basic-vector-length-ok)
	       (:movzxw (:ebx (:offset movitz-basic-vector fill-pointer))
			:eax)
	      basic-vector-length-ok)))
       (do-it)))))

(defun length%list (sequence)
  (do ((length 0 (1+ length))
       (x sequence (cdr x)))
      ((null x) length)))

(defun elt (sequence index)
  (sequence-dispatch sequence
    (vector (aref sequence index))
    (list (nth index sequence))))

(defun (setf elt) (value sequence index)
  (sequence-dispatch sequence
    (vector (setf (aref sequence index) value))
    (list (setf (nth index sequence) value))))

(defun reduce (function sequence &key (key 'identity) from-end
				      (start 0) (end (length sequence))
				      (initial-value nil initial-value-p))
  (numargs-case
   (2 (function sequence)
      (with-funcallable (funcall-function function)
	(sequence-dispatch sequence
	  (list
	   (cond
	    ((null sequence)
	     (funcall-function))
	    ((null (cdr sequence))
	     (car sequence))
	    (t (do* ((list sequence)
		     (result (funcall-function (pop list) (pop list))
			     (funcall-function result (pop list))))
		   ((endp list)
		    result)))))
	  (vector
	   (let ((end (length sequence)))
	     (case end
	       (0 (funcall-function))
	       (1 (aref sequence 0))
	       (t (with-subvector-accessor (sequence-ref sequence 0 end)
		    (do* ((index 0)
			  (result (funcall-function (sequence-ref (prog1 index (incf index)))
						    (sequence-ref (prog1 index (incf index))))
				  (funcall-function result (sequence-ref (prog1 index (incf index))))))
			((= index end) result))))))))))
   (t (function sequence &key (key 'identity) from-end
		(start 0) (end (length sequence))
		(initial-value nil initial-value-p))
      (when from-end
	(error "REDUCE from-end is not implemented."))
      (with-funcallable (funcall-function function)
	(with-funcallable (key)
	  (case (- end start)
	    (0 (if initial-value-p
		   initial-value
		 (funcall-function)))
	    (1 (if initial-value-p
		   (funcall-function initial-value (key (elt sequence start)))
		 (key (elt sequence start))))
	    (t (sequence-dispatch sequence
		 (list
		  (do* ((counter (1+ start) (1+ counter))
			(list (nthcdr start sequence))
			(result (funcall-function (if initial-value-p
						      initial-value
						    (key (pop list)))
						  (key (pop list)))
				(funcall-function result (key (pop list)))))
		      ((or (null list)
			   (= end counter))
		       result)))
		 (vector
		  (with-subvector-accessor (sequence-ref sequence start end)
		    (do* ((index start)
			  (result (funcall-function (if initial-value-p
							initial-value
						      (key (sequence-ref (prog1 index (incf index)))))
						    (key (sequence-ref (prog1 index (incf index)))))
				  (funcall-function result (sequence-ref (prog1 index (incf index))))))
			((= index end) result))))))))))))

(defun subseq (sequence start &optional end)
  (sequence-dispatch sequence
    (vector
     (unless end
       (setf end (length sequence)))
     (with-subvector-accessor (old-ref sequence start end)
       (let ((new-vector (make-array (- end start) :element-type (array-element-type sequence))))
	 (replace new-vector sequence :start2 start :end2 end)
	 #+ignore (with-subvector-accessor (new-ref new-vector)
		    (do ((i start (1+ i))
			 (j 0 (1+ j)))
			((>= i end) new-vector)
		      (setf (new-ref j) (old-ref i))))
	 )))
    (list
     (let ((list-start (nthcdr start sequence)))
       (cond
	((not end)
	 (copy-list list-start))
	((> start end)
	 (error "Start ~A is greater than end ~A." start end))
	((endp list-start) nil)
	((= start end) nil)
	(t (do* ((p (cdr list-start) (cdr p))
		 (i (1+ start) (1+ i))
		 (head (cons (car list-start) nil))
		 (tail head))
	       ((or (endp p) (>= i end)) head)
	     (setf (cdr tail) (cons (car p) nil)
		   tail (cdr tail)))))))))

(defsetf subseq (sequence start &optional (end nil end-p)) (new-sequence)
  `(progn (replace ,sequence ,new-sequence :start1 ,start
		   ,@(when end-p `(:end1 ,end)))
	  ,new-sequence))

(defun copy-seq (sequence)
  (subseq sequence 0))

(defun position (item sequence &key from-end (test #'eql) test-not (start 0) end (key 'identity))
  (numargs-case
   (2 (item sequence)
      (sequence-dispatch sequence
	(vector
	 (with-subvector-accessor (sequence-ref sequence)
	   (do ((end (length sequence))
		(i 0 (1+ i)))
	       ((>= i end))
	     (when (eql (sequence-ref i) item)
	       (return i)))))
	(list
	 (do ((i 0 (1+ i)))
	     ((null sequence) nil)
	   (when (eql (pop sequence) item)
	     (return i))))))
   (t (item sequence &key from-end (test #'eql) test-not (start 0) end  (key 'identity))
      (with-funcallable (key)
	(with-funcallable (test)
	  (sequence-dispatch sequence
	    (vector
	     (unless end
	       (setf end (length sequence)))
	     (with-subvector-accessor (sequence-ref sequence start end)
	       (cond
		((not from-end)
		 (do ((i start (1+ i)))
		     ((>= i end))
		   (when (test (key (sequence-ref i)) item)
		     (return i))))
		(t (do ((i (1- end) (1- i)))
		       ((< i start))
		     (when (test (key (sequence-ref i)) item)
		       (return i)))))))
	    (list
	     (cond
	      ((not end)
	       (do ((p (nthcdr start sequence))
		    (i start (1+ i)))
		   ((null p) nil)
		 (when (test (key (pop p)) item)
		   (return (if (not from-end)
			       i
			     (let ((next-i (position item p :key key :from-end t
						     :test test :test-not test-not)))
			       (if next-i (+ i 1 next-i ) i)))))))
	      (t (do ((p (nthcdr start sequence))
		      (i start (1+ i)))
		     ((or (null p) (>= i end)) nil)
		   (when (test (key (pop p)) item)
		     (return (if (not from-end) i
			       (let ((next-i (position item p :end (- end 1 i) :from-end t
						       :key key :test test :test-not test-not)))
				 (if next-i (+ i 1 next-i ) i)))))))))))))))

(defun position-if (predicate sequence &key (start 0) end (key 'identity) from-end)
  (numargs-case
   (2 (predicate sequence)
      (with-funcallable (predicate)
	(sequence-dispatch sequence
	  (vector
	   (with-subvector-accessor (sequence-ref sequence)
	     (do ((end (length sequence))
		  (i 0 (1+ i)))
		 ((>= i end))
	       (when (predicate (sequence-ref i))
		 (return i)))))
	  (list
	   (do ((p sequence)
		(i 0 (1+ i)))
	       ((null p))
	     (when (predicate (pop p))
	       (return i)))))))
   (t (predicate sequence &key (start 0) end (key 'identity) from-end)
      (with-funcallable (predicate)
	(with-funcallable (key)
	  (sequence-dispatch sequence
	    (vector
	     (setf end (or end (length sequence)))
	     (with-subvector-accessor (sequence-ref sequence start end)
	       (cond
		((not from-end)
		 (do ((i start (1+ i)))
		     ((>= i end))
		   (when (predicate (key (sequence-ref i)))
		     (return i))))
		(t (do ((i (1- end) (1- i)))
		       ((< i start))
		     (when (predicate (key (sequence-ref i)))
		       (return i)))))))
	    (list
	     (cond
	      (end
	       (do ((p (nthcdr start sequence))
		    (i start (1+ i)))
		   ((or (>= i end) (null p)))
		 (when (predicate (key (pop p)))
		   (return (if (not from-end) i
			     (let ((next-i (position-if predicate p :key key
							:from-end t :end (- end i 1))))
			       (if next-i (+ i 1 next-i) i)))))))
	      (t (do ((p (nthcdr start sequence))
		      (i start (1+ i)))
		     ((null p))
		   (when (predicate (key (pop p)))
		     (return (if (not from-end) i
			       (let ((next-i (position-if predicate p :key key :from-end t)))
				 (if next-i (+ i 1 next-i) i)))))))))))))))

(defun position-if-not (predicate sequence &rest key-args)
  (declare (dynamic-extent key-args))
  (apply #'position-if (complement predicate) sequence key-args))

(defun nreverse (sequence)
  (sequence-dispatch sequence
    (list
     (do ((prev-cons nil current-cons)
	  (next-cons (cdr sequence) (cdr next-cons))
	  (current-cons sequence next-cons))
	 ((null current-cons) prev-cons)
       (setf (cdr current-cons) prev-cons)))
    (vector
     (with-subvector-accessor (sequence-ref sequence)
       (do ((i 0 (1+ i))
	    (j (1- (length sequence)) (1- j)))
	   ((<= j i))
	 (let ((x (sequence-ref i)))
	   (setf (sequence-ref i) (sequence-ref j)
		 (sequence-ref j) x))))
     sequence)))

(defun reverse (sequence)
  (sequence-dispatch sequence
    (list
     (let ((result nil))
       (dolist (x sequence)
	 (push x result))
       result))
    (vector
     (nreverse (copy-seq sequence)))))

(defun mismatch-eql-identity (sequence-1 sequence-2 start1 start2 end1 end2)
  (sequence-dispatch sequence-1
    (vector
     (unless end1 (setf end1 (length sequence-1)))
     (with-subvector-accessor (seq1-ref sequence-1 start1 end1)
       (sequence-dispatch sequence-2
	 (vector
	  (unless end2 (setf end2 (length sequence-2)))
	  (with-subvector-accessor (seq2-ref sequence-2 start2 end2)
	    (macrolet ((test-return (index1 index2)
			 `(unless (eql (seq1-ref ,index1) (seq2-ref ,index2))
			    (return ,index1))))
	      (let ((length1 (- end1 start1))
		    (length2 (- end2 start2)))
		(cond
		 ((= length1 length2)
		  (do* ((i start1 (1+ i))
			(j start2 (1+ j)))
		      ((>= i end1) nil)
		    (declare (type (unsigned-byte 16) i j start1 end1 start2 end2))
		    (test-return i j)))
		 ((< length1 length2)
		  (do* ((i start1 (1+ i))
			(j start2 (1+ j)))
		      ((>= i end1) end1)
		    (declare ((unsigned-byte 16) i j start1 end1 start2 end2))
		    (test-return i j)))
		 ((> length1 length2)
		  (do* ((i start1 (1+ i))
			(j start2 (1+ j)))
		      ((>= j end2) i)
		    (declare ((unsigned-byte 16) i j start1 end1 start2 end2))
		    (test-return i j))))))))
	 (list
	  (let ((length1 (- end1 start1))
		(start-cons2 (nthcdr start2 sequence-2)))
	    (cond
	     ((and (zerop length1) (null start-cons2))
	      (if (and end2 (> end2 start2)) start1 nil))
	     ((not end2)
	      (do ((i1 start1 (1+ i1))
		   (p2 start-cons2 (cdr p2)))
		  ((>= i1 end1) (if (null p2) nil i1))
		(unless (and p2 (eql (seq1-ref i1) (car p2)))
		  (return i1))))
	     ((< length1 (- end2 start2))
	      (do ((i1 start1 (1+ i1))
		   (p2 start-cons2 (cdr p2)))
		  ((>= i1 end1) end1)
		(unless (eql (seq1-ref i1) (car p2))
		  (return i1))))
	     ((> length1 (- end2 start2))
	      (do ((i1 start1 (1+ i1))
		   (p2 start-cons2 (cdr p2)))
		  ((null p2) end1)
		(unless (eql (seq1-ref i1) (car p2))
		  (return i1))))
	     (t (do ((i1 start1 (1+ i1))
		     (p2 start-cons2 (cdr p2)))
		    ((null p2) nil)
		  (unless (eql (seq1-ref i1) (car p2))
		    (return i1))))))))))
    (list
     (sequence-dispatch sequence-2
       (vector
	(let ((mismatch-2 (mismatch-eql-identity sequence-2 sequence-1 start2 start1 end2 end1)))
	  (if (not mismatch-2)
	      nil
	    (+ start1 (- mismatch-2 start2)))))
       (list
	(let ((start-cons1 (nthcdr start1 sequence-1))
	      (start-cons2 (nthcdr start2 sequence-2)))
	  (assert (and start-cons1 start-cons2) (start1 start2) "Illegal bounding indexes.")
	  (cond
	   ((and (not end1) (not end2))
	    (do ((p1 start-cons1 (cdr p1))
		 (p2 start-cons2 (cdr p2))
		 (i1 start1 (1+ i1)))
		((null p1) (if (null p2) nil i1))
	      (unless (and p2 (eql (car p1) (car p2)))
		(return i1))))
	   (t (do ((p1 start-cons1 (cdr p1))
		   (p2 start-cons2 (cdr p2))
		   (i1 start1 (1+ i1))
		   (i2 start2 (1+ i2)))
		  ((if end1 (>= i1 end1) (null p1))
		   (if (if end2 (>= i2 end2) (null p2)) nil i1))
		(unless (and (or (not end2) (< i1 end2))
			     (eql (car p1) (car p2)))
		  (return i1)))))))))))

(define-compiler-macro mismatch (&whole form sequence-1 sequence-2
				 &key (start1 0) (start2 0) end1 end2
				      (test 'eql test-p) (key 'identity key-p) from-end)
  (declare (ignore key test))
  (cond
   ((and (not test-p) (not key-p))
    (assert (not from-end) ()
      "Mismatch :from-end not implemented.")
    `(mismatch-eql-identity ,sequence-1 ,sequence-2 ,start1 ,start2 ,end1 ,end2))
   (t form)))

(defun mismatch (sequence-1 sequence-2 &key (start1 0) (start2 0) end1 end2
					    (test 'eql) (key 'identity) from-end)
  (numargs-case
   (2 (s1 s2)
      (mismatch-eql-identity s1 s2 0 0 nil nil))
   (t (sequence-1 sequence-2 &key (start1 0) (start2 0) end1 end2
		  (test 'eql) (key 'identity) from-end)
      (assert (not from-end) ()
	"Mismatch :from-end not implemented.")
      (with-funcallable (test)
	(with-funcallable (key)
	  (sequence-dispatch sequence-1
	    (vector
	     (unless end1 (setf end1 (length sequence-1)))
	     (with-subvector-accessor (sequence-1-ref sequence-1 start1 end1)
	       (sequence-dispatch sequence-2
		 (vector
		  (unless end2 (setf end2 (length sequence-2)))
		  (with-subvector-accessor (sequence-2-ref sequence-2 start2 end2)
		    (macrolet ((test-return (index1 index2)
				 `(unless (test (key (sequence-1-ref ,index1))
						(key (sequence-2-ref ,index2)))
				    (return-from mismatch ,index1))))
		      (let ((length1 (- end1 start1))
			    (length2 (- end2 start2)))
			(cond
			 ((< length1 length2)
			  (dotimes (i length1)
			    (declare ((unsigned-byte 16) i start1 start2))
			    (test-return (+ start1 i) (+ start2 i)))
			  end1)
			 ((> length1 length2)
			  (dotimes (i length2)
			    (declare ((unsigned-byte 16) i start1 start2))
			    (test-return (+ start1 i) (+ start2 i)))
			  (+ start1 length2))
			 (t (dotimes (i length1)
			      (declare ((unsigned-byte 16) i start1 start2))
			      (test-return (+ start1 i) (+ start2 i)))
			    nil))))))
		 (list
		  (let ((length1 (- end1 start1))
			(start-cons2 (nthcdr start2 sequence-2)))
		    (cond
		     ((and (zerop length1) (null start-cons2))
		      (if (and end2 (> end2 start2)) start1 nil))
		     ((not end2)
		      (do ((i1 start1 (1+ i1))
			   (p2 start-cons2 (cdr p2)))
			  ((>= i1 end1) (if (null p2) nil i1))
			(unless (and p2 (test (key (sequence-1-ref i1)) (key (car p2))))
			  (return-from mismatch i1))))
		     ((< length1 (- end2 start2))
		      (do ((i1 start1 (1+ i1))
			   (p2 start-cons2 (cdr p2)))
			  ((>= i1 end1) end1)
			(unless (test (key (sequence-1-ref i1)) (key (car p2)))
			  (return-from mismatch i1))))
		     ((> length1 (- end2 start2))
		      (do ((i1 start1 (1+ i1))
			   (p2 start-cons2 (cdr p2)))
			  ((null p2) end1)
			(unless (test (key (sequence-1-ref i1)) (key (car p2)))
			  (return-from mismatch i1))))
		     (t (do ((i1 start1 (1+ i1))
			     (p2 start-cons2 (cdr p2)))
			    ((null p2) nil)
			  (unless (test (key (sequence-1-ref i1)) (key (car p2)))
			    (return-from mismatch i1))))))))))
	    (list
	     (sequence-dispatch sequence-2
	       (vector
		(let ((mismatch-2 (mismatch sequence-2 sequence-1 :from-end from-end :test test :key key
					    :start1 start2 :end1 end2 :start2 start1 :end2 end1)))
		  (if (not mismatch-2)
		      nil
		    (+ start1 (- mismatch-2 start2)))))
	       (list
		(let ((start-cons1 (nthcdr start1 sequence-1))
		      (start-cons2 (nthcdr start2 sequence-2)))
		  (assert (and start-cons1 start-cons2) (start1 start2) "Illegal bounding indexes.")
		  (cond
		   ((and (not end1) (not end2))
		    (do ((p1 start-cons1 (cdr p1))
			 (p2 start-cons2 (cdr p2))
			 (i1 start1 (1+ i1)))
			((null p1) (if (null p2) nil i1))
		      (unless (and p2 (test (key (car p1)) (key (car p2))))
			(return i1))))
		   (t (do ((p1 start-cons1 (cdr p1))
			   (p2 start-cons2 (cdr p2))
			   (i1 start1 (1+ i1))
			   (i2 start2 (1+ i2)))
			  ((if end1 (>= i1 end1) (null p1))
			   (if (if end2 (>= i2 end2) (null p2)) nil i1))
			(unless p2
			  (if end2
			      (error "Illegal end2 bounding index.")
			    (return i1)))
			(unless (and (or (not end2) (< i1 end2))
				     (test (key (car p1)) (key (car p2))))
			  (return i1)))))))))))))))

(defun map-into (result-sequence function first-sequence &rest more-sequences)
  (declare (dynamic-extent more-sequences))
  (assert (null more-sequences) ()
    "MAP-INTO not implemented.")
  (with-funcallable (map function)
    (sequence-double-dispatch (result-sequence first-sequence)
      ((vector vector)
       (let ((length (min (length result-sequence)
			  (length first-sequence))))
	 (with-subvector-accessor (result-ref result-sequence 0 length)
	   (with-subvector-accessor (first-sequence-ref first-sequence 0 length)
	     (dotimes (i length result-sequence)
	       (setf (result-ref i)
		 (map (first-sequence-ref i))))))))
      ((list list)
       (do ((p result-sequence (cdr p))
	    (q first-sequence (cdr q)))
	   ((or (null p) (null q))
	    result-sequence)
	 (setf (car p) (map (car q)))))
      ((vector list)
       (with-subvector-accessor (result-ref result-sequence)
	 (do ((end (length result-sequence))
	      (i 0 (1+ i))
	      (p first-sequence (cdr p)))
	     ((or (endp p) (>= i end)) result-sequence)
	   (setf (result-ref i) (map (car p))))))
      ((list vector)
       (with-subvector-accessor (first-ref first-sequence)
	 (do ((end (length first-sequence))
	      (i 0 (1+ i))
	      (p result-sequence (cdr p)))
	     ((or (endp p) (>= i end)) result-sequence)
	   (setf (car p) (map (first-ref i)))))))))

(defun map-for-nil (function first-sequence &rest more-sequences)
  (numargs-case
   (2 (function first-sequence)
      (with-funcallable (mapf function)
	(sequence-dispatch first-sequence
	  (list
	   (dolist (x first-sequence)
	     (mapf x)))
	  (vector
	   (with-subvector-accessor (sequence-ref first-sequence)
	     (dotimes (i (length first-sequence))
	       (mapf (sequence-ref i))))))))
   (3 (function first-sequence second-sequence)
      (with-funcallable (mapf function)
	(sequence-double-dispatch (first-sequence second-sequence)
	  ((list list)
	   (do ((p first-sequence (cdr p))
		(q second-sequence (cdr q)))
	       ((or (endp p) (endp q)))
	     (mapf (car p) (car q))))
	  ((vector vector)
	   (with-subvector-accessor (first-sequence-ref first-sequence)
	     (with-subvector-accessor (second-sequence-ref second-sequence)
	       (do ((len1 (length first-sequence))
		    (len2 (length second-sequence))
		    (i 0 (1+ i))
		    (j 0 (1+ j)))
		   ((or (>= i len1)
			(>= j len2)))
		 (mapf (first-sequence-ref i) (second-sequence-ref j))))))
	  )))
   (t (function first-sequence &rest more-sequences)
      (declare (ignore function first-sequence more-sequences))
      (error "MAP not implemented."))))

(defun map-for-list (function first-sequence &rest more-sequences)
  (numargs-case
   (2 (function first-sequence)
      (with-funcallable (mapf function)
	(sequence-dispatch first-sequence
	  (list
	   (mapcar function first-sequence))
	  (vector
	   (with-subvector-accessor (sequence-ref first-sequence)
	     (let ((result nil))
	       (dotimes (i (length first-sequence))
		 (push (mapf (sequence-ref i))
		       result))
	       (nreverse result)))))))
   (3 (function first-sequence second-sequence)
      (sequence-double-dispatch (first-sequence second-sequence)
	((list list)
	 (mapcar function first-sequence second-sequence))
	((vector vector)
	 (with-funcallable (mapf function)
	   (with-subvector-accessor (first-sequence-ref first-sequence)
	     (with-subvector-accessor (second-sequence-ref second-sequence)
	       (do ((result nil)
		    (len1 (length first-sequence))
		    (len2 (length second-sequence))
		    (i 0 (1+ i))
		    (j 0 (1+ j)))
		   ((or (>= i len1)
			(>= j len2))
		    (nreverse result))
		 (push (mapf (first-sequence-ref i) (second-sequence-ref j))
		       result))))))
	((list vector)
	 (with-funcallable (mapf function)
	   (with-subvector-accessor (second-sequence-ref second-sequence)
	     (do ((result nil)
		  (len2 (length second-sequence))
		  (p first-sequence (cdr p))
		  (j 0 (1+ j)))
		 ((or (endp p) (>= j len2))
		  (nreverse result))
	       (push (mapf (car p) (second-sequence-ref j))
		     result)))))
	((vector list)
	 (with-funcallable (mapf function)
	   (with-subvector-accessor (first-sequence-ref first-sequence)
	     (do ((result nil)
		  (len1 (length first-sequence))
		  (p second-sequence (cdr p))
		  (j 0 (1+ j)))
		 ((or (endp p) (>= j len1))
		  (nreverse result))
	       (push (mapf (first-sequence-ref j) (car p))
		     result)))))))
   (t (function first-sequence &rest more-sequences)
      (declare (dynamic-extent more-sequences)
	       (ignore function first-sequence more-sequences))
      (error "MAP not implemented."))))

(defun map-for-string (function first-sequence &rest more-sequences)
  (numargs-case
   (2 (function first-sequence)
      (with-funcallable (mapf function)
	(let ((result (make-string (length first-sequence))))
	  (sequence-dispatch first-sequence
	    (vector
	     (do ((i 0 (1+ i)))
		 ((>= i (length result)) result)
	       (setf (char result i) (mapf (aref first-sequence i)))))
	    (list
	     (do ((i 0 (1+ i)))
		 ((>= i (length result)) result)
	       (setf (char result i) (mapf (pop first-sequence)))))))))
   (t (function first-sequence &rest more-sequences)
      (declare (ignore function first-sequence more-sequences))
      (error "MAP not implemented."))))


(defun map (result-type function first-sequence &rest more-sequences)
  "=> result"
  (declare (dynamic-extent more-sequences))
  (cond
   ((null result-type)
    (apply 'map-for-nil function first-sequence more-sequences))
   ((eq 'list result-type)
    (apply 'map-for-list function first-sequence more-sequences))
   ((eq 'string result-type)
    (apply 'map-for-string function first-sequence more-sequences))
   (t (error "MAP not implemented."))))

(defun fill (sequence item &key (start 0) end)
  "=> sequence"
  (etypecase sequence
    (list
     (do ((p (nthcdr start sequence) (cdr p))
	  (i start (1+ i)))
	 ((or (null p) (and end (>= i end))))
       (setf (car p) item)))
    ((simple-array (unsigned-byte 32) 1)
     (let* ((length (array-dimension sequence 0))
	    (end (or end length)))
       (unless (<= 0 end length)
	 (error 'index-out-of-range :index end :range length))
       (do ((i start (1+ i)))
	   ((>= i end))
	 (declare (type index i))
	 (setf (memref sequence (movitz-type-slot-offset 'movitz-basic-vector 'data)
		       :index i
		       :type :unsigned-byte32)
	   item))))
    (vector
     (let ((end (or end (length sequence))))
       (with-subvector-accessor (sequence-ref sequence start end)
	 (do ((i start (1+ i)))
	     ((>= i end))
	   (declare (index i))
	   (setf (sequence-ref i) item))))))
  sequence)

(defun replace (sequence-1 sequence-2 &key (start1 0) end1 (start2 0) end2)
  (cond
   ((and (eq sequence-1 sequence-2)
	 (<= start2 start1 (or end2 start1)))
    (if (= start1 start2)
	sequence-1			; no need to copy anything
      ;; must copy in reverse direction
      (sequence-dispatch sequence-1
	(vector
	 (let ((l (length sequence-1)))
	   (setf end1 (or end1 l)
		 end2 (or end2 l))
	   (assert (<= 0 start2 end2 l)))
	 (with-subvector-accessor (sequence-1-ref sequence-1 start1 end1)
	   (do* ((length (min (- end1 start1) (- end2 start2)))
		 (i (+ start1 length -1) (1- i))
		 (j (+ start2 length -1) (1- j)))
	       ((< i start1) sequence-1)
	     (declare (index i j length))
	     (setf (sequence-1-ref i)
	       (sequence-1-ref j)))))
	(list
	 (let* ((length (length sequence-1))
		(reverse-list (nreverse sequence-1))
		(size (min (- (or end1 length) start1) (- (or end2 length) start2))))
	   (do ((p (nthcdr (- length start1 size) reverse-list) (cdr p))
		(q (nthcdr (- length start2 size) reverse-list) (cdr q))
		(i 0 (1+ i)))
	       ((>= i size) (nreverse reverse-list))
	     (setf (car p) (car q))))))))
   ;; (not (eq sequence-1 sequence-2)) ..
   (t (sequence-dispatch sequence-1
	(vector
	 (setf end1 (or end1 (length sequence-1)))
	 (sequence-dispatch sequence-2
	   (vector
	    (setf end2 (or end2 (length sequence-2)))
	    (with-subvector-accessor (sequence-1-ref sequence-1 start1 end1)
	      (with-subvector-accessor (sequence-2-ref sequence-2 start2 end2)
		(cond
		 ((< (- end1 start1) (- end2 start2))
		  (do ((i start1 (1+ i))
		       (j start2 (1+ j)))
		      ((>= i end1) sequence-1)
		    (setf (sequence-1-ref i) (sequence-2-ref j))))
		 (t (do ((i start1 (1+ i))
			 (j start2 (1+ j)))
			((>= j end2) sequence-1)
		      (setf (sequence-1-ref i) (sequence-2-ref j))))))))
	   (list
	    (with-subvector-accessor (sequence-1-ref sequence-1 start1 end1)
	      (if (not end2)
		  (do ((i start1 (1+ i))
		       (p (nthcdr start2 sequence-2) (cdr p)))
		      ((or (null p) (>= i end1)) sequence-1)
		    (setf (sequence-1-ref i) (car p)))
		(do ((i start1 (1+ i))
		     (j start2 (1+ j))
		     (p (nthcdr start2 sequence-2) (cdr p)))
		    ((or (>= i end1) (endp p) (>= j end2)) sequence-1)
		  (setf (sequence-1-ref i) (car p))))))))
	(list
	 (sequence-dispatch sequence-2
	   (vector
	    (setf end2 (or end2 (length sequence-2)))
	    (with-subvector-accessor (sequence-2-ref sequence-2 start2 end2)
	      (do ((p (nthcdr start1 sequence-1) (cdr p))
		   (i start1 (1+ i))
		   (j start2 (1+ j)))
		  ((or (endp p) (>= j end2) (and end1 (>= i end1)))
		   sequence-1)
		(setf (car p) (sequence-2-ref j)))))
	   (list
	    (do ((i start1 (1+ i))
		 (j start2 (1+ j))
		 (p (nthcdr start1 sequence-1) (cdr p))
		 (q (nthcdr start2 sequence-2) (cdr q)))
		((or (endp p) (endp q)
		     (and end1 (>= i end1))
		     (and end2 (>= j end2)))
		 sequence-1)
	      (setf (car p) (car q)))))))
      sequence-1)))

(defun find (item sequence &key from-end (test 'eql) (start 0) end (key 'identity))
  (numargs-case
   (2 (item sequence)
      (sequence-dispatch sequence
	(vector
	 (with-subvector-accessor (sequence-ref sequence)
	   (dotimes (i (length sequence))
	     (when (eql item (sequence-ref i))
	       (return item)))))
	(list
	 (dolist (x sequence)
	   (when (eql item x)
	     (return x))))))
   (t (item sequence &key from-end (test 'eql) (start 0) end (key 'identity))
      (with-funcallable (test)
	(with-funcallable (key)
	  (sequence-dispatch sequence
	    (vector
	     (setf end (or end (length sequence)))
	     (with-subvector-accessor (sequence-ref sequence start end)
	       (if (not from-end)
		   (do ((i start (1+ i)))
		       ((>= i end) nil)
		     (when (test item (key (aref sequence i)))
		       (return (sequence-ref i))))
		 (do ((i (1- end) (1- i)))
		     ((< i start) nil)
		   (when (test item (key (sequence-ref i)))
		     (return (sequence-ref i)))))))
	    (list
	     (if end
		 (do ((p (nthcdr start sequence) (cdr p))
		      (i start (1+ i)))
		     ((or (>= i end) (endp p)) nil)
		   (when (test item (key (car p)))
		     (return (or (and from-end
				      (find item (cdr p)
					    :from-end t :test test
					    :key key :end (- end i 1)))
				 (car p)))))
	       (do ((p (nthcdr start sequence) (cdr p)))
		   ((endp p) nil)
		 (when (test item (key (car p)))
		   (return (or (and from-end (find item (cdr p) :from-end t :test test :key key))
			       (car p)))))))))))))
  

(defun find-if (predicate sequence &key from-end (start 0) end (key 'identity))
  (numargs-case
   (2 (predicate sequence)
      (with-funcallable (predicate)
	(sequence-dispatch sequence
	  (vector
	   (let ((end (length sequence)))
	     (with-subvector-accessor (sequence-ref sequence 0 end)
	       (do ((i 0 (1+ i)))
		   ((>= i end))
		 (let ((x (sequence-ref i)))
		   (when (predicate x) (return x)))))))
	  (list
	   (do ((p sequence (cdr p)))
	       ((endp p) nil)
	     (let ((x (car p)))
	       (when (predicate x) (return x))))))))
   (t (predicate sequence &key from-end (start 0) end (key 'identity))
      (with-funcallable (predicate)
	(with-funcallable (key)
	  (sequence-dispatch sequence
	    (vector
	     (setf end (or end (length sequence)))
	     (with-subvector-accessor (sequence-ref sequence start end)
	       (cond
		((not from-end)
		 (do ((i start (1+ i)))
		     ((>= i end))
		   (when (predicate (key (sequence-ref i)))
		     (return (sequence-ref i)))))
		(t (do ((i (1- end) (1- i)))
		       ((< i start))
		     (when (predicate (key (sequence-ref i)))
		       (return (sequence-ref i))))))))
	    (list
	     (cond
	      (end
	       (do ((p (nthcdr start sequence) (cdr p))
		    (i start (1+ i)))
		   ((or (>= i end) (endp p)) nil)
		 (when (predicate (key (car p)))
		   (return (or (and from-end
				    (find-if predicate (cdr p) :end (- end i 1) :key key :from-end t))
			       (car p))))))
	      (t (do ((p (nthcdr start sequence) (cdr p)))
		     ((endp p) nil)
		   (when (predicate (key (car p)))
		     (return (or (and from-end
				      (find-if predicate (cdr p) :key key :from-end t))
				 (car p))))))))))))))

(defun find-if-not (predicate sequence &rest key-args)
  (declare (dynamic-extent key-args))
  (apply (complement predicate) sequence key-args))
  
(defun count (item sequence &key (start 0) end (test 'eql) (key 'identity) test-not from-end)
  (declare (ignore test-not))
  (with-funcallable (test)
    (with-funcallable (key)
      (sequence-dispatch sequence
	(vector
	 (setf end (or end (length sequence)))
	 (with-subvector-accessor (sequence-ref sequence start end)
	   (cond
	    ((not from-end)
	     (do ((i start (1+ i))
		  (n 0))
		 ((>= i end) n)
	       (when (test item (key (sequence-ref i)))
		 (incf n))))
	    (t (do ((i (1- end) (1- i))
		    (n 0))
		   ((< i start) n)
		 (when (test item (key (sequence-ref i)))
		   (incf n)))))))
	(list
	 (cond
	  ((not end)
	   (do ((p (nthcdr start sequence) (cdr p))
		(n 0))
	       ((endp p) n)
	     (when (test item (key (car p)))
	       (incf n))))
	  (t (do ((p (nthcdr start sequence) (cdr p))
		  (i start (1+ i))
		  (n 0))
		 ((or (endp p) (>= i end)) n)
	       (when (test item (key (car p)))
		 (incf n))))))))))

(defun count-if (predicate sequence &key (start 0) end (key 'identity) #+ignore from-end)
  (numargs-case
   (2 (predicate sequence)
      (with-funcallable (predicate)
	(sequence-dispatch sequence
	  (list
	   (let ((count 0))
	     (dolist (x sequence)
	       (when (predicate x)
		 (incf count)))
	     count))
	  (vector
	   (with-subvector-accessor (sequence-ref sequence)
	     (let ((count 0))
	       (dotimes (i (length sequence))
		 (when (predicate (sequence-ref i))
		   (incf count)))
	       count))))))
   (t (predicate sequence &key (start 0) end (key 'identity) #+ignore from-end)
      (with-funcallable (predicate)
	(with-funcallable (key)
	  (sequence-dispatch sequence
	    (list
	     (if (not end)
		 (do ((n 0)
		      (p (nthcdr start sequence) (cdr p)))
		     ((endp p) n)
		   (when (predicate (key (car p)))
		     (incf n)))
	       (do ((n 0)
		    (i start (1+ i))
		    (p (nthcdr start sequence) (cdr p)))
		   ((or (endp p) (>= i end)) n)
		 (when (predicate (key (car p)))
		   (incf n)))))
	    (vector
	     (error "vector count-if not implemented."))))))))


(macrolet ((every-some-body ()
	     "This function body is shared between every and some."
	     `(with-funcallable (predicate)
		(cond
		 ((null more-sequences)	; 1 sequence case
		  (sequence-dispatch first-sequence
		    (list
		     (do ((p first-sequence (cdr p)))
			 ((null p) (default-value))
		       (test-return (predicate (car p)))))
		    (vector
		     (do* ((l (length first-sequence))
			   (i 0 (1+ i)))
			 ((= l i) (default-value))
		       (test-return (predicate (aref first-sequence i)))))))
		 ((null (cdr more-sequences)) ; 2 sequences case
		  (let ((second-sequence (first more-sequences)))
		    (sequence-double-dispatch (first-sequence second-sequence)
		      ((list list)
		       (do ((p0 first-sequence (cdr p0))
			    (p1 second-sequence (cdr p1)))
			   ((or (endp p0) (endp p1)) (default-value))
			 (test-return (predicate (car p0) (car p1)))))
		      ((vector vector)
		       (do ((end (min (length first-sequence) (length second-sequence)))
			    (i 0 (1+ i)))
			   ((>= i end) (default-value))
			 (test-return (predicate (aref first-sequence i)
						 (aref second-sequence i)))))
		      ((list vector)
		       (do ((end (length second-sequence))
			    (i 0 (1+ i))
			    (p first-sequence (cdr p)))
			   ((or (endp p) (>= i end)) (default-value))
			 (test-return (predicate (car p) (aref second-sequence i)))))
		      ((vector list)
		       (do ((end (length first-sequence))
			    (i 0 (1+ i))
			    (p second-sequence (cdr p)))
			   ((or (endp p) (>= i end)) (default-value))
			 (test-return (predicate (aref first-sequence i) (car p))))))))
		 (t (flet ((next (p)
			     (sequence-dispatch p
			       (list (cdr p))
			       (vector p)))
			   (seqend (p i)
			     (sequence-dispatch p
			       (list (null p))
			       (vector (>= i (length p)))))
			   (seqelt (p i)
			     (sequence-dispatch p
			       (list (car p))
			       (vector (aref p i)))))
		      (do* ((i 0 (1+ i)) ; 3 or more sequences, conses at 4 or more.
			    (p0 first-sequence (next p0))
			    (p1 (car more-sequences) (next p1))
			    (p2 (cadr more-sequences) (next p2))
			    (p3+ (cddr more-sequences) (map-into p3+ #'next p3+)) ;a list of pointers
			    (arg3+ (make-list (length p3+))))
			  ((or (seqend p0 i)
			       (seqend p1 i)
			       (seqend p2 i)
			       (dolist (p p3+ nil)
				 (when (seqend p i)
				   (return t))))
			   (default-value))
			(do ((x arg3+ (cdr x))
			     (y p3+ (cdr y)))
			    ((null x))
			  (setf (car x) (seqelt (car y) i)))
			(test-return (apply predicate (seqelt p0 i) (seqelt p1 i)
					    (seqelt p2 i) arg3+)))))))))
  (defun some (predicate first-sequence &rest more-sequences)
    (declare (dynamic-extent more-sequences))
    (macrolet ((test-return (form)
		 `(let ((x ,form)) (when x (return x))))
	       (default-value () nil))
      (every-some-body)))
  (defun every (predicate first-sequence &rest more-sequences)
    (declare (dynamic-extent more-sequences))
    (macrolet ((test-return (form)
		 `(unless ,form (return nil)))
	       (default-value () t))
      (every-some-body))))

(defun notany (predicate first-sequence &rest more-sequences)
  (declare (dynamic-extent more-sequences))
  (not (apply 'some predicate first-sequence more-sequences)))

(defun list-remove (item list test key end count)
  "Implements remove for lists. Assumes (not from-end)."
  (cond
   ((endp list)
    nil)
   ((eq 0 count)
    list)
   (t (with-funcallable (test)
	(with-funcallable (key)
	  (if (test item (key (car list)))
	      (list-remove item (cdr list) test key
			   (when end (1- end))
			   (when count (1- count)))
	    (do ((i 1 (1+ i))
		 (p0 list (cdr p0))
		 (p1 (cdr list) (cdr p1)))
		((or (endp p1) (and end (>= i end))) list)
	      (when (test item (key (car p1)))
		(return
		  ;; reiterate from <list> to <p1>, consing up a copy, with
		  ;; the copy's tail being the recursive call to list-remove.
		  (do* ((new-list (cons (car list) nil))
			(x (cdr list) (cdr x))
			(new-x new-list))
		      ((eq x p1)
		       (setf (cdr new-x) (list-remove item (cdr p1) test key
						      (when end (- end i 1))
						      (when count (1- count))))
		       new-list)
		    (setf new-x
		      (setf (cdr new-x)
			(cons (car x) nil)))))))))))))

(defun list-remove-simple (item list)
  "The same as list-remove, without count, end, or key, with test=eql."
  (cond
   ((endp list)
    nil)
   ((eql item (car list))
    (list-remove-simple item (cdr list)))
   (t (do ((i 1 (1+ i))
	   (p0 list (cdr p0))
	   (p1 (cdr list) (cdr p1)))
	  ((endp p1) list)
	(when (eql item (car p1))
	  (return
	    ;; reiterate from <list> to <p1>, consing up a copy, with
	    ;; the copy's tail being the recursive call to list-remove.
	    (do* ((new-list (cons (car list) nil))
		  (x (cdr list) (cdr x))
		  (new-x new-list))
		((eq x p1)
		 (setf (cdr new-x) (list-remove-simple item (cdr p1)))
		 new-list)
	      (setf new-x
		(setf (cdr new-x)
		  (cons (car x) nil))))))))))

(defun remove (item sequence &key (test 'eql) (start 0) end count (key 'identity) test-not from-end)
  (when test-not
    (setf test (complement test-not)))
  (sequence-dispatch sequence
    (list
     (setf sequence (nthcdr start sequence))
     (when end (decf end start))
     (cond
      ((endp sequence)
       nil)
      ((not from-end)
       (if (and (eq test 'eql)
		(not end)
		(not count)
		(eq key 'identity))
	   (list-remove-simple item sequence)
	 (list-remove item sequence test key end count)))
      (t (error "from-end not implemented."))))
    (vector
     (error "vector remove not implemented."))))

(defun list-remove-if (test list key end count)
  "Implements remove-if for lists. Assumes (not from-end)."
  (cond
   ((endp list)
    nil)
   ((eq 0 count)
    list)
   (t (with-funcallable (test)
	(with-funcallable (key)
	  (if (test (key (car list)))
	      (list-remove-if test (cdr list) key
			      (when end (1- end))
			      (when count (1- count)))
	    (do ((i 1 (1+ i))
		 (p0 list (cdr p0))
		 (p1 (cdr list) (cdr p1)))
		((or (endp p1) (and end (>= i end))) list)
	      (when (test (key (car p1)))
		(return
		  ;; reiterate from <list> to <p1>, consing up a copy, with
		  ;; the copy's tail being the recursive call to list-remove.
		  (do* ((new-list (cons (car list) nil))
			(x (cdr list) (cdr x))
			(new-x new-list))
		      ((eq x p1)
		       (setf (cdr new-x) (list-remove-if test (cdr p1) key
							 (when end (- end i 1))
							 (when count (1- count))))
		       new-list)
		    (setf new-x
		      (setf (cdr new-x)
			(cons (car x) nil)))))))))))))

(defun remove-if (test sequence &key from-end (start 0) end count (key 'identity))
  (sequence-dispatch sequence
    (list
     (setf sequence (nthcdr start sequence))
     (when end (decf end start))
     (cond
      ((endp sequence)
       nil)
      ((not from-end)
       (list-remove-if test sequence key end count))
      (t (error "from-end not implemented."))))
    (vector
     (error "vector remove not implemented."))))

(defun remove-if-not (test sequence &rest args)
  (declare (dynamic-extent args))
  (apply 'remove-if (complement test) sequence args))

(defun list-delete (item list test key start end count)
  "Implements delete-if for lists. Assumes (not from-end)."
  (cond
   ((null list)
    nil)
   ((eq 0 count)
    list)
   ((eq start end)
    list)
   (t (with-funcallable (test)
	(with-funcallable (key)
	  (let ((i 0)			; for end checking
		(c 0))			; for count checking
	    (cond
	     ((= 0 start)
	      ;; delete from head..
	      (do ()
		  ((not (test item (key (car list)))))
		(when (or (endp (setf list (cdr list)))
			  (eq (incf i) end)
			  (eq (incf c) count))
		  (return-from list-delete list)))
	      (setq start 1))
	     (t (incf i (1- start))))
	    ;; now delete "inside" list
	    (do* ((p (nthcdr (1- start) list))
		  (q (cdr p)))
		((or (endp q)
		     (eq (incf i) end))
		 list)
	      (cond
	       ((test item (key (car q)))
		(setf q (cdr q)
		      (cdr p) q)
		(when (eq (incf c) count)
		  (return list)))
	       (t (setf p q
			q (cdr q)))))))))))


(defun list-delete-if (test list key start end count)
  "Implements delete-if for lists. Assumes (not from-end)."
  (cond
   ((null list)
    nil)
   ((eq 0 count)
    list)
   ((eq start end)
    list)
   (t (with-funcallable (test)
	(with-funcallable (key)
	  (let ((i 0)			; for end checking
		(c 0))			; for count checking
	    (cond
	     ((= 0 start)
	      ;; delete from head..
	      (do ()
		  ((not (test (key (car list)))))
		(when (or (endp (setf list (cdr list)))
			  (eq (incf i) end)
			  (eq (incf c) count))
		  (return-from list-delete-if list)))
	      (setq start 1))
	     (t (incf i (1- start))))
	    ;; now delete "inside" list
	    (do* ((p (nthcdr (1- start) list))
		  (q (cdr p)))
		((or (endp q)
		     (eq (incf i) end))
		 list)
	      (cond
	       ((test (key (car q)))
		(setf q (cdr q)
		      (cdr p) q)
		(when (eq (incf c) count)
		  (return list)))
	       (t (setf p q
			q (cdr q)))))))))))

(defun delete (item sequence &key (test 'eql) from-end (start 0) end count (key 'identity))
  (sequence-dispatch sequence
    (list
     (when from-end
       (error "from-end not implemented."))
     (list-delete item  sequence test key start end count))
    (vector
     (error "vector delete not implemented."))))

(defun delete-if (test sequence &key from-end (start 0) end count (key 'identity))
  (sequence-dispatch sequence
    (list
     (when from-end
       (error "from-end not implemented."))
     (list-delete-if test sequence key start end count))
    (vector
     (error "vector delete-if not implemented."))))

(defun delete-if-not (test sequence &rest key-args)
  (declare (dynamic-extent key-args))
  (apply 'delete-if (complement test) sequence key-args))

(defun remove-duplicates (sequence &key (test 'eql) (key 'identity) (start 0) end test-not from-end)
  (when test-not
    (setf test (complement test-not)))
  (sequence-dispatch sequence
    (list
     (setf sequence (nthcdr start sequence))
     (when end (decf end start))
     (cond
      ((endp sequence)
       nil)
      ((not from-end)
       (let* ((new-end (when end (1- end)))
	      (tail (remove-duplicates (cdr sequence) :test test :key key :end new-end)))
	 (cond
	  ((find (car sequence) (cdr sequence) :test test :key key :end new-end)
	   tail)
	  ((eq tail (cdr sequence))
	   sequence)
	  (t (cons (car sequence) tail)))))		   
      (t (error "from-end not implemented."))))
    (vector
     (error "vector remove-duplicates not implemented."))))

(defun delete-duplicates (sequence &key from-end (test 'eql) (key 'identity) test-not (start 0) end)
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (sequence-dispatch sequence
      (list
       (cond
	(from-end
	 (error "from-end not implemented."))
	((not end)
	 (when (not (endp sequence))
	   (when (= 0 start)
	     ;; delete from head
	     (do ()
		 ((not (find (car sequence) (cdr sequence) :test test :key key)))
	       (setf sequence (cdr sequence))))
	   (do* ((p (nthcdr start sequence))
		 (q (cdr p) (cdr p)))
	       ((endp q) sequence)
	     (if (find (car q) (cdr q) :test test :key key)
		 (setf (cdr p) (cdr q))
	       (setf p (cdr p))))))
	(t (error "delete-duplicates end parameter not implemented."))))
      (vector
;;;       (unless end
;;;	 (setf end (length sequence)))
;;;       (do ((i start (1+ i))
;;;	    (c 0))
;;;	   ((>= i end)
;;;	    (cond
;;;	     ((= 0 c) sequence)
	     
       (error "vector delete-duplicates not implemented.")))))


(defun search (sequence-1 sequence-2 &key (test 'eql) (key 'identity)
					  (start1 0) end1 (start2 0) end2 test-not from-end)
  (let ((test (if test-not
		  (complement test-not)
		test)))
    (declare (dynamic-extent test))
    (sequence-dispatch sequence-2
      (vector
       (unless end1
	 (setf end1 (length sequence-1)))
       (unless end2
	 (setf end2 (length sequence-2)))
       (do ((stop (- end2 (- end1 start1 1)))
	    (i start2 (1+ i)))
	   ((>= i stop) nil)
	 (let ((mismatch-position (mismatch sequence-1 sequence-2
					    :start1 start1 :end1 end1
					    :start2 i :end2 end2
					    :key key :test test)))
	   (when (or (not mismatch-position)
		     (= mismatch-position end1))
	     (return (or (and from-end
			      (search sequence-1 sequence-2
				      :from-end t :test test :key key
				      :start1 start1 :end1 end1
				      :start2 (1+ i) :end2 end2))
			 i))))))
      (list
       (unless end1
	 (setf end1 (length sequence-1)))
       (do ((stop (and end2 (- end2 start2 (- end1 start1 1))))
	    (p (nthcdr start2 sequence-2) (cdr p))
	    (i 0 (1+ i)))
	   ((or (endp p) (and stop (>= i stop))) nil)
	 (let ((mismatch-position (mismatch sequence-1 p
					    :start1 start1 :end1 end1
					    :key key :test test)))
	   (when (or (not mismatch-position)
		     (= mismatch-position end1))
	     (return (+ start2 i
			(or (and from-end
				 (search sequence-1 p
					 :start2 1 :end2 (and end2 (- end2 i start2))
					 :from-end t :test test :key key
					 :start1 start1 :end1 end1))
			    0))))))))))


(defun insertion-sort (vector predicate key start end)
  "Insertion-sort is used for stable-sort, and as a finalizer for
quick-sort with cut-off greater than 1."
  (with-funcallable (predicate)
    (with-subvector-accessor (vector-ref vector start end)
      (if (not key)
	  (do ((i (1+ start) (1+ i)))
	      ((>= i end))
	    ;; insert vector[i] into [start...i-1]
	    (let ((v (vector-ref i))
		  (j (1- i)))
	      (when (predicate v (vector-ref j))
		(setf (vector-ref i) (vector-ref j))
		(do* ((j+1 j (1- j+1))
		      (j (1- j) (1- j)))
		    ((or (< j start)
			 (not (predicate v (vector-ref j))))
		     (setf (vector-ref j+1) v))
		  (setf (vector-ref j+1) (vector-ref j))))))
	(with-funcallable (key)
	  (do ((i (1+ start) (1+ i)))	; the same, only with a key-function..
	      ((>= i end))
	    ;; insert vector[i] into [start...i-1]
	    (do* ((v (vector-ref i))
		  (vk (key v))
		  (j (1- i) (1- j))
		  (j+1 i (1- j+1)))
		((or (<= j+1 start)
		     (not (predicate vk (key (vector-ref j)))))
		 (setf (vector-ref j+1) v))
	      (setf (vector-ref j+1) (vector-ref j))))))))
  vector)

(defun quick-sort (vector predicate key start end cut-off)
  (macrolet ((do-while (p &body body)
	       `(do () ((not ,p)) ,@body)))
    (when (> (- end start) cut-off)
      (with-subvector-accessor (vector-ref vector start end)
	(with-funcallable (predicate)
	  (with-funcallable (key)
	    (prog* ((pivot (vector-ref start)) ; should do median-of-three here..
		    (keyed-pivot (key pivot))
		    (left (1+ start))
		    (right (1- end))
		    left-item right-item)
	     partitioning-loop
	      (do-while (not (predicate keyed-pivot (key (setf left-item (vector-ref left)))))
		(incf left)
		(when (>= left end)
		  (setf right-item (vector-ref right))
		  (go partitioning-complete)))
	      (do-while (predicate keyed-pivot (key (setf right-item (vector-ref right))))
		(decf right))
	      (when (< left right)
		(setf (vector-ref left) right-item
		      (vector-ref right) left-item)
		(incf left)
		(decf right)
		(go partitioning-loop))
	     partitioning-complete
	      (setf (vector-ref start) right-item ; (aref vector right)
		    (vector-ref right) pivot)
	      (quick-sort vector predicate key start right cut-off)
	      (quick-sort vector predicate key (1+ right) end cut-off)))))))
  vector)

(defun sort (sequence predicate &key (key 'identity))
  (sequence-dispatch sequence
    (list
     (sort-list sequence predicate key))
    (vector
     (quick-sort sequence predicate key 0 (length sequence) 9)
     (insertion-sort sequence predicate key 0 (length sequence)))))

(defun stable-sort (sequence predicate &key key)
  (sequence-dispatch sequence
    (list
     (error "Stable-sort not implemented for lists."))
    (vector
     (insertion-sort sequence predicate key 0 (length sequence)))))


(defun merge (result-type sequence-1 sequence-2 predicate &key (key 'identity))
  (ecase result-type
    (list
     (sequence-double-dispatch (sequence-1 sequence-2)
       ((list list)
	(merge-list-list sequence-1 sequence-2 predicate key))))))

(defun merge-list-list (list1 list2 predicate key)
  (cond
   ((null list1)
    list2)
   ((null list2)
    list1)
   (t (with-funcallable (predicate)
	(with-funcallable (key)
	  (macrolet ((xpop (var)
		       `(let ((x ,var)) (setf ,var (cdr x)) x)))
	    (do* ((result (if (predicate (key (car list1)) (key (car list2)))
			      (xpop list1)
			    (xpop list2)))
		  (r result))
		((null (setf r
			 (setf (cdr r)
			   (cond
			    ((null list1) (xpop list2))
			    ((null list2) (xpop list1))
			    ((predicate (key (car list1)) (key (car list2)))
			     (xpop list1))
			    (t (xpop list2))))))
		 result))))))))
	    
	 
;;; Most of list-sorting snipped from cmucl.
	       
;;; MERGE-LISTS*   originally written by Jim Large.
;;; 		   modified to return a pointer to the end of the result
;;; 		      and to not cons header each time its called.
;;; It destructively merges list-1 with list-2.  In the resulting
;;; list, elements of list-2 are guaranteed to come after equal elements
;;; of list-1.
(defun merge-lists* (list-1 list-2 predicate key merge-lists-header)
  (with-funcallable (predicate)
    (with-funcallable (key)
      (do* ((result merge-lists-header)
	    (P result))			; P points to last cell of result
	  ((or (null list-1) (null list-2)) ; done when either list used up	
	   (if (null list-1)		; in which case, append the
	       (rplacd p list-2)	;   other list
	     (rplacd p list-1))
	   (do ((drag p lead)
		(lead (cdr p) (cdr lead)))
	       ((null lead)
		(values (prog1 (cdr result) ; return the result sans header
			  (rplacd result nil)) ; (free memory, be careful)
			drag))))	; and return pointer to last element
	(cond ((predicate (key (car list-2)) (key (car list-1)))
	       (rplacd p list-2)	; append the lesser list to last cell of
	       (setq p (cdr p))		;   result.  Note: test must bo done for
	       (pop list-2))		;   list-2 < list-1 so merge will be
	      (t (rplacd p list-1)	;   stable for list-1
		 (setq p (cdr p))
		 (pop list-1)))))))


;;; SORT-LIST uses a bottom up merge sort.  First a pass is made over
;;; the list grabbing one element at a time and merging it with the next one
;;; form pairs of sorted elements.  Then n is doubled, and elements are taken
;;; in runs of two, merging one run with the next to form quadruples of sorted
;;; elements.  This continues until n is large enough that the inner loop only
;;; runs for one iteration; that is, there are only two runs that can be merged,
;;; the first run starting at the beginning of the list, and the second being
;;; the remaining elements.

(defun sort-list (list pred key)
  (let ((head (cons :header list))  ; head holds on to everything
	(n 1)                       ; bottom-up size of lists to be merged
	unsorted		    ; unsorted is the remaining list to be
				    ;   broken into n size lists and merged
	list-1			    ; list-1 is one length n list to be merged
	last			    ; last points to the last visited cell
	(merge-lists-header (list :header)))
    (declare (fixnum n))
    (do () (nil)
      ;; start collecting runs of n at the first element
      (setf unsorted (cdr head))
      ;; tack on the first merge of two n-runs to the head holder
      (setf last head)
      (let ((n-1 (1- n)))
	(declare (fixnum n-1))
	(do () (nil)
	  (setf list-1 unsorted)
	  (let ((temp (nthcdr n-1 list-1))
		list-2)
	    (cond (temp
		   ;; there are enough elements for a second run
		   (setf list-2 (cdr temp))
		   (setf (cdr temp) nil)
		   (setf temp (nthcdr n-1 list-2))
		   (cond (temp
			  (setf unsorted (cdr temp))
			  (setf (cdr temp) nil))
			 ;; the second run goes off the end of the list
			 (t (setf unsorted nil)))
		   (multiple-value-bind (merged-head merged-last)
		       (merge-lists* list-1 list-2 pred key
				     merge-lists-header)
		     (setf (cdr last) merged-head)
		     (setf last merged-last))
		   (if (null unsorted) (return)))
		  ;; if there is only one run, then tack it on to the end
		  (t (setf (cdr last) list-1)
		     (return)))))
	(setf n (ash n 1))		; (+ n n)
	;; If the inner loop only executed once, then there were only enough
	;; elements for two runs given n, so all the elements have been merged
	;; into one list.  This may waste one outer iteration to realize.
	(if (eq list-1 (cdr head))
	    (return list-1))))))

(defun make-sequence (result-type size &key (initial-element nil initial-element-p))
  "=> sequence"
  (ecase result-type
    (string
     (if (not initial-element-p)
	 (make-string size)
       (make-string size :initial-element initial-element)))
    (vector
     (make-array size :initial-element initial-element))
    (list
     (make-list size :initial-element initial-element))))

(defun concatenate (result-type &rest sequences)
  "=> result-sequence"
  (declare (dynamic-extent sequences))
  (cond
   ((null sequences)
    (make-sequence result-type 0))
   ((and (null (rest sequences))
	 (typep (first sequences) result-type))
    (copy-seq (first sequences)))
   ((= 0 (length (first sequences)))
    (apply #'concatenate result-type (cdr sequences)))
   ((member result-type '(vector string))
    (let* ((r (make-sequence result-type
			     (let ((length 0))
			       (dolist (s sequences length)
				 (incf length (length s))))))
	   (i 0))
      (dolist (s sequences)
	(replace r s :start1 i)
	(incf i (length s)))
      r))
   (t (error "Can't concatenate ~S yet: ~:S" result-type sequences))))
     
  
