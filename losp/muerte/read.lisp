;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      read.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Oct 17 21:50:42 2001
;;;;                
;;;; $Id: read.lisp,v 1.14 2006/04/07 21:50:37 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/read)

(in-package muerte)

(defvar *read-suppress*)
(defvar *readtable* nil)

(defun copy-readtable (&optional from-readtable to-readtable)
  (declare (ignore from-readtable to-readtable))
  nil)

(defun substring (string start end)
  (if (and (zerop start) (= end (length string)))
      string
    (subseq string start end)))

(defun parse-integer (string &key (start 0) (end (length string)) (radix 10) (junk-allowed nil))
  "PARSE-INTEGER parses an integer in the specified radix from the substring
of string delimited by start and end."
  (let ((integer 0)
	(minusp nil)
	(integer-start (do ((i start (1+ i)))
			   ((>= i end) (if junk-allowed
					   (return-from parse-integer (values nil i))
					 (error "No integer in the string ~S."
						(substring string start end))))
			 (unless (char-whitespace-p (char string i))
			   (return i)))))
    (case (char string integer-start)
      (#\+ (incf integer-start))
      (#\- (setf minusp t)
	   (incf integer-start)))
    (when (>= integer-start end)
      (if junk-allowed
	  (return-from parse-integer (values nil integer-start))
	(error "No integer in the string ~S." (substring string start end))))
    (setf integer (digit-char-p (char string integer-start) radix))
    (unless integer
      (if junk-allowed
	  (return-from parse-integer (values nil integer-start))
	(error "There is junk in the string ~S." (substring string start end))))
    (do ((i (1+ integer-start) (1+ i)))
	((>= i end) (values (if minusp (- integer) integer) i))
      (let ((digit (digit-char-p (char string i) radix)))
	(cond
	 ((not (null digit))
	  (setf integer (+ (* integer radix) digit)))
	 ((char-whitespace-p (char string i))
	  ;; Skip trailing whitespace
	  (do () (nil)
	    (incf i)
	    (cond
	     ((>= i end)
	      (return-from parse-integer (values integer i)))
	     ((char-whitespace-p (char string i))
	      nil)
	     (junk-allowed
	      (return-from parse-integer (values integer i)))
	     (t (error "There is junk in the string ~S." (substring string start end))))))
	 (junk-allowed
	  (return-from parse-integer (values integer i)))
	 (t (error "There is junk in the string ~S." (substring string start end))))))))


(defconstant +simple-token-terminators+ '(#\space #\tab #\newline #\) #\( #\'))

(defun find-token-end (string &key (start 0) (end (length string)))
  (do ((i start (1+ i)))
      ((>= i end) end)
    (when (member (aref string i) +simple-token-terminators+)
      (return i))))

(defun simple-read-token (string &key (start 0) (end (length string)))
  (let ((start (check-the index start))
	(end (check-the index end))
	(colon-position (and (char= #\: (schar string start)) start))
	(almost-integer nil))
    (multiple-value-bind (token-end token-integer token-denominator)
	(do ((integer (or (digit-char-p (schar string start) *read-base*)
			  (and (member (schar string start) '(#\- #\+))
			       (> end (1+ start))
			       (digit-char-p (schar string (1+ start)) *read-base*)
			       0)))
	     (denominator nil)
	     (decimal nil)
	     (i (1+ start) (1+ i)))
	    ((or (>= i end)
		 (member (schar string i) +simple-token-terminators+))
	     (values i
		     (unless (eql 0 denominator)
		       (if (and integer (char= #\- (schar string start)))
			   (- integer)
			 integer))
		     (when (and integer denominator (plusp denominator))
		       denominator)))
	  (declare (index i))
	  (let ((c (schar string i)))
	    (when (char= #\: c)
	      (setf colon-position i))
	    (setf almost-integer integer)
	    (when integer
	      (let ((digit (digit-char-p c *read-base*)))
		(cond
		 (denominator
		  (if (not digit)
		      (setf integer nil)
		    (setf denominator (+ (* denominator *read-base*) digit))))
		 ((char= #\/ c)
		  (setf denominator 0))
		 (t (setf integer (and digit (+ (* integer *read-base*) digit)))))))))
      (cond
       (token-denominator
	(values (make-rational token-integer token-denominator)
		token-end))
       (token-integer
	(values token-integer token-end))
       ((and (char= #\. (schar string (1- token-end))) ; check for base-10 <n>. notation.
	     (> token-end start)
	     (or almost-integer
		 (and (< *read-base* 10)
		      (do ((i start (1+ i)))
			  ((>= i (1- token-end)) t)
			(declare (index i))
			(unless (digit-char-p (schar string i) 10)
			  (return nil))))))
	(let ((x (if (= *read-base* 10)
		     almost-integer
		   (parse-integer string :start start :end (1- token-end)
				  :junk-allowed nil))))
	  (values x token-end)))
       ((not colon-position)
	(values (intern-string string *package* :start start :end token-end :key #'char-upcase)
		token-end))
       ((= start colon-position)
	(values (intern-string string :keyword :start (1+ start) :end token-end :key #'char-upcase)
		token-end))
       (t (let ((package-end (if (and (> colon-position 0)
				      (char= #\: (schar string (1- colon-position))))
				 (1- colon-position)
			       colon-position)))
	    (values (intern-string string (or (find-package-string string start package-end
								   #'char-upcase)
					      (error "No package named ~S."
						     (substring string start package-end)))
				   :start (1+ colon-position) :end token-end :key #'char-upcase)
		    token-end)))))))


(defun simple-read-integer (string start end radix)
  (multiple-value-bind (x token-end)
      (let ((*read-base* radix))
	(simple-read-token string :start start :end end))
    (check-type x number)
    (values x token-end))
  #+ignore
  (let ((token-end (do ((i start (1+ i)))
		       ((>= i end) i)
		     (when (member (schar string i) +simple-token-terminators+)
		       (return i)))))
    (values (parse-integer string
			   :start start
			   :end token-end
			   :radix radix
			   :junk-allowed nil)
	    token-end)))

(define-condition reader-error () ())
(define-condition missing-delimiter (reader-error)
  ((delimiter
    :initarg :delimiter
    :reader delimiter)))

(defun simple-read-delimited-list (delimiter string start end &key (tail-delimiter #\.) list)
  "=> list, new-position, new-string, new-end."
  (let ((start (check-the index start))
	(end (check-the index end)))
    (multiple-value-bind (next-string next-start next-end)
	(catch 'next-line
	  (restart-bind
	      ((next-line (lambda (next-string &optional (next-start 0)
							 (next-end (length next-string)))
			    (throw 'next-line
			      (values next-string next-start next-end)))))
	    (do ((i start (1+ i)))
		((>= i end)
		 (error 'missing-delimiter
			:delimiter delimiter
			:start-position start))
	      (declare (index i))
	      (let ((char (schar string i)))
		(cond
		 ((char= delimiter char)
		  (return-from simple-read-delimited-list
		    (values (nreverse list) (1+ i) string end)))
		 ((eq tail-delimiter char)
		  (unless list
		    (error "Nothing before ~C in list." tail-delimiter))
		  (multiple-value-bind (cdr-list cdr-end cdr-string cdr-string-end)
		      (simple-read-delimited-list #\) string (1+ i) end
						  :tail-delimiter tail-delimiter)
		    (unless (endp (cdr cdr-list))
		      (error "Too many objects after ~C in list: ~S"
			     tail-delimiter (cdr cdr-list)))
		    (setf list (nreverse list)
			  (cdr (last list)) (car cdr-list))
		    (return-from simple-read-delimited-list
		      (values list cdr-end cdr-string cdr-string-end))))
		 ((char-whitespace-p char))
		 (t (multiple-value-bind (element element-end next-string next-string-end)
			(simple-read-from-string string t t :start i :end end)
		      (when next-string
			(assert next-string-end)
			(setf string next-string
			      end next-string-end))
		      (setf i (1- element-end))
		      (push element list))))))))
      (simple-read-delimited-list delimiter next-string next-start next-end
				  :tail-delimiter tail-delimiter
				  :list list))))

(defun position-with-escape (char string start end &optional (errorp t))
  (with-subvector-accessor (string-ref string start end)
    (do* ((i start (1+ i))
	  (escapes 0))
	((>= i end)
	 (when errorp
	   (error "Missing terminating character ~C." char)))
      (declare (index i))
      (let ((c (string-ref i)))
	(cond
	 ((char= char c)
	  (return (values i escapes)))
	 ((char= #\\ c)
	  (incf escapes)
	  (incf i)))))))

(defun escaped-string-copy (string start end num-escapes)
  (let ((start (check-the index start))
	(end (check-the index end)))
    (do* ((length (- end start num-escapes))
	  (new-string (make-string length))
	  (p 0 (1+ p))
	  (q start (1+ q)))
	((>= p length) new-string)
      (declare (index p q))
      (when (char= (char string q) #\\)
	(incf q))
      (setf (char new-string p) (char string q)))))
  

(defun simple-read-from-string (string &optional eof-error-p eof-value &key (start 0) (end (length string)))
  "=> object, new-position, new-string, new-end."
  (let ((start (check-the index start))
	(end (check-the index end)))
    (do ((i start (1+ i)))
	((>= i end) (if eof-error-p
			(error "EOF")
		      (values eof-value i)))
      (declare (index i))
      (case (schar string i)
	((#\space #\tab #\newline))
	(#\( (return-from simple-read-from-string
	       (simple-read-delimited-list #\) string (1+ i) end :tail-delimiter #\.)))
	(#\) (warn "Ignoring extra ~C." (schar string i))
	     (incf i))
	(#\' (multiple-value-bind (quoted-form form-end)
		 (simple-read-from-string string eof-error-p eof-value :start (1+ i) :end end)
	       (return-from simple-read-from-string
		 (values (list 'quote quoted-form) form-end string end))))
	(#\" (incf i)
	     (multiple-value-bind (string-end num-escapes)
		 (position-with-escape #\" string i end)
	       (return-from simple-read-from-string
		 (values (escaped-string-copy string i string-end num-escapes)
			 (1+ string-end)
			 string end))))
	(#\| (incf i)
	     (multiple-value-bind (symbol-end num-escapes)
		 (position-with-escape #\| string i end)
	       (return-from simple-read-from-string
		 (values (if (= 0 num-escapes)
			     (intern-string string *package* :start i :end symbol-end)
			   (intern (escaped-string-copy string i symbol-end num-escapes)))
			 (1+ symbol-end)
			 string end))))
	(#\# (assert (< (incf i) end) (string)
	       "End of string after #: ~S." (substring string start end))
	    (multiple-value-bind (parameter parameter-end)
		(parse-integer string :start i :end end :radix 10 :junk-allowed t)
	      (setf i parameter-end)
	      (return-from simple-read-from-string
		(ecase (char-downcase (char string i))
		  (#\b (simple-read-integer string (1+ i) end 2))
		  (#\o (simple-read-integer string (1+ i) end 8))
		  (#\x (simple-read-integer string (1+ i) end 16))
		  (#\r (check-type parameter (integer 2 36))
		       (simple-read-integer string (1+ i) end parameter))
		  (#\' (multiple-value-bind (quoted-form form-end)
			   (simple-read-from-string string eof-error-p eof-value :start (1+ i) :end end)
			 (values (list 'function quoted-form) form-end string end)))
		  (#\( (multiple-value-bind (contents-list form-end)
			   (simple-read-delimited-list #\) string (1+ i) end)
			 (values (replace (make-array (or parameter (length contents-list))
						      :initial-element (car (last contents-list)))
					  contents-list)
				 form-end
				 string end)))
		  (#\* (let* ((token-end (find-token-end string :start (incf i) :end end))
			      (bit-vector (make-array (or parameter (- token-end i))
						      :element-type 'bit)))
			 (do ((p i (1+ p))
			      (q 0 (1+ q))
			      (bit nil))
			     ((>= q (length bit-vector)))
			   (when (< p token-end)
			     (setf bit (schar string p)))
			   (case bit
			     (#\0 (setf (aref bit-vector q) 0))
			     (#\1 (setf (aref bit-vector q) 1))
			     (t (error "Illegal bit-vector element: ~S" bit))))
			 (values bit-vector
				 token-end
				 string end)))
		  (#\s (multiple-value-bind (struct-form form-end)
			   (simple-read-from-string string eof-error-p eof-value :start (1+ i) :end end)
			 (check-type struct-form list)
			 (let* ((struct-name (car struct-form))
				(struct-args (cdr struct-form)))
			   (check-type struct-name symbol "A structure name.")
			   (values (apply #'make-structure struct-name struct-args)
				   form-end string end))))
		  (#\: (let* ((token-end (find-token-end string :start (incf i) :end end))
			      (symbol-name (string-upcase string :start i :end token-end)))
			 (values (make-symbol symbol-name)
				 token-end string end)))
		  (#\\ (let* ((token-end (find-token-end string :start (incf i) :end end))
			      (char (name-char string i token-end)))
			 (cond
			  (char (values char token-end))
			  ((>= 1 (- token-end i))
			   (values (char string i) (1+ i) string end))
			  (t (error "Don't know this character: ~S"
				    (substring string i token-end))))))))))
	(t (return-from simple-read-from-string
	     (simple-read-token string :start i :end end)))))))

(defun read-from-string (&rest args)
  (declare (dynamic-extent args))
  (apply #'simple-read-from-string args))

(defun un-backquote (form level)
  "Dont ask.."
  (declare (notinline un-backquote))
  (assert (not (minusp level)))
  (values
   (typecase form
     (null nil)
     (list
      (case (car form)
	(backquote-comma
	 (cadr form))
	(t (cons 'append
		 (loop for sub-form-head on form
		     as sub-form = (and (consp sub-form-head)
					(car sub-form-head))
		     collecting
		       (cond
			((atom sub-form-head)
			 (list 'quote sub-form-head))
			((atom sub-form)
			 (list 'quote (list sub-form)))
			(t (case (car sub-form)
			     (muerte::movitz-backquote
			      (list 'list
				    (list 'list (list 'quote 'muerte::movitz-backquote)
					  (un-backquote (cadr sub-form) (1+ level)))))
			     (backquote-comma
			      (cond
			       ((= 0 level)
				(list 'list (cadr sub-form)))
			       ((and (listp (cadr sub-form))
				     (eq 'backquote-comma-at (caadr sub-form)))
				(list 'append
				      (list 'mapcar
					    '(lambda (x) (list 'backquote-comma x))
					    (cadr (cadr sub-form)))))
			       (t (list 'list
					(list 'list
					      (list 'quote 'backquote-comma)
					      (un-backquote (cadr sub-form) (1- level)))))))
			     (backquote-comma-at
			      (if (= 0 level)
				  (cadr sub-form)
				(list 'list
				      (list 'list
					    (list 'quote 'backquote-comma-at)
					    (un-backquote (cadr sub-form) (1- level))))))
			     (t (list 'list (un-backquote sub-form level))))))
		     when (not (listp (cdr sub-form-head)))
		     collect (list 'quote (cdr sub-form-head)))
		 ))))
     (array
      (error "Array backquote not implemented."))
     (t (list 'quote form)))))

