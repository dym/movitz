;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      format.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sat Mar 23 01:18:36 2002
;;;;                
;;;; $Id: format.lisp,v 1.17 2007/04/09 21:10:48 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/format)

(in-package muerte)

;;;
;;; Format extensions:
;;;
;;;  ~Z   Print a word in hex.
;;;  ~@Z  Print the (32-bit) word located at a fixnum argument.
;;;

(defun format (destination control &rest args)
  (declare (dynamic-extent args))
  (let ((destination
	 (case destination
	   ((nil) (make-array (+ (length control)
				 (* 8 (count #\~ control)))
			      :element-type 'character
			      :fill-pointer 0
			      :adjustable t))
	   ((t) *standard-output*)
	   (otherwise destination))))
    (etypecase control
      (string
       (let ((*standard-output* destination))
	 (format-by-string control 0 0 args)))
      (function
       (apply control destination args)))
    (if (stringp destination)
	destination
      nil)))

(defun format-integer (x base at-sign-p colon-p prefix-parameters)
  (if (integerp x)
      (let ((mincol (first prefix-parameters))
	    (padchar (or (second prefix-parameters) #\space))
	    (commachar (or (third prefix-parameters) #\,))
	    (comma-interval (or (fourth prefix-parameters) 3)))
	(write-integer x *standard-output* base nil
		       mincol padchar at-sign-p commachar (and colon-p comma-interval)))
    (let ((*print-escape* nil)
	  (*print-radix* nil)
	  (*print-base* base)
	  (*print-readably* nil))
      (write x))))

(defun format-float (x &optional at-sign-p colon-p w d (k 0) overflowchar padchar)
  (cond
   ((eql 0 d)
    (write-integer (round x) *standard-output* 10 nil))
   ((minusp x)
    (write-char #\-)
    (format-float (- x) at-sign-p colon-p w d k overflowchar padchar))
   (t (let ((decimals (if d (1- d) 15)))
        (multiple-value-bind (integer-part decimal-part)
            (truncate (+ x (* 1/20 (expt 1/10 decimals))))
          (write-integer integer-part *standard-output* 10 nil)
          (dotimes (i k)
            (write-char #\0))
          (write-char #\.)
          (do ((remainder decimal-part)
               (i 0 (1+ i)))
              ((or (and (not d) (plusp i) (zerop remainder))
                   (> i decimals)))
            (declare (index i))
            (multiple-value-bind (next-digit next-remainder)
                (truncate (* 10 remainder))
              (setf remainder next-remainder)
              (write-digit next-digit *standard-output*))))))))

(defun find-directive (string i directive &optional recursive-skip-start
						    (recursive-skip-end directive))
  "Return position of <directive> in <string>, starting search at <i>. Also return
colon-at-p and at-sign-p. If <recursive-skip-directive> is used to search for matching
clause."
  (prog ((local-colon-p nil)
	 (local-at-p nil))
   loop
    (setq i (position #\~ string :start i))
    (unless i
      (return nil))
   next-after-tilde
    (incf i)
    (let ((c (char-upcase (char string i))))
      (case c
	(#\: (setf local-colon-p t) (go next-after-tilde))
	(#\@ (setf local-at-p t) (go next-after-tilde))
	(#\' (incf i) (go next-after-tilde))
	((#\, #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
	 (go next-after-tilde)))
      (cond
       ((char= c directive)
	(return (values i local-colon-p local-at-p)))
       ((and recursive-skip-start
	     (char= c recursive-skip-start))
	(setq i (find-directive string (1+ i)
				recursive-skip-end
				recursive-skip-start
				recursive-skip-end))
	(assert i () "Recursive search for format directive ~A failed." directive))
       ((and recursive-skip-start
	     recursive-skip-end
	     (char= c recursive-skip-end))
	(return nil))))
    (go loop)))

(defun format-by-string (control-string start loop-limit args)
  (declare (dynamic-extent args))
  (check-type control-string string)
  (let ((args-head args)		; keep this in case of ~:*.
	(i start))
    (tagbody
     loop
      (when (>= i (length control-string))
	(go end-loop))
      (let ((c (schar control-string i)))
	(if (char/= c #\~)
	    (write-char c)
	  ;; Process ~ directive
	  (prog ((colon-p nil)
		 (at-sign-p nil)
		 (prefix-parameters nil))
	   proceed
	    (incf i)
	    (case (char-upcase (schar control-string i))
	      (#\Newline
	       (when at-sign-p
		 (write-char #\Newline))
	       (unless colon-p
		 (do ((stop (1- (length control-string))))
		     ((or (>= i stop)
			  (not (member (schar control-string (1+ i))
				       '(#\space #\newline #\tab)))))
		   (incf i))))
	      (#\P (let ((arg (if (not colon-p)
				  (pop args)
				(car (nthcdr (1- (do ((i 0 (1+ i)) (p args-head (cdr p)))
						     ((eq p args) i) ; find arg's position in arg-head.
						   (assert p)))
					     args-head)))))
		     (write-string (if at-sign-p
				       (if (eql arg 1) "y" "ies")
				     (if (eql arg 1) "" "s")))))
	      (#\Z (if at-sign-p
		       (print-word-indirect (pop args) nil)
		     (print-word (pop args) nil)))
	      (#\A (let ((arg (pop args)))
		     (cond
		      ((and (null arg) colon-p)
		       (write-string "()"))
		      (t (write arg :escape nil :readably nil)))))
	      (#\S (let ((arg (pop args)))
		     (cond
		      ((and (null arg) colon-p)
		       (write-string "()"))
		      (t (write arg :escape t)))))
	      (#\W (cond
		    ((and colon-p at-sign-p)
		     (write (pop args) :pretty t :level nil :length nil))
		    (colon-p
		     (write (pop args) :pretty t))
		    (at-sign-p
		     (write (pop args) :level nil :length nil))
		    (t (write (pop args)))))
	      (#\B (format-integer (pop args) 2 at-sign-p colon-p
				   (reverse prefix-parameters)))
	      (#\O (format-integer (pop args) 8 at-sign-p colon-p
				   (reverse prefix-parameters)))
	      (#\D (format-integer (pop args) 10 at-sign-p colon-p
				   (reverse prefix-parameters)))
	      (#\X (format-integer (pop args) 16 at-sign-p colon-p
				   (reverse prefix-parameters)))
	      (#\F (apply 'format-float (pop args) at-sign-p colon-p (nreverse prefix-parameters)))
	      (#\C (if colon-p
		       (let ((c (pop args)))
			 (write-string (or (char-name c) c)))
		     (write-char (pop args))))
	      (#\% (dotimes (i (or (car prefix-parameters) 1))
		     (terpri)))
	      (#\& (fresh-line))
	      (#\~ (write-char #\~))
	      (#\/ (let* ((name-end (or (position #\/ control-string :start (incf i))
					(error "Call function name not terminated in ~S."
					       control-string)))
			  (function-name (read-from-string control-string nil nil
							   :start i :end name-end)))
		     (check-type function-name symbol)
		     (setf i name-end)
		     (apply function-name *standard-output* (pop args)
			    colon-p at-sign-p (nreverse prefix-parameters))))
	      (#\* (cond
		    ((and colon-p at-sign-p)
		     (error "~:@* is not defined."))
		    (at-sign-p		; goto relative to args-head.
		     (setf args (nthcdr (or (first prefix-parameters) 0)
					args-head)))
		    (colon-p		; goto backwards
		     (setf args (nthcdr (- (do ((i 0 (1+ i)) (p args-head (cdr p)))
					       ((eq p args) i) ; find arg's position in arg-head.
					     (assert p))
					   (or (first prefix-parameters) 1))
					args-head)))
		    (t (setf args (nthcdr (or (first prefix-parameters) 1)
					  args)))))
	      (#\[ (cond
		    ((and (not colon-p) (not at-sign-p))
		     (do ((clause-number (or (car prefix-parameters)
					     (pop args)))
			  (last-else-pos nil))
			 ((= 0 clause-number))
		       (multiple-value-bind (clause-pos clause-colon-p)
			   (find-directive control-string i #\; #\[ #\])
			 (unless clause-pos
			   (if last-else-pos
			       (setf i last-else-pos)
			     (setf i (find-directive control-string i #\] #\[)))
			   (return))
			 (setq i clause-pos)
			 (when clause-colon-p
			   (setq last-else-pos i))
			 (decf clause-number))))
		    ((and colon-p (not at-sign-p))
		     (cond
		      ((not (pop args))) ; false, use (first) alternative clause.
		      (t (setf i (or (find-directive control-string i #\; #\[ #\])
				     (find-directive control-string i #\] #\[)))
			 (assert i () "Format directive ~~:[ not terminated."))))
		    ((and at-sign-p (not colon-p))
		     (when (not (car args))
		       (pop args)
		       (setf i (find-directive control-string i #\] #\[))
		       (assert i () "Format directive ~~@[ not terminated.")))
		    (t (error "~~:@[ is unspecified."))))
	      (#\])
	      (#\; (setq i (find-directive control-string (incf i) #\] #\[))
		(assert i () "Unterminated format directive ~~;"))
	      (#\{ (let ((loop-limit (or (first prefix-parameters) -1)))
		     (flet ((skip-iteration (string start)
			      (do ((i start (1+ i))
				   (level 0))
				  ((>= i (length string)) i)
				(when (char= #\~ (schar string (1- i)))
				  (case (schar string i)
				    (#\} (if (plusp level)
					     (decf level)
					   (return i)))
				    (#\{ (incf level)))))))
		       (cond
			(colon-p
			 (prog ((loop-args (if at-sign-p args (pop args)))
				(loop-start (1+ i)))
			   (when (or (zerop loop-limit) (null loop-args))
			     (setf i (skip-iteration control-string (1+ i)))
			     (go skip-iteration))
			  iterate
			   (setf i
			     (format-by-string control-string loop-start 0 (pop loop-args)))
			   (when (and (< i (length control-string))
				      (char= #\} (schar control-string i))
				      loop-args
				      (not (zerop loop-limit)))
			     (decf loop-limit)
			     (go iterate))
			   (when at-sign-p
			     (setf args loop-args))
			  skip-iteration))
			(at-sign-p
			 (unless (or (zerop loop-limit)
				     (null args))
			   (setf args (nth-value 1 (format-by-string control-string (1+ i)
								     (1- loop-limit) args))))
			 (setf i (skip-iteration control-string (1+ i))))
			(t (let ((loop-args (pop args)))
			     (unless (or (zerop loop-limit) (null loop-args))
			       (format-by-string control-string (1+ i)
						 (1- loop-limit) loop-args))
			     (setf i (skip-iteration control-string (1+ i)))))))))
	      (#\} (if (and args
			    (or (not loop-limit)
				(not (zerop loop-limit))))
		       (setf loop-limit (and loop-limit (1- loop-limit))
			     i (1- start))
		     (go end-loop)))
	      (#\^ (case (length prefix-parameters)
		     (0 (unless args
			  (go end-loop)))
		     (1 (when (zerop (first prefix-parameters))
			  (go end-loop)))
		     (2 (when (= (first prefix-parameters)
				 (second prefix-parameters))
			  (go end-loop)))
		     (3 (when (<= (first prefix-parameters)
				  (second prefix-parameters)
				  (third prefix-parameters))
			  (go end-loop)))
		     (t (error "format directive ~^ takes at most 3 parameters."))))
	      #+ignore
	      (#\( (multiple-value-setq (i args)
		     (format-by-string control-string (1+ i) loop-limit args
				       (cond
                                         ((and colon-p at-sign-p) :upcase)
					(colon-p :capitalize)
					(at-sign-p :capitalize-first)
					(t :downcase)))))
	      (#\? (if (not at-sign-p)
                       (format-by-string (pop args) 0 0 (pop args))
                       (setf args (nth-value 1 (format-by-string (pop args) 0 0 args)))))
	      (#\: (setf colon-p t)
		   (go proceed))
	      (#\@ (setf at-sign-p t)
		   (go proceed))
	      (#\, (push nil prefix-parameters)
		   (go proceed))
	      (#\V (push (pop args) prefix-parameters)
		   (go proceed))
	      (#\# (push (length args) prefix-parameters)
		   (go proceed))
	      (#\' (push (schar control-string (incf i)) prefix-parameters)
		   (when (char= #\, (schar control-string (1+ i)))
		     (incf i))
		   (go proceed))
	      ((#\+ #\- #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
	       (multiple-value-bind (value value-end)
		   (parse-integer control-string :start i :junk-allowed t)
		 (setf i (1- value-end))
		 (when (char= #\, (schar control-string value-end))
		   (incf i))
		 (push value prefix-parameters)
		 (go proceed)))
	      ))))
      (incf i)
      (go loop)
     end-loop)
    (values i args)))

	   
