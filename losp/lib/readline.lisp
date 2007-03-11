;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      readline.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Nov  2 13:58:58 2001
;;;;                
;;;; $Id: readline.lisp,v 1.9 2007/03/11 22:43:46 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :common-lisp)
(require :lib/package)
(provide :lib/readline)

(defpackage muerte.readline
  (:use #:muerte.cl #:muerte.lib)
  (:export #:readline
	   #:readline-buffer
	   #:readline-keypress
	   #:readline-keypress-key
	   #:*readline-signal-keypresses*
	   #:make-readline-buffer
	   #:readline-buffer-string
	   #:readline-buffer-cursor-position
	   #:readline-buffer-cursor-end
	   #:make-readline-context
	   #:contextual-readline
	   #:complete-symbol-name))

(in-package muerte.readline)

(defvar *readline-signal-keypresses* nil)

(defun complete-symbol-name (string &key (start 0) (end (length string)) (collect-matches nil)
					 filter-matches (package *package*))
  "=> completion (a symbol), completion-count completion-start completion-end completion-collection.
completion-start and completion-end are bounding indexes into completion's name."
  (when (<= end start)
    (return-from complete-symbol-name (values nil 0)))
  (let ((colon-position (position #\: string :start start :end end :test #'char=)))
    (multiple-value-bind (symbol-start search-package acceptable-statuses)
	(cond
	 ((not colon-position)
	  (values start (find-package package) '(:inherited :external :internal)))
	 ((= start colon-position)
	  (values (1+ colon-position) (find-package :keyword) '(:external)))
	 ((and (< 1 (- end colon-position))
	       (char= #\: (char string (1+ colon-position))))
	  (values (+ 2 colon-position)
		  (find-package (string-upcase string :start start :end colon-position))
		  '(:external :internal)))
	 (t (values (1+ colon-position)
		    (find-package (string-upcase string :start start :end colon-position))
		    '(:external))))
      (if (not search-package)
	  nil
	(let ((count 0)
	      (symbol-length (- end symbol-start))
	      (match nil)
	      (match-end 0))
	  (flet ((symbol-status (symbol package)
		   (nth-value 1 (find-symbol (symbol-name symbol) package))))
	    (do-symbols (test-symbol search-package)
	      (when (or (not filter-matches)
			(funcall filter-matches test-symbol))
		(let* ((test-name (symbol-name test-symbol))
		       (test-length (length test-name)))
		  (cond
		   ((not match)		; first match?
		    (when (>= test-length symbol-length) ; test-symbol long enough?
		      ;; (warn "test-name1: ~S" test-name)
		      (let ((mismatch-position (mismatch string test-name
							 :start1 symbol-start :end1 end
							 :test #'char-equal)))
			(when (or (not mismatch-position)
				  (= mismatch-position end))
			  (when (member (symbol-status test-symbol search-package)
					acceptable-statuses)
			    (setf match test-symbol ;; test-name ; found first match
				  match-end test-length
				  count 1
				  collect-matches (and collect-matches (list test-symbol))))))))
		   ;; not first match, so see if this test-name restricts match further..
		   ((< test-length symbol-length)) ; no match
		   (t (let ((mismatch-position (mismatch (symbol-name match) test-name :end1 match-end)))
			(when (not mismatch-position)
			  (setq mismatch-position end))
			(when (and (>= mismatch-position symbol-length)
				   (when (member (symbol-status test-symbol search-package)
						 acceptable-statuses)))
			  (incf count)
			  (when collect-matches
			    (pushnew test-symbol collect-matches))
			  (when (< mismatch-position match-end)
			    (setf match-end mismatch-position))))))))))
	  (if match
	      (values match
		      count
		      (- end symbol-start)
		      match-end
		      collect-matches)
	    (values nil 0)))))))


(defstruct readline-buffer
  (cursor-position 0)
  (cursor-end 0)
  string)

(define-condition readline-keypress ()
  ((key
    :accessor readline-keypress-key
    :initarg :key)))

(defun readline (readline-buffer console &key (terminators '(#\newline)))
  (with-accessors ((buffer readline-buffer-string)
		   (pos readline-buffer-cursor-position)
		   (end readline-buffer-cursor-end))
      readline-buffer
    (let ((cursor-origin (cursor-x console)))
      (clear-line console (cursor-x console) (cursor-y console))
      (write-string buffer t :end end)
      (setf (cursor-x console) (+ cursor-origin pos)))
    (loop with previous-key-was-tab-p = nil
	and displayed-completions-p = nil
	as key = (muerte:read-key console)
	do (with-saved-excursion (console)
	     (when *readline-signal-keypresses*
	       (with-simple-restart (continue "Proceed with interactive READLINE.")
		 (signal 'readline-keypress :key key))))
	   (when (characterp key)
	     (unless (char= key #\tab)
	       (setf previous-key-was-tab-p nil))
	     (when (member key terminators)
	       (when displayed-completions-p
		 (do ((y (1+ (cursor-y console)) (1+ y)))
		     ((>= y (console-height console)))
		   (clear-line console 0 y)))
	       (return key))
	     (case key
	       (#\tab
		(when (plusp pos)
		  (let ((token-pos pos))
		    (do ()		; move to start of token
			((or (zerop token-pos)
			     (member (char buffer (1- token-pos))
				     '(#\space #\( #\) #\newline #\'))))
		      (decf token-pos))
		    (multiple-value-bind (completion completion-count completion-start
					  completion-end completion-collection)
			(complete-symbol-name
			 buffer
			 :start token-pos
			 :end pos
			 :collect-matches previous-key-was-tab-p
			 :filter-matches (if (and (< 0 token-pos)
						  (char= #\( (char buffer (1- token-pos)))
						  (not (and (< 1 token-pos)
							    (char= #\( (char buffer (- token-pos 2))))))
					     #'fboundp
					   nil))
		      ;; (warn "comp: ~S" completion-collection)
		      ;; move tail string forward
		      (when completion
			(let ((completion-length (- completion-end completion-start)))
			  (incf end completion-length)
			  (dotimes (i (- end pos completion-length))
			    (setf (char buffer (- end i 1))
			      (char buffer (- end i 1 completion-length))))
			  ;; insert completion
			  (loop for i from completion-start below completion-end
			      do (write-char 
				  (setf (char buffer pos) (char-downcase (char (symbol-name completion) i))))
			      do (incf pos))
			  (let ((x (cursor-x console)))
			    (write-string buffer t :start pos :end end)
			    (setf (cursor-x console) x))))
		      (when displayed-completions-p
			(do ((y (1+ (cursor-y console)) (1+ y)))
			    ((>= y (console-height console)))
			  (clear-line console 0 y))
			(setf displayed-completions-p nil))
		      (when previous-key-was-tab-p
			(with-saved-excursion (console)
			  (cond
			   ((null completion-collection)
			    (format t "~%No completions."))
			   ((< completion-count 20)
			    (format t "~%Completions:~{ ~A~}." completion-collection))
			   (t (format t "~%~D completions!" completion-count))))
			(setf displayed-completions-p t)))))
		(setf previous-key-was-tab-p (not previous-key-was-tab-p)))
	       ((:left #\^b)
		(unless (zerop pos)
		  (decf pos)
		  (decf (cursor-x console))))
	       (#\^a
		(decf (cursor-x console) pos)
		(setf pos 0))
	       ((:right #\^f)
		(when (< pos end)
		  (incf pos)
		  (incf (cursor-x console))))
	       (#\^e
		(incf (cursor-x console) (- end pos))
		(setf pos end))
	       ((:kill #\^k)
		(let ((x (cursor-x console)))
		  (dotimes (i (- end pos))
		    (write-char #\space))
		  (setf (cursor-x console) x
			end pos)))
	       ((#\Rubout #\^d)
		(when (< pos end)
		  (dotimes (i (- end pos))
		    (setf (char buffer (+ pos i))
		      (char buffer (+ pos i 1))))
		  (decf end)
		  (let ((x (cursor-x console)))
		    (write-string buffer t :start pos :end end)
		    (write-char #\space)
		    (setf (cursor-x console) x))))
	       (#\backspace
		(unless (zerop pos)
		  (decf pos)
		  (decf (cursor-x console))
		  (when (< pos end)
		    (dotimes (i (- end pos))
		      (setf (char buffer (+ pos i))
			(char buffer (+ pos i 1))))
		    (decf end)
		    (let ((x (cursor-x console)))
		      (write-string buffer t :start pos :end end)
		      (write-char #\space)
		      (setf (cursor-x console) x)))))
	       (t (when (and (characterp key)
			     (< 1 (- (console-width console)
				     (cursor-x console))))
		    (dotimes (i (- end pos))
		      (setf (char buffer (- end i))
			(char buffer (- end i 1))))
		    (setf (char buffer pos) key)
		    (incf end)
		    (let ((x (cursor-x console)))
		      (write-string buffer t :start pos :end end)
		      (setf (cursor-x console) (1+ x)))
		    (incf pos))))))))

(defstruct readline-context-state
  scratch
  current-buffer
  buffers)

(defun make-readline-context (&key (history-size 8) (line-length 128))
  (let ((context (make-readline-context-state
		  :current-buffer 0
		  :buffers (make-array history-size)
		  :scratch (make-readline-buffer :string (make-string line-length)))))
    (loop for i from 0 below history-size
	do (setf (aref (readline-context-state-buffers context) i)
	     (make-readline-buffer :string (make-string line-length))))
    context))

(defvar *global-readline-context-state* nil)

(defun replace-buffer (to from)
  (setf (readline-buffer-cursor-position to)
    (readline-buffer-cursor-position from))
  (setf (readline-buffer-cursor-end to)
    (readline-buffer-cursor-end from))
  (setf (fill-pointer (readline-buffer-string to))
    (array-dimension (readline-buffer-string to) 0))
  (replace (readline-buffer-string to)
	   (readline-buffer-string from))
  to)

(define-condition readline-break ()
  ((character
    :initarg :character
    :reader readline-break-character)))

(defun contextual-readline (context &key initial-contents initial-element
					 (initial-length (length initial-contents))
					 break-characters)
  ;; (check-type context readline-context-state)
  (with-accessors ((scratch readline-context-state-scratch)
		   (buffers readline-context-state-buffers)
		   (current-buffer readline-context-state-current-buffer))
      (or context
	  *global-readline-context-state*
	  (setf *global-readline-context-state*
	    (make-readline-context)))
    (let* ((edit-buffer current-buffer)
	   (buffer (readline-buffer-string (aref buffers edit-buffer))))
      (cond
       (initial-element
	(fill buffer initial-element 0 initial-length))
       (initial-contents
	(replace buffer initial-contents :end1 initial-length)))
      (setf (readline-buffer-cursor-end (aref buffers edit-buffer)) initial-length
	    (readline-buffer-cursor-position (aref buffers edit-buffer)) initial-length)
      (loop with cursor-origin = (cursor-x *standard-output*)
	  as terminator =
	    (readline (replace-buffer scratch (aref buffers edit-buffer))
		      *standard-output*
		      :terminators (append break-characters
					   '(#\^c #\newline #\^p #\^n :up :down)))
	  do (when (or (eql #\^c terminator)
		       (member terminator break-characters))
	       (signal 'readline-break :character terminator))
	     (case terminator
	       (#\newline
		(let* ((return-buffer (replace-buffer (aref buffers current-buffer) scratch))
		       (string (readline-buffer-string return-buffer))
		       (end (readline-buffer-cursor-end return-buffer))
		       (first-char (position-if (lambda (c)
						  (not (member c '(#\space #\tab #\newline))))
						string :end end)))
		  ;; remove whitespace at start of string
		  (cond
		   ((not first-char)
		    (setf end 0))
		   ((plusp first-char)
		    (replace string string :start2 first-char)
		    (decf end first-char)
		    (decf (readline-buffer-cursor-position return-buffer) first-char)))
		  (unless (zerop end)
		    (setf current-buffer (mod (1+ current-buffer) (length buffers))))
		  (setf (readline-buffer-cursor-end return-buffer) end
			(fill-pointer string) end)
		  (return-from contextual-readline
		    (values string end))))
	       ((#\^p :up)
		(replace-buffer (aref buffers edit-buffer) scratch)
		(setf (cursor-x *standard-output*) cursor-origin
		      edit-buffer (mod (1- edit-buffer) (length buffers))))
	       ((#\^n :down)
		(replace-buffer (aref buffers edit-buffer) scratch)
		(setf (cursor-x *standard-output*) cursor-origin
		      edit-buffer (mod (1+ edit-buffer) (length buffers))))
	       (t (warn "unknown terminator: ~S" terminator)))))))



