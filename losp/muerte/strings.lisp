;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      strings.lisp
;;;; Description:   String functions.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 19 17:05:25 2001
;;;;                
;;;; $Id: strings.lisp,v 1.6 2008-04-27 19:45:33 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/arrays)
(require :muerte/characters)
(provide :muerte/strings)

(in-package muerte)

(deftype string-designator ()
  '(or string symbol character))

(defun string= (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (setf string1 (string string1)
	end1 (or end1 (length string1))
	string2 (string string2)
	end2 (or end2 (length string2)))
  (and (= (- end1 start1) (- end2 start2))
       (do ((i start1 (1+ i))
	    (j start2 (1+ j)))
	   ((>= i end1) t)
	 (unless (char= (char string1 i) (char string2 j))
	   (return nil)))))

(defun string/= (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (not (string= string1 string2 :start1 start1 :end1 end1 :start2 start2 :end2 end2)))

(defun string-equal (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (setf string1 (string string1)
	end1 (or end1 (length string1))
	string2 (string string2)
	end2 (or end2 (length string2)))
  (and (= (- end1 start1) (- end2 start2))
       (do ((i start1 (1+ i))
	    (j start2 (1+ j)))
	   ((>= i end1) t)
	 (unless (char-equal (char string1 i) (char string2 j))
	   (return nil)))))

(defun string-not-equal (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (not (string-equal string1 string2
		     :start1 start1
		     :end1 end1
		     :start2 start2
		     :end2 end2)))

(defun string (name)
  (typecase name
    (string name)
    (symbol (symbol-name name))
    (character (make-string 1 :initial-element name))
    (t (error 'type-error
              :datum name
              :expected-type 'string-designator))))
	    
(defun make-string (size &key initial-element (element-type 'character))
  (if (not initial-element)
      (make-array size :element-type element-type)
    (progn
      (check-type initial-element character)
      (make-array size :initial-element initial-element :element-type element-type))))

(defun string-upcase (string &key (start 0) (end (length string)))
  (let* ((length (- end start))
	 (cased-string (make-string length)))
    (dotimes (i length)
      (setf (char cased-string i)
	(char-upcase (char string (+ i start)))))
    cased-string))

(defun string-downcase (string &key (start 0) (end (length string)))
  (let* ((length (- end start))
	 (cased-string (make-string length)))
    (dotimes (i length)
      (setf (char cased-string i)
	(char-downcase (char string (+ i start)))))
    cased-string))

(defun string-capitalize (string &key (start 0) end)
  (unless end (setf end (length string)))
  (flet ((char-alpha-p (c)
	   (char/= (char-upcase c) (char-downcase c))))
    (do* ((capitalized-string (make-string (- end start)))
	  (i start (1+ i))
	  (j 0 (1+ j))
	  (between-words-p t))
	((>= i end) capitalized-string)
      (setf (char capitalized-string j)
	(let ((c (char string i)))
	  (cond
	   ((and between-words-p (char-alpha-p c))
	    (setf between-words-p nil)
	    (char-upcase c))
	   (t (setf between-words-p (not (char-alpha-p c)))
	      (char-downcase c))))))))
				
(defun string< (string1 string2 &key (start1 0) end1 (start2 0) end2)
  "=> mismatch-index"
  (let ((mismatch (mismatch string1 string2
			    :start1 start1
			    :end1 end1
			    :start2 start2
			    :end2 end2
			    :test #'char=)))
    (cond
      ((not mismatch)
       nil)
      ((>= mismatch
	   (or end1 (length string1)))
       mismatch)
      ((>= (+ start2 mismatch)
	   (or end2 (length string2)))
       nil)
      (t (when (char< (char string1 mismatch)
		      (char string2 (+ start2 mismatch)))
	   mismatch)))))

(defun string<= (string1 string2 &key (start1 0) end1 (start2 0) end2)
  "=> mismatch-index"
  (let ((mismatch (mismatch string1 string2
			    :start1 start1
			    :end1 end1
			    :start2 start2
			    :end2 end2
			    :test #'char=)))
    (cond
      ((not mismatch)
       (or end1 (length string1)))
      ((>= mismatch
	   (or end1 (length string1)))
       mismatch)
      ((>= (+ start2 mismatch)
	   (or end2 (length string2)))
       nil)
      (t (when (char<= (char string1 mismatch)
		       (char string2 (+ start2 mismatch)))
	   mismatch)))))

(defun string> (string1 string2 result= start1 end1 start2 end2)
  "=> mismatch-index"
  (let ((mismatch (mismatch string1 string2
			    :start1 start1
			    :end1 end1
			    :start2 start2
			    :end2 end2
			    :test #'char=)))
    (cond
      ((not mismatch)
       nil)
      ((>= mismatch
	   (or end1 (length string1)))
       mismatch)
      ((>= (+ start2 mismatch)
	   (or end2 (length string2)))
       nil)
      (t (when (char> (char string1 mismatch)
		      (char string2 (+ start2 mismatch)))
	   mismatch)))))

(defun string>= (string1 string2 result= start1 end1 start2 end2)
  "=> mismatch-index"
  (let ((mismatch (mismatch string1 string2
			    :start1 start1
			    :end1 end1
			    :start2 start2
			    :end2 end2
			    :test #'char=)))
    (cond
      ((not mismatch)
       (or end1 (length string1)))
      ((>= mismatch
	   (or end1 (length string1)))
       mismatch)
      ((>= (+ start2 mismatch)
	   (or end2 (length string2)))
       nil)
      (t (when (char>= (char string1 mismatch)
		       (char string2 (+ start2 mismatch)))
	   mismatch)))))
