;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      strings.lisp
;;;; Description:   String functions.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Oct 19 17:05:25 2001
;;;;                
;;;; $Id: strings.lisp,v 1.1 2004/01/13 11:05:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/arrays)
(require :muerte/characters)
(provide :muerte/strings)

(in-package muerte)

(defun string= (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (setf string1 (string string1)
	end1 (or end1 (length string1))
	string2 (string string2)
	end2 (or end2 (length string2)))
  (and (= (- end1 start1) (- end2 start2))
       (do ((i start1 (1+ i))
	    (j start2 (1+ j)))
	   ((>= i end1) t)
	 (unless (char= (schar string1 i) (schar string2 j))
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
	 (unless (char-equal (schar string1 i) (schar string2 j))
	   (return nil)))))

(defun string-not-equal (string1 string2 &key (start1 0) end1 (start2 0) end2)
  (not (string-equal string1 string2 :start1 start1 :end1 end1 :start2 start2 :end2 end2)))

(defun string (name)
  (typecase name
    (string name)
    (symbol (symbol-name name))
    (character (make-string 1 :initial-element name))
    (t (error "Not a string designator: ~S" name))))
	    
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
      (setf (schar cased-string i)
	(char-upcase (schar string (+ i start)))))
    cased-string))

(defun string-downcase (string &key (start 0) (end (length string)))
  (let* ((length (- end start))
	 (cased-string (make-string length)))
    (dotimes (i length)
      (setf (schar cased-string i)
	(char-downcase (schar string (+ i start)))))
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
      (setf (schar capitalized-string j)
	(let ((c (schar string i)))
	  (cond
	   ((and between-words-p (char-alpha-p c))
	    (setf between-words-p nil)
	    (char-upcase c))
	   (t (setf between-words-p (not (char-alpha-p c)))
	      (char-downcase c))))))))
				
       
      
