;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      characters.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Feb  5 19:05:01 2001
;;;;                
;;;; $Id: characters.lisp,v 1.7 2009-07-19 18:51:26 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(provide :muerte/characters)

(in-package muerte)

(defconstant char-code-limit #x10000)

(defun char-code (character)
  "Return a characters integer code."
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) character)
    (:cmpb #.(movitz::tag :character) :al)
    (:jne '(:sub-program (not-a-character) (:int 66)))
    (:shrl #.(cl:- 8 movitz::+movitz-fixnum-shift+) :eax)))

(defun char-int (c)
  (char-code c))

(defun code-char (code)
  (with-inline-assembly (:returns :eax)
    (:compile-form (:result-mode :eax) code)
    (:testb #.movitz::+movitz-fixnum-zmask+ :al)
    (:jnz '(:sub-program (not-fixnum) (:int 64)))
    (:shll #.(cl:- 8 movitz::+movitz-fixnum-shift+) :eax)
    (:movb #.(movitz::tag :character) :al)))

(define-compiler-macro char=%2op (x y)
  `(eq ,x ,y))				; should we make sure x and y are
					; in fact characters??

(define-compiler-macro char= (&whole form first-character &rest characters)
  (case (length characters)
    (0 t)
    (1 `(eql ,first-character ,(first characters)))
    (t form)))

(defun char= (first-character &rest characters)
  (numargs-case
   (2 (x y)
      (eql x y))
   (t (first-character &rest characters)
      (declare (dynamic-extent characters))
      (dolist (c characters t)
	(unless (char= c first-character)
	  (return nil))))))

(defun char/= (first-character &rest characters)
  (numargs-case
   (1 (x) (declare (ignore x)) t)
   (2 (x y) (not (eql x y)))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (do ((c first-character (pop more-characters)))
          ((null more-characters) t)
        (when (member c more-characters)
          (return nil))))))

(defmacro/cross-compilation define-char-cmp (name mode not-branch)
  `(defun ,name (first-character &rest more-characters)
     (numargs-case
      (1 (x) (declare (ignore x)) t)
      (2 (x y)
	 (with-inline-assembly (:returns ,mode)
	   (:compile-form (:result-mode :eax) x)
	   (:compile-form (:result-mode :ebx) y)
	   (:cmpb ,(movitz::tag :character) :al)
	   (:jne '(:sub-program (x-not-char)
		   (:int 69)))
	   (:cmpb ,(movitz::tag :character) :bl)
	   (:jne '(:sub-program (y-not-char)
		   (:movl :ebx :eax)
		   (:int 69)))
	   (:cmpl :ebx :eax)))
      (3 (x y z)
	 (with-inline-assembly (:returns ,mode)
	   (:compile-form (:result-mode :eax) x)
	   (:compile-form (:result-mode :ebx) y)
	   (:cmpb ,(movitz::tag :character) :al)
	   (:jne 'x-not-char)
	   (:cmpb ,(movitz::tag :character) :bl)
	   (:jne 'y-not-char)
	   (:cmpl :ebx :eax)
	   (,not-branch 'done)
	   (:compile-form (:result-mode :eax) z)
	   (:cmpb ,(movitz::tag :character) :al)
	   (:jne 'x-not-char)
	   (:cmpl :eax :ebx)
	  done))
      (t (first-character &rest characters)
	 (declare (dynamic-extent characters))
	 (if (null characters)
	     t
	   (and (,name first-character (first characters))
		(do ((c characters (cdr c)))
		    ((null (cdr c)) t)
		  (unless (,name (first c) (second c))
		    (return nil)))))))))

(define-char-cmp char<= :boolean-less-equal :jg)
(define-char-cmp char< :boolean-less :jge)
(define-char-cmp char>= :boolean-greater-equal :jl)
(define-char-cmp char> :boolean-greater :jle)

(defun char-upcase (c)
  (if (char<= #\a c #\z)
      (code-char (- (char-code c) 32))
    c))

(defun char-downcase (c)
  (if (char<= #\A c #\Z)
      (code-char (+ (char-code c) 32))
    c))

(defun upper-case-p (c)
  (char<= #\A c #\Z))

(defun lower-case-p (c)
  (char<= #\a c #\z))

(defun both-case-p (c)
  (alpha-char-p c))


(defun char-equal (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (char= (char-upcase x) (char-upcase y)))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (let ((f (char-upcase first-character)))
	(dolist (c more-characters t)
	  (unless (char= f (char-upcase c))
	    (return nil)))))))

(defun char-not-equal (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (not (char= (char-upcase x) (char-upcase y))))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (not (apply #'char-equal first-character more-characters)))))

(defun char-lessp (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (char< (char-upcase x)
	     (char-upcase y)))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (let ((x (char-upcase first-character)))
	(dolist (y more-characters t)
	  (unless (char< x (setf x (char-upcase y)))
	    (return nil)))))))

(defun char-not-lessp (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (not (char< (char-upcase x)
		  (char-upcase y))))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (not (apply #'char-lessp first-character more-characters)))))

(defun char-greaterp (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (char> (char-upcase x)
	     (char-upcase y)))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (let ((x (char-upcase first-character)))
	(dolist (y more-characters t)
	  (unless (char> x (setf x (char-upcase y)))
	    (return nil)))))))

(defun char-not-greaterp (first-character &rest more-characters)
  (numargs-case
   (1 (x)
      (declare (ignore x))
      t)
   (2 (x y)
      (not (char> (char-upcase x)
		  (char-upcase y))))
   (t (first-character &rest more-characters)
      (declare (dynamic-extent more-characters))
      (not (apply #'char-greaterp first-character more-characters)))))

(defun standard-char-p (c)
  "CLHS 2.1.3 Standard Characters"
  (or (char<= #\A (char-upcase c) #\Z)
      (char<= #\0 c #\9)
      (member c '(#\newline #\space
		  #\! #\$ #\" #\' #\( #\) #\, #\_ #\- #\. #\/ #\: #\; #\?
		  #\+ #\< #\= #\>
		  #\# #\% #\& #\* #\@ #\[ #\\ #\] #\{ #\| #\} #\` #\^ #\~))))

(defun alpha-char-p (c)
  (let ((x (char-code c)))
    (or (<= 65 x 90)
	(<= 97 x 122))))

(defun alphanumericp (c)
  (let ((x (char-code c)))
    (or (<= 65 x 90)
	(<= 97 x 122)
	(<= 48 x 57))))

(defun digit-char-p (char &optional (radix 10))
  "If CHAR is a digit under the base radix, return the digit value. Otherwise return NIL."
  (cond
   ((char<= #\0 char #\9)
    (let ((d (- (char-code char) (char-code #\0))))
      (and (< d radix) d)))
   ((and (> radix 10)
	 (char<= #\a (char-downcase char) #\z))
    (let ((d (- (char-code (char-downcase char)) (char-code #\a))))
      (and (< d (- radix 10))
	   (+ d 10))))))

(defun graphic-char-p (char)
  (and (not (char= char #\newline))
       (standard-char-p char)))
  

(defun digit-char (weight &optional (radix 10))
  "=> char"
  (cond
   ((not (below weight radix))
    nil)
   ((below weight 10)
    (code-char (+ #x30 weight)))
   (t (code-char (+ #x41 (- weight 10))))))


(defconstant +char-names+
    #("null" 
      "^a" "^b" "^c" "^d" "^e" "^f"
      "bel" "Backspace" "Tab" "Newline" "vt" "Page" "Return" 
      "^n" "^o" "^p" "^q" "^r" "^s"
      "^t" "^u" "^v" "^w" "^x" "^y"
      "^z" "esc" "^\\" "^]" "^^" "^_" "Space"))

(defun char-name (character)
  (when (below (char-code character) (length +char-names+))
    (svref +char-names+ (char-code character))))

(defun name-char (name &optional (start 0) (end (length name)))
  (dotimes (i (length +char-names+))
    (when (string-equal name (svref +char-names+ i) :start1 start :end1 end)
      (return (code-char i)))))

(defun char-whitespace-p (character)
  (or (char= character #\Space)
      (char= character #\Return)
      (char= character #\Tab)
      (char= character #\Linefeed)))

(defun character (c)
  (etypecase c
    (character c)
    ((string 1)
     (char c 0))
    (symbol
     (character (symbol-name c)))))


