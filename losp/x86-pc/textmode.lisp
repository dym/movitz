;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001,2000, 2002-2004,
;;;;    Department of Computer Science, University of Tromsø, Norway
;;;; 
;;;; Filename:      textmode.lisp
;;;; Description:   A primitive 80x25 text-mode console driver.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Nov  9 15:38:56 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: textmode.lisp,v 1.1 2004/01/13 11:05:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

;; (require :common-lisp)

(require :x86-pc/vga)
(require :x86-pc/package)
(require :x86-pc/keyboard)
(require :lib/package)

(provide :x86-pc/textmode)

(defpackage muerte.x86-pc
  (:export textmode-console))

(in-package muerte.x86-pc)

(defconstant *screen* #xb8000)
(defconstant *screen-width* 80)
(defconstant *screen-height* 24)
(defconstant *screen-stride* 80)

(defparameter *cursor-x* (rem (vga-cursor-location) 80))
(defparameter *cursor-y* (truncate (vga-cursor-location) 80))
(defparameter *color* #x0700)

(defparameter *simple-console-state* 'initialized)

(defun move-vga-cursor (x y)
  (let ((dest (+ x (* y *screen-stride*))))
    (setf (vga-cursor-location) dest)))

(defun cursor-row (&optional device)
  (declare (ignore device))
  *cursor-y*)

(defun (setf cursor-row) (value &optional device)
  (declare (ignore device))
  (setf *cursor-y* value)
  (move-vga-cursor *cursor-x* *cursor-y*)
  value)

(defun cursor-column (&optional device)
  (declare (ignore device))
  *cursor-x*)

(defun (setf cursor-column) (value &optional device)
  (declare (ignore device))
  (setf *cursor-x* value)
  (move-vga-cursor *cursor-x* *cursor-y*)
  value)

(defun textmode-write-char (c)
  (cond
   #+ignore
   ((and (not (eq 'initialized *simple-console-state*))
	 (/= #xabba (memref-int #xb8000 0 0 :unsigned-byte16)))
    (setf (memref-int #xb8000 0 0 :unsigned-byte16) #xabba
	  (memref-int #xb8000 0 1 :unsigned-byte16) 4
	  (memref-int #xb8000 0 8 :unsigned-byte8) #x46 ; (char-code c)
	  (memref-int #xb8000 1 8 :unsigned-byte8) #xe0))
   #+ignore
   ((not (eq 'initialized *simple-console-state*))
    (let ((pos (memref-int #xb8000 0 1 :unsigned-byte16)))
      (when (< pos (* 80 25 2))
	(setf (memref-int #xb8000 0 (* 2 pos) :unsigned-byte8) (char-code c)
	      (memref-int #xb8000 1 (* 2 pos) :unsigned-byte8) #xe0
	      (memref-int #xb8000 0 1 :unsigned-byte16) (1+ pos)))))
   (t (case c
	(#\newline
	 (setf *cursor-x* 0)
	 (cond
	  ((= *screen-height* *cursor-y*)
	   (textmode-scroll-down)
	   (move-vga-cursor *cursor-x* *cursor-y*))
	  (t (incf *cursor-y*)
	     (move-vga-cursor *cursor-x* *cursor-y*))))
	(#\backspace
	 (if (/= 0 *cursor-x*)
	     (decf *cursor-x*)
	   (progn
	     (decf *cursor-y*)
	     (setf *cursor-x* (1- *screen-width*))))
	 (move-vga-cursor *cursor-x* *cursor-y*))
	(#\return
	  (setf *cursor-x* 0)
	  (move-vga-cursor *cursor-x* *cursor-y*))
	(#\tab
	 (textmode-write-char #\space)
	 (do () ((zerop (rem *cursor-x* 8)))
	   (textmode-write-char #\space)))
	(t (when (>= *cursor-x* *screen-width*)
	     (textmode-write-char #\newline))
	   (let ((index (+ *cursor-x* (* *cursor-y* *screen-stride*))))
	     (setf (memref-int *screen* 0 index :unsigned-byte16 t)
	       (logior #x0700 (char-code c)))
	     (incf *cursor-x*)
	     (move-vga-cursor *cursor-x* *cursor-y*))))))
  nil)

(defun textmode-scroll-down ()
  "Scroll the console down one line."
  (declare (special muerte.lib::*scroll-offset*))
  (incf muerte.lib::*scroll-offset*)
  (with-inline-assembly (:returns :nothing)
    (:movl #xb8000 :eax)
    (:movl #.(cl:+ #xb8000 160) :ebx)
    (:movl #.(cl:* 80 24 1) :ecx)
   copy-loop
    ((:gs-override) :movw (:ebx) :dx)
    ((:gs-override) :movw :dx (:eax))
    (:addl 2 :ebx)
    (:addl 2 :eax)
    (:subl 1 :ecx)
    (:jnz 'copy-loop)
    (:movl #.(cl:* 80 1) :ecx)
   clear-loop
    ((:gs-override) :movw #x0720 (:eax))
    (:addl 2 :eax)
    (:subl 1 :ecx)
    (:jnz 'clear-loop)))

  
(defun textmode-clear-line (from-column line)
  (let ((dest (+ *screen* (* line 80 2) (* from-column 2))))
    (dotimes (i (- 80 from-column))
      (setf (memref-int dest 0 i :unsigned-byte16 t) #x0720))
    #+ignore
    (with-inline-assembly (:returns :nothing)
      (:pushl :edi)
      (:compile-form (:result-mode :eax) dest)
      (:movl :eax :edi)
      (:shrl #.movitz:+movitz-fixnum-shift+ :edi)
      (:movl #.(cl:* 80 1) :ecx)
      (:movw #x0720 :ax)
      ((:repz) :stosw)
      (:popl :edi))))
      
(defun write-word (word)
  (let ((dest (+ *screen* (* *cursor-x* 2) (* *cursor-y* 160))))
    (setf (memref-int dest 0 0 :unsigned-byte16 t) #x0723
	  (memref-int dest 0 1 :unsigned-byte16 t) #x0778)
    (write-word-lowlevel word (+ dest 4))
    (textmode-write-char #\newline)))

(defun write-word-nl (word)
  (let ((dest (+ *screen* (* *cursor-x* 2) (* *cursor-y* 160))))
    (setf (memref-int dest 0 0 :unsigned-byte16 t) #x0723
	  (memref-int dest 0 1 :unsigned-byte16 t) #x0778)
    (write-word-lowlevel word (+ dest 4))))

(defun write-word-bottom (word)
  (write-word-lowlevel word #.(cl:+ #xb8000 (cl:* 24 160))))

(defun write-word-top (word)
  (write-word-lowlevel word #.(cl:+ #xb8000 (cl:* 0 160))))

(defun write-word-top2 (word)
  (write-word-lowlevel word #.(cl:+ 24 #xb8000 (cl:* 0 160))))

(defun write-word-bottom2 (word)
  (write-word-lowlevel word #.(cl:+ 96 #xb8000 (cl:* 24 160))))

(defun write-word-bottom3 (word)
  (write-word-lowlevel word #.(cl:+ 140 #xb8000 (cl:* 24 160))))

(defmacro write-word-lowlevel-macro (word dest)
  (let ((loop-label (make-symbol "write-word-loop"))
	(l1 (make-symbol "write-word-l1"))
	(l2 (make-symbol "write-word-l2"))
	(l3 (make-symbol "write-word-l3"))
	(l4 (make-symbol "write-word-l4")))
    `(with-inline-assembly (:returns :nothing)
       (:compile-two-forms (:eax :ebx) ,word ,dest)
       (:movl :eax :edx)

       (:shrl #.movitz:+movitz-fixnum-shift+ :ebx)
       (:movb 2 :cl)

       ((:gs-override) :movl #x07000700 (:ebx 0))
       ((:gs-override) :movl #x07000700 (:ebx 4))
       ((:gs-override) :movl #x07000700 (:ebx 8))
       ((:gs-override) :movl #x07000700 (:ebx 12))
       ,loop-label

       (:andl #x0f0f0f0f :eax)
       (:addl #x30303030 :eax)

       (:cmpb #x39 :al) (:jle ',l1) (:addb 7 :al)
       ,l1 ((:gs-override) :movb :al (14 :ebx)) ; 8
       (:cmpb #x39 :ah) (:jle ',l2) (:addb 7 :ah)
       ,l2 ((:gs-override) :movb :ah (10 :ebx))	; 6

       (:shrl 16 :eax)
      
       (:cmpb #x39 :al) (:jle ',l3) (:addb 7 :al)
       ,l3 ((:gs-override) :movb :al (6 :ebx))		; 4
       (:cmpb #x39 :ah) (:jle ',l4) (:addb 7 :ah)
       ,l4 ((:gs-override) :movb :ah (2 :ebx))		; 2

       (:movl :edx :eax)
       (:shrl 4 :eax)
       (:subl 2 :ebx)
       (:decb :cl)
       (:jnz ',loop-label))))

(defun write-word-lowlevel (word dest)
  (write-word-lowlevel-macro word dest))

(defun textmode-console (op &rest args)
  "This function can act as *terminal-io* without/before CLOS support."
  (declare (dynamic-extent args))
  (case op
    (muerte::stream-fresh-line
     (when (plusp (cursor-column))
       (textmode-write-char #\Newline)
       t))
    (muerte::stream-write-char
     (textmode-write-char (car args)))
    (muerte::stream-read-char
     (loop when (muerte.x86-pc.keyboard:poll-char) return it))
    (muerte::stream-read-char-no-hang
     (muerte.x86-pc.keyboard:poll-char))
    (cursor-x (cursor-column))
    (cursor-y (cursor-row))
    (console-width *screen-width*)
    (console-height *screen-height*)
    (clear-line
     (textmode-clear-line (car args) (cadr args)))
    (scroll-down
     (textmode-scroll-down))
    (local-echo-p
     nil)
    (t (cond
	((and (listp op) (eq 'setf (car op)))
	 (case (cadr op)
	   (cursor-x (setf (cursor-column) (car args)))
	   (cursor-y (setf (cursor-row) (car args)))))
	(t (error "Unknown op: ~S" op))))))
