;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      textmode-console.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Jul  8 15:13:24 2003
;;;;                
;;;; $Id: textmode-console.lisp,v 1.5 2005/05/05 15:17:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/console)
(require :x86-pc/textmode)
(provide :x86-pc/textmode-console)

(in-package muerte.x86-pc)

(defclass vga-text-console (console stream)
  ((base
    :initform (vga-memory-map)
    :initarg :base
    :reader base)
   (stride
    :initarg :stride
    :reader stride)
   (color
    :initarg :color
    :initform 7
    :accessor color))
  (:default-initargs :width 80 :height 25 :stride 80
		     :cursor-x (rem (vga-cursor-location) 80)
		     :cursor-y (truncate (vga-cursor-location) 80)))

(defmethod cursor-x ((console vga-text-console))
  (rem (vga-cursor-location) (stride console)))

(defmethod cursor-y ((console vga-text-console))
  (truncate (vga-cursor-location) (stride console)))

(defmethod (setf cursor-x) (x (console vga-text-console))
  (let ((stride (stride console)))
    (setf (vga-cursor-location)
      (+ (* stride (cursor-y console))
	 (max x (1- (console-width console))))))
  x)

(defmethod (setf cursor-y) (y (console vga-text-console))
  (let ((stride (stride console)))
    (setf (vga-cursor-location)
      (+ (* stride (max y (1- (console-height console))))
	 (cursor-x console))))
  y)

#+ignore
(defmethod clear-line ((console vga-text-console) line &optional (from-column 0))
  (let ((dest (+ (base console)
		 (* line (console-width console) 2)
		 (* from-column 2))))
    (dotimes (i (- (console-width console) from-column))
      (setf (memref-int dest :index i :type :unsigned-byte16) #x0720))
    nil))

(defmethod (setf console-char) (character (console vga-text-console) x y)
  (when (and (< x (console-width console))
	     (< y (console-height console)))
    (let ((index (+ x (* y (stride console)))))
      (setf (memref-int (base console) :index index :type :unsigned-byte16)
	(logior (ash (color console) 8) (char-code character)))))
  character)

(defmethod console-char ((console vga-text-console) x y)
  (when (and (< x (console-width console))
	     (< y (console-height console)))
    (let* ((index (+ x (* y (stride console))))
	   (code (memref-int (base console) :index index :type :unsigned-byte16)))
      (code-char (ldb (byte 8 0) code)))))

(defmethod put-string ((console vga-text-console) string x y
		       &optional (start 0) (end (length string)))
  (when (< y (console-height console))
    (loop with color = (ash (color console) 8) with base = (base console)
	for cursor upfrom (+ x (* y (stride console)))
	for column from x below (console-width console)
	for i from start below end
	as character = (char string i)
	do (setf (memref-int base :index cursor :type :unsigned-byte16)
	     (logior color (char-code character)))))
  string)

(defmethod clear-line ((console vga-text-console) x y)
  (when (< y (console-height console))
    (loop with base = (base console)
	for index upfrom (+ x (* y (stride console)))
	for column from x below (console-width console)
	do (setf (memref-int base :index index :type :unsigned-byte16)
	     #x0720))))

(defmethod scroll-down ((console vga-text-console))
  (loop with ystride = (* 2 (stride console))
      for y below (console-height console)
      for row from (base console) by ystride
      do (loop with next-row = (+ row ystride)
	     for x below (console-width console)
	     do (setf (memref-int row :index x :type :unsigned-byte16)
		  (memref-int next-row :index x :type :unsigned-byte16))))
  nil)

(defmethod stream-read-char ((stream vga-text-console))
  (loop for char = (muerte.x86-pc.keyboard:poll-char) when char return it))

