;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2000-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      textmode.lisp
;;;; Description:   A primitive VGA text-mode console driver.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Nov  9 15:38:56 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: textmode.lisp,v 1.18 2008-03-15 20:58:30 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

;; (require :common-lisp)

(require :x86-pc/vga)
(require :x86-pc/package)
(require :x86-pc/keyboard)
(require :lib/package)
(provide :x86-pc/textmode)

(in-package muerte.x86-pc)

(defvar *text-output-port* nil
  "Output all text also to this port. For example, bochs #xe9 port hack.")

(defvar *screen* 
    (vga-memory-map))

(defvar *screen-width*
    (vga-horizontal-display-end))

(defvar *screen-stride*
    (vga-horizontal-display-end))

(defvar *cursor-x*
    (rem (vga-cursor-location) *screen-stride*))

(defvar *cursor-y*
    (truncate (vga-cursor-location) *screen-stride*))

(defvar *screen-height*
    (truncate (vga-vertical-display-end)
	      (vga-character-height)))

(defun move-vga-cursor (x y)
  (let ((dest (+ x (* y *screen-stride*))))
    (setf (vga-cursor-location) dest)))

(defun cursor-row (&optional device)
  (declare (ignore device))
  *cursor-y*)

(defun (setf cursor-row) (value &optional device)
  (declare (ignore device))
  (setf *cursor-y* value)
  (move-vga-cursor *cursor-x* value)
  value)

(defun cursor-column (&optional device)
  (declare (ignore device))
  *cursor-x*)

(defun (setf cursor-column) (value &optional device)
  (declare (ignore device))
  (setf *cursor-x* value)
  (move-vga-cursor value *cursor-y*)
  value)

(defun textmode-write-char (c)
  (when *text-output-port*
    (setf (io-port *text-output-port* :unsigned-byte8) (char-code c)))
  (case c
    (#\newline
     (setf *cursor-x* 0)
     (move-vga-cursor 0 *cursor-y*)
     (cond
      ((>= (1+ *cursor-y*) *screen-height*)
       (textmode-scroll-down)
       (setf *cursor-y* (1- *screen-height*)))
      (t (incf *cursor-y*))))
    (#\backspace
     (if (/= 0 *cursor-x*)
	 (decf *cursor-x*)
       (progn
	 (decf *cursor-y*)
	 (setf *cursor-x* (1- *screen-width*))))
     (move-vga-cursor *cursor-x* *cursor-y*))
    (#\return
      (setf *cursor-x* 0)
      (move-vga-cursor 0 *cursor-y*))
    (#\tab
     (textmode-write-char #\space)
     (do () ((zerop (rem *cursor-x* 8)))
       (textmode-write-char #\space)))
    (t (let ((x *cursor-x*)
	     (y *cursor-y*))
	 (when (>= x *screen-width*)
	   (textmode-write-char #\newline)
	   (setf x *cursor-x* y *cursor-y*))
	 (setf (memref-int *screen* :index (+ x (* y *screen-stride*)) :type :unsigned-byte16)
	   (logior #x0700 (char-code c)))
	 (move-vga-cursor (setf *cursor-x* (1+ x)) y))))
  nil)

#+ignore
(defun textmode-copy-line (destination source count)
  (check-type count (and (integer 0 511) (satisfies evenp)))
  (check-type source (unsigned-byte 20))
  (check-type destination (unsigned-byte 20))
  (with-inline-assembly (:returns :nothing)
    (:compile-form (:result-mode :eax) source)
    (:compile-form (:result-mode :edx) destination)
    (:compile-form (:result-mode :ebx) count)
    (:std)				; Only EBX is now (potential) GC root
    (:andl #x-8 :ebx)			; ..so make sure EBX is a fixnum
    (:shrl 2 :eax)
    (:shrl 2 :edx)
    (:shrl 1 :ebx)
    (:jz 'end-copy-loop)
   copy-loop
    (#.movitz:*compiler-physical-segment-prefix* :movl (:eax :ebx -4) :ecx)
    (#.movitz:*compiler-physical-segment-prefix* :movl :ecx (:edx :ebx -4))
    (:subl 4 :ebx)
    (:ja 'copy-loop)
   end-copy-loop
    (:cld)))

(defun textmode-scroll-down ()
  (declare (special muerte.lib::*scroll-offset*))
  (incf muerte.lib::*scroll-offset*)
  (macrolet ((copy-line (destination source count)
	       `(let ((destination ,destination)
		      (source ,source)
		      (count ,count))
		  (with-inline-assembly (:returns :nothing)
		    (:compile-form (:result-mode :edx) destination)
		    (:compile-form (:result-mode :eax) source)
		    (:compile-form (:result-mode :ebx) count)
		    (:std)		; Only EBX is now (potential) GC root
		    (:andl #x-8 :ebx)	; ..so make sure EBX is a fixnum
		    (:shrl 2 :eax)
		    (:shrl 2 :edx)
		    (:shrl 1 :ebx)
		    (:jz 'end-copy-loop)
		   copy-loop
		    (#.movitz:*compiler-physical-segment-prefix* :movl (:eax :ebx -4) :ecx)
		    (#.movitz:*compiler-physical-segment-prefix* :movl :ecx (:edx :ebx -4))
		    (:subl 4 :ebx)
		    (:ja 'copy-loop)
		   end-copy-loop
		    (:cld)))))
    (loop with screen = (check-the fixnum *screen*)
	with stride = (* 2 *screen-stride*)
	with width = (check-the fixnum *screen-width*)
	with height = (1- (check-the fixnum *screen-height*))
	repeat height
	as src of-type fixnum from (+ screen stride) by stride
	as dst of-type fixnum from screen by stride
	do (copy-line dst src width)
	finally (textmode-clear-line 0 height)))
  (signal 'newline))

(defun textmode-clear-line (from-column line)
  (let ((dest (+ *screen* (* line *screen-width* 2) (* from-column 2))))
    (dotimes (i (- *screen-width* from-column))
      (setf (memref-int dest :index i :type :unsigned-byte16) #x0720))))
      
(defun write-word (word)
  (let ((dest (+ *screen* (* *cursor-x* 2) (* *cursor-y* *screen-width* 2))))
    (setf (memref-int dest :index 0 :type :unsigned-byte16) #x0723
	  (memref-int dest :index 1 :type :unsigned-byte16) #x0778)
    (write-word-lowlevel word (+ dest 4))
    (textmode-write-char #\newline)))

(defun write-word-nl (word)
  (let ((dest (+ *screen* (* *cursor-x* 2) (* *cursor-y* 160))))
    (setf (memref-int dest :index 0 :type :unsigned-byte16) #x0723
	  (memref-int dest :index 1 :type :unsigned-byte16) #x0778)
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

(define-compiler-macro write-word-lowlevel-macro (word dest)
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

       (,movitz:*compiler-physical-segment-prefix*
	:movl #x07000700 (:ebx 0))
       (,movitz:*compiler-physical-segment-prefix* :movl #x07000700 (:ebx 4))
       (,movitz:*compiler-physical-segment-prefix* :movl #x07000700 (:ebx 8))
       (,movitz:*compiler-physical-segment-prefix* :movl #x07000700 (:ebx 12))
       ,loop-label

       (:andl #x0f0f0f0f :eax)
       (:addl #x30303030 :eax)

       (:cmpb #x39 :al) (:jle ',l1) (:addb 7 :al)
       ,l1 (,movitz:*compiler-physical-segment-prefix* :movb :al (14 :ebx)) ; 8
       (:cmpb #x39 :ah) (:jle ',l2) (:addb 7 :ah)
       ,l2 (,movitz:*compiler-physical-segment-prefix* :movb :ah (10 :ebx)) ; 6

       (:shrl 16 :eax)
      
       (:cmpb #x39 :al) (:jle ',l3) (:addb 7 :al)
       ,l3 (,movitz:*compiler-physical-segment-prefix* :movb :al (6 :ebx))		; 4
       (:cmpb #x39 :ah) (:jle ',l4) (:addb 7 :ah)
       ,l4 (,movitz:*compiler-physical-segment-prefix* :movb :ah (2 :ebx))		; 2

       (:movl :edx :eax)
       (:shrl 4 :eax)
       (:subl 2 :ebx)
       (:decb :cl)
       (:jnz ',loop-label))))

(defun write-word-lowlevel (word dest)
  (write-word-lowlevel-macro word dest))

(defun e9-output (op &rest args)
  (declare (dynamic-extent args))
  (ecase op
    (muerte::stream-write-char
     (setf (io-port #xe9 :unsigned-byte8) (char-code (car args))))
    (muerte::stream-fresh-line
     (e9-output 'muerte::stream-write-char #\Newline)
     t)
    (local-echo-p
     nil)))

(defun textmode-console (op &rest args)
  "This function can act as *terminal-io* without/before CLOS support."
  (declare (dynamic-extent args))
  (case op
    (muerte::stream-write-char
     (textmode-write-char (car args)))
    (muerte::stream-fresh-line
     (when (plusp (cursor-column))
       (textmode-write-char #\Newline)
       t))
    (muerte::stream-read-char
     (loop when (muerte.x86-pc.keyboard:poll-char) return it))
    (muerte::stream-read-char-no-hang
     (muerte.x86-pc.keyboard:poll-char))
    (muerte::stream-read-key
     (loop when (muerte.x86-pc.keyboard:poll-key) return it))
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

  
(defun set-textmode (mode-state)
  (unless (= #xb8000 (vga-memory-map))
    (break "This is only likely to work on VGA based at #xb8000, yours is at ~S."
	   (vga-memory-map)))
  (setf (vga-state) mode-state)
  (ecase (vga-character-height)
    (8 (write-font +vga-font-8x8+ 8))
    (16 (write-font +vga-font-8x16+ 16)))
  (setf *screen-width*
    (vga-horizontal-display-end))
  (setf *screen-height*
    (truncate (vga-vertical-display-end)
	      (vga-character-height)))
  (setf *screen-stride*
    (vga-horizontal-display-end))
  (setf *cursor-x*
    (min (1- *screen-width*) *cursor-x*))
  (setf *cursor-y*
    (min (1- *screen-height*) *cursor-y*))
  (values))
