;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      keyboard.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Sep 24 16:04:12 2001
;;;;                
;;;; $Id: keyboard.lisp,v 1.4 2004/11/24 16:20:14 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/named-integers)
(provide :x86-pc/keyboard)

(defpackage muerte.x86-pc.keyboard
  (:use muerte.cl muerte muerte.lib muerte.x86-pc)
  (:export poll-char
	   ;; read-char
	   poll-keypress
	   read-keypress
	   poll-key
	   set-leds
	   cpu-reset))

(in-package muerte.x86-pc.keyboard)

(defvar *scan-codes-shift*
    #(#\null   nil      #\!      #\@      #\#      #\$      #\%      #\^ ; #x00
      #\&      #\*      #\(      #\)      #\_      #\+      nil      nil ; #x08
      #\Q      #\W      #\E      #\R      #\T      #\Y      #\U      #\I ; #x10
      #\O      #\P      #\{      #\}     #\newline nil      #\A      #\S ; #x18
			       
      #\D      #\F      #\G      #\H      #\J      #\K      #\L      #\: ; #x20
      #\"      #\~      nil      #\|      #\Z      #\X      #\C      #\V ; #x28
      #\B      #\N      #\M      #\<      #\>      #\?      nil      nil ; #x30
      nil      nil      nil      nil      nil      nil      nil      nil ; #x38
      nil      nil      nil      nil      nil    :pause     nil      nil)) ; #x40

(defparameter *scan-codes*
    #(#\null   #\esc    #\1      #\2      #\3      #\4      #\5      #\6 ; #x00
      #\7      #\8      #\9      #\0      #\-      #\= #\backspace #\tab ; #x08
      #\q      #\w      #\e      #\r      #\t      #\y      #\u      #\i ; #x10
      #\o      #\p      #\[      #\]   #\newline :ctrl-left #\a      #\s ; #x18
			       
      #\d      #\f      #\g      #\h      #\j      #\k      #\l      #\; ; #x20
      #\'      #\`   :shift-left #\\      #\z      #\x      #\c      #\v ; #x28
      #\b      #\n      #\m      #\,      #\.      #\/  :shift-right #\esc ; #x30
      :alt-left #\space :caps-lock :f1    :f2      :f3      :f4      :f5 ; #x38
			       
      :f6      :f7      :f8      :f9      :f10   :break :scroll-lock nil ; #x40
      nil      nil      nil      nil      nil      nil      nil      nil ; #x48
      nil      :kp-ins  nil      :kp-del  nil      nil      nil      :f11 ; #x50
      :f12     nil      nil      nil      nil      nil      nil      nil ; #x58
      			       
      nil      nil      nil      nil      nil      nil      nil      nil ; #x60
      nil      nil      nil      nil      nil      nil      nil      nil ; #x68
      nil      nil      nil      nil      nil      nil      nil      nil ; #x70
      nil      nil      nil      nil      nil      nil      nil      nil ; #x78
			       
      nil      nil      nil      nil      nil      nil      nil      nil ; #x80
      nil      nil      nil      nil      nil      nil      nil      nil ; #x88
      nil      nil      nil      nil   :ctrl-right nil      nil      nil ; #x90
      nil      nil      nil      nil      nil  :ctrl-right  nil      nil ; #x98
      			       
      nil      nil      nil      nil      nil      nil      nil      nil ; #xa0
      nil      nil      nil      nil      nil      nil      nil      nil ; #xa8
      nil      nil      nil      nil      nil      nil      nil      nil ; #xb0
      :alt-right nil    nil      nil      nil      nil      nil      nil ; #xb8

      nil      nil      nil      nil      nil      nil      nil    :home ; #xc0
      :up      :page-up nil      :left    nil      :right   nil     :end ; #xc8
      :down  :page-down :insert  #\delete nil      nil      nil      nil ; #xd0
      :alt-right nil    nil      nil      :win     :menu    nil      nil)) ; #xd8

(defun lowlevel-event-p ()
  (logbitp 0 (io-port #x64 :unsigned-byte8)))

(defun keyboard-ack ()
  (prog1 (io-port #x60 :unsigned-byte8)
    (let ((x (io-port #x61 :unsigned-byte8)))
      (setf (io-port #x61 :unsigned-byte8) (logior x #x80)
	    (io-port #x61 :unsigned-byte8) (logand x #x7f)))
    (muerte.x86-pc::pic8259-end-of-interrupt 1)))

(defun test-kbd ()
  (print (keyboard-ack))
  (let ((a (io-port #x61 :unsigned-byte8)))
    (setf (io-port #x61 :unsigned-byte8) (logior a #x80)
	  (io-port #x61 :unsigned-byte8) a))
  (io-delay 500000))

(defun lowlevel-read ()
  "Read a keyboard event. Return two values:
The scan-code, with bit 7 set if it was an extended (#xe0) code.
Secondly, whether this was a release event is returned."
  (let ((first-code (io-port #x60 :unsigned-byte8)))
    (case first-code
      (#xe0
       ;; (warn "e0")
       (let ((second-code (progn
			    (loop until (logbitp 0 (io-port #x64 :unsigned-byte8)))
			    (io-port #x60 :unsigned-byte8))))
	 (values (logior #x80 second-code)
		 (logbitp 7 second-code))))
      (#xe1				; XXX
       (loop until (logbitp 0 (io-port #x64 :unsigned-byte8)))
       (io-port #x60 :unsigned-byte8)
       (loop until (logbitp 0 (io-port #x64 :unsigned-byte8)))
       (io-port #x60 :unsigned-byte8))
      (t (values (ldb (byte 7 0) first-code)
		 (logbitp 7 first-code))))))

(define-named-integer qualifier (:only-constants t)
  (0 shift)
  (1 ctrl)
  (2 alt))

(defvar *qualifier-state* 0)

(defconstant +qualifier-map+
    #(nil				; 0
      (:shift)				; 1
      (:ctrl)				; 2
      (:shift :ctrl)			; 3
      (:alt)				; 4
      (:shift :alt)			; 5
      (:ctrl :alt)			; 6
      (:shift :ctrl :alt)))		; 7

(defun decode-qualifier-state (state)
  (svref #(nil				; 0
	   (:shift)			; 1
	   (:ctrl)			; 2
	   (:shift :ctrl)		; 3
	   (:alt)			; 4
	   (:shift :alt)		; 5
	   (:ctrl :alt)			; 6
	   (:shift :ctrl :alt))
	 state))

(defun qualifier-p (qualifier qualifier-state)
  (if (member qualifier (decode-qualifier-state qualifier-state))
      t
    nil))

(defun decode-key-code (key-code qualifiers)
  (or (and (logbitp +qualifier-shift+ qualifiers)
	   (< -1 key-code (length *scan-codes-shift*))
	   (aref *scan-codes-shift* key-code))
      (and (< -1 key-code (length *scan-codes*))
	   (aref *scan-codes* key-code))))
;;;  (< -1 key-code (length *scan-codes*)))

(defun get-key ()
  (when (lowlevel-event-p)
    (multiple-value-bind (key-code release-p)
	(lowlevel-read)
      (let ((key (or (decode-key-code key-code *qualifier-state*)
		     key-code)))
	(case key
	  ((:ctrl-left :ctrl-right)
	   (setf (ldb (byte 1 +qualifier-ctrl+) *qualifier-state*)
	     (if release-p 0 1)))
	  ((:shift-left :shift-right)
	   (setf (ldb (byte 1 +qualifier-shift+) *qualifier-state*)
	     (if release-p 0 1)))
	  ((:alt-left :alt-right)
	   (setf (ldb (byte 1 +qualifier-alt+) *qualifier-state*)
	     (if release-p 0 1))))
	(values key release-p)))))

(defun poll-keypress ()
  (multiple-value-bind (key release-p)
      (get-key)
    (unless release-p
      (values key *qualifier-state*))))

(defun read-keypress (&optional device)
  (declare (ignore device))
  (loop for key = (poll-keypress)
      when key
      return (values key *qualifier-state*)))

(defun poll-char ()
  (multiple-value-bind (key qualifiers)
      (poll-keypress)
    (cond
     ((not key) nil)
     ((symbolp key)
      (case key
	(:up #\^p)
	(:down #\^n)
	(:left #\^b)
	(:right #\^f)))
     ((not (characterp key))
      nil)
     ((and (qualifier-p :ctrl qualifiers)
	   (char<= #\a (char-downcase key) #\z))
      (code-char (+ (char-code #\^a)
		    (char-code (char-downcase key))
		    (- (char-code #\a)))))
     (t key))))

(defun poll-key ()
  (multiple-value-bind (key qualifiers)
      (poll-keypress)
    (if (and (characterp key)
	     (qualifier-p :ctrl qualifiers)
	     (char<= #\a (char-downcase key) #\z))
	(code-char (+ (char-code #\^a)
		      (char-code (char-downcase key))
		      (- (char-code #\a))))
      key)))

(defun set-leds (led0 led1 led2)
  (loop while (logbitp 1 (io-port #x64 :unsigned-byte8)))
  (setf (io-port #x60 :unsigned-byte8) #xed)
  (loop while (logbitp 1 (io-port #x64 :unsigned-byte8)))
  (setf (io-port #x60 :unsigned-byte8) (logior (if led0 2 0) (if led1 4 0) (if led2 1 0))))

(defun cpu-reset ()
  (loop for temp = (io-port #x64 :unsigned-byte8)
      do (when (logbitp 0 temp)
	   (io-port #x60 :unsigned-byte8))
      while (logbitp 1 temp)
      finally (setf (io-port #x64 :unsigned-byte8) #xfe)))


  
