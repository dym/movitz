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
;;;; $Id: keyboard.lisp,v 1.8 2007-03-31 21:08:13 ffjeld Exp $
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
	   cpu-reset
           set-kbd-layout))

(in-package muerte.x86-pc.keyboard)


(defvar *layouts*
  '((:qwerty
     #(#\null   #\escape #\1      #\2      #\3      #\4      #\5      #\6 ; #x00
       #\7      #\8      #\9      #\0      #\-      #\= #\backspace #\tab ; #x08
       #\q      #\w      #\e      #\r      #\t      #\y      #\u      #\i ; #x10
       #\o      #\p      #\[      #\]   #\newline :ctrl-left #\a      #\s ; #x18
			       
       #\d      #\f      #\g      #\h      #\j      #\k      #\l      #\; ; #x20
       #\'      #\`   :shift-left #\\      #\z      #\x      #\c      #\v ; #x28
       #\b      #\n      #\m      #\,      #\.      #\/  :shift-right #\escape ; #x30
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
       :down  :page-down :insert  nil #+ignore #\delete nil nil      nil      nil      nil ; #xd0
       :alt-right nil    nil      nil      :win     :menu    nil      nil) ; #x40
     #(#\null   nil      #\!      #\@      #\#      #\$      #\%      #\^ ; #x00
       #\&      #\*      #\(      #\)      #\_      #\+      nil      nil ; #x08
       #\Q      #\W      #\E      #\R      #\T      #\Y      #\U      #\I ; #x10
       #\O      #\P      #\{      #\}     #\newline nil      #\A      #\S ; #x18
			       
       #\D      #\F      #\G      #\H      #\J      #\K      #\L      #\: ; #x20
       #\"      #\~      nil      #\|      #\Z      #\X      #\C      #\V ; #x28
       #\B      #\N      #\M      #\<      #\>      #\?      nil      nil ; #x30
       nil      nil      nil      nil      nil      nil      nil      nil ; #x38
       nil      nil      nil      nil      nil    :pause     nil      nil)) ; #xd8
    (:azerty
     #(#\null   #\escape #\&      #\~      #\"      #\'      #\(      #\- ; #x00
       #\`      #\_      #\|      #\@      #\)      #\= #\backspace #\tab ; #x08
       #\a      #\z      #\e      #\r      #\t      #\y      #\u      #\i ; #x10
       #\o      #\p      #\^      #\$   #\newline :ctrl-left #\q      #\s ; #x18
			       
       #\d      #\f      #\g      #\h      #\j      #\k      #\l      #\m ; #x20
       #\%      #\#   :shift-left #\*      #\w      #\x      #\c      #\v ; #x28
       #\b      #\n      #\,      #\;      #\:      #\!  :shift-right #\escape ; #x30
       :alt-left #\space :caps-lock :f1    :f2      :f3      :f4      :f5 ; #x38
			       
       :f6      :f7      :f8      :f9      :f10   :break :scroll-lock nil ; #x40
       nil      nil      nil      nil      nil      nil      nil      nil ; #x48
       nil      :kp-ins  nil      :kp-del  nil      nil      #\<      :f11 ; #x50
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
       :down  :page-down :insert  nil #+ignore #\delete nil nil      nil      nil      nil ; #xd0
       :alt-right nil    nil      nil      :win     :menu    nil      nil) ; #x40
     #(#\null   nil      #\1      #\2      #\3      #\4      #\5      #\6 ; #x00
       #\7      #\8      #\9      #\0      #\A      #\+      nil      nil ; #x08
       #\A      #\Z      #\E      #\R      #\T      #\Y      #\U      #\I ; #x10
       #\O      #\P      #\{      #\}     #\newline nil      #\Q      #\S ; #x18
			       
       #\D      #\F      #\G      #\H      #\J      #\K      #\L      #\M ; #x20
       #\[      #\|      nil      #\]      #\W      #\X      #\C      #\V ; #x28
       #\B      #\N      #\?      #\.      #\/      #\\      nil      nil ; #x30
       nil      nil      nil      nil      nil      nil      nil      nil ; #x38
       nil      nil      nil      nil      nil    :pause     nil      nil ; #x40
       nil      nil      nil      nil      nil      nil      nil      nil ; #x48
       nil      nil      nil      nil      nil      nil      #\>      nil)) ; #x50
    (:dvorak
     #(#\null   #\escape #\1      #\2      #\3      #\4      #\5      #\6 ; #x00
       #\7      #\8      #\9      #\0      #\[      #\] #\backspace #\tab ; #x08
       #\'      #\,      #\.      #\p      #\y      #\f      #\g      #\c ; #x10
       #\r      #\l      #\/      #\=   #\newline :ctrl-left #\a      #\o ; #x18
			       
       #\e      #\u      #\i      #\d      #\h      #\t      #\n      #\s ; #x20
       #\-      #\`   :shift-left #\\      #\;      #\q      #\j      #\k ; #x28
       #\x      #\b      #\m      #\w      #\v      #\z  :shift-right #\escape ; #x30
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
       :down  :page-down :insert  nil #+ignore #\delete nil nil      nil      nil      nil ; #xd0
       :alt-right nil    nil      nil      :win     :menu    nil      nil) ; #x40
     #(#\null   nil      #\!      #\@      #\#      #\$      #\%      #\^ ; #x00
       #\&      #\*      #\(      #\)      #\{      #\}      nil      nil ; #x08
       #\"      #\<      #\>      #\P      #\Y      #\F      #\G      #\C ; #x10
       #\R      #\L      #\?      #\+     #\newline nil      #\A      #\O ; #x18
			       
       #\E      #\U      #\I      #\D      #\H      #\T      #\N      #\S ; #x20
       #\_      #\~      nil      #\|      #\:      #\Q      #\J      #\K ; #x28
       #\X      #\B      #\M      #\W      #\V      #\Z      nil      nil ; #x30
       nil      nil      nil      nil      nil      nil      nil      nil ; #x38
       nil      nil      nil      nil      nil    :pause     nil      nil))) ; #xd8
  "An assoc of all defined keyboard layouts.")

;; default to qwerty
(defparameter *scan-codes* (second (assoc :qwerty *layouts*)))
(defparameter *scan-codes-shift* (third (assoc :qwerty *layouts*)))

(defun set-kbd-layout (layout-id)
  "Set the keyboard layout to one provided in *layouts*."
  (let* ((layout (or (assoc layout-id *layouts*)
                     (error "Ther is no layout named ~S defined." layout-id)))
         (normal (second layout))
         (shifted (third layout)))
    (setf *scan-codes* normal
          *scan-codes-shift* shifted)))

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

(defconstant +qualifier-shift+ 0)
(defconstant +qualifier-ctrl+ 1)
(defconstant +qualifier-alt+ 2)

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


  
