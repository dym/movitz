;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      vga.lisp
;;;; Description:   Low-level VGA interfacing.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue Sep 25 14:08:20 2001
;;;;                
;;;; $Id: vga.lisp,v 1.6 2004/11/14 22:58:33 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :x86-pc/package)
(provide :x86-pc/vga)

(in-package muerte.x86-pc)

(defconstant +vga-base+ #x3c0)

(defmacro vga-port (register)
  `(io-register8 +vga-base+ ,register))

(defun vga-crt-controller-register (register)
  (let* ((address-register (if (logbitp 0 (io-port #x3cc :unsigned-byte8)) #x3d4 #x3b4))
	 (data-register (1+ address-register)))
    (setf (io-port address-register :unsigned-byte8) register)
    (io-port data-register :unsigned-byte8)))

(defun (setf vga-crt-controller-register) (value register)
  (let* ((address-register (if (logbitp 0 (io-port #x3cc :unsigned-byte8)) #x3d4 #x3b4))
	 (data-register (1+ address-register)))
    (setf (io-port address-register :unsigned-byte8) register
	  (io-port data-register :unsigned-byte8) value)))

(defun vga-graphics-register (register)
  (setf (io-port #x3ce :unsigned-byte8) register)
  (io-port #x3cf :unsigned-byte8))

(defun (setf vga-graphics-register) (value register)
  (setf (io-port #x3ce :unsigned-byte8) register
	(io-port #x3cf :unsigned-byte8) value))

(defun vga-sequencer-register (register)
  (setf (vga-port 4) register)
  (vga-port 5))

(defun (setf vga-sequencer-register) (value register)
  (setf (vga-port 4) register
	(vga-port 5) value))

(defun vga-attribute-register (register)
  (vga-port #x1a)
  (setf (vga-port 0) register)
  (vga-port 1))

(defun (setf vga-attribute-register) (value register)
  (vga-port #x1a)
  (setf (vga-port 0) register
	(vga-port 0) value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun (setf vga-cursor-location) (value)
  (setf (vga-crt-controller-register #x0e) (ldb (byte 8 8) value) ; high
	(vga-crt-controller-register #x0f) (ldb (byte 8 0) value)) ; low
  value)

(defun vga-cursor-location ()
  (dpb (vga-crt-controller-register #x0e)
       (byte 8 8)
       (vga-crt-controller-register #x0f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vga-memory-map ()
  (case (ldb (byte 2 2)
	     (vga-graphics-register 6))
    (#b00 (values #xa0000 #xbffff))
    (#b01 (values #xa0000 #xaffff))
    (#b10 (values #xb0000 #xb7fff))
    (#b11 (values #xb8000 #xbffff))))

(defun vga-horizontal-display-end ()
  (1+ (vga-crt-controller-register 1)))

(defun vga-vertical-display-end ()
  (let ((overflow (vga-crt-controller-register 7)))
    (+ 1
       (vga-crt-controller-register #x12)
       (if (logbitp 1 overflow) #x100 0)
       (if (logbitp 6 overflow) #x200 0))))

(defun vga-character-height ()
  (1+ (ldb (byte 5 0)
	   (vga-crt-controller-register 9))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; VGA stuff ported from http://my.execpc.com/CE/AC/geezer/osd/graphics/modes.c

(defconstant +vga-state-80x25+
    '((:misc . #x67)
      (:sequencer
       #x03 #x00 #x03 #x00 #x02)
      (:crtc
       #x5F #x4F #x50 #x82 #x55 #x81 #xBF #x1F
       #x00 #x4F #x0D #x0E #x00 #x00 #x00 #x50
       #x9C #x0E #x8F #x28 #x1F #x96 #xB9 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))

(defconstant +vga-state-80x50+
    '((:misc . #x67)
      (:sequencer
       #x03 #x00 #x03 #x00 #x02)
      (:crtc
       #x5F #x4F #x50 #x82 #x55 #x81 #xBF #x1F
       #x00 #x47 #x06 #x07 #x00 #x00 #x01 #x40
       #x9C #x8E #x8F #x28 #x1F #x96 #xB9 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))

(defconstant +vga-state-40x25+
    '((:misc . #x67)
      (:sequencer
       #x03 #x08 #x03 #x00 #x02)
      (:crtc
       #x2D #x27 #x28 #x90 #x2B #xA0 #xBF #x1F
       #x00 #x4F #x0D #x0E #x00 #x00 #x00 #xA0
       #x9C #x8E #x8F #x14 #x1F #x96 #xB9 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))

(defconstant +vga-state-40x50+
    '((:misc . #x67)
      (:sequencer
       #x03 #x08 #x03 #x00 #x02)
      (:crtc
       #x2D #x27 #x28 #x90 #x2B #xA0 #xBF #x1F
       #x00 #x47 #x06 #x07 #x00 #x00 #x04 #x60
       #x9C #x8E #x8F #x14 #x1F #x96 #xB9 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))

(defconstant +vga-state-90x30+
    '((:misc . #xE7)
      (:sequencer
       #x03 #x01 #x03 #x00 #x02)
      (:crtc
       #x6B #x59 #x5A #x82 #x60 #x8D #x0B #x3E
       #x00 #x4F #x0D #x0E #x00 #x00 #x00 #x00
       #xEA #x0C #xDF #x2D #x10 #xE8 #x05 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))

(defconstant +vga-state-90x60+
    '((:misc . #xE7)
      (:sequencer
       #x03 #x01 #x03 #x00 #x02)
      (:crtc
       #x6B #x59 #x5A #x82 #x60 #x8D #x0B #x3E
       #x00 #x47 #x06 #x07 #x00 #x00 #x00 #x00
       #xEA #x0C #xDF #x2D #x08 #xE8 #x05 #xA3
       #xFF)
      (:graphics
       #x00 #x00 #x00 #x00 #x00 #x10 #x0E #x00
       #xFF)
      (:attribute
       #x00 #x01 #x02 #x03 #x04 #x05 #x14 #x07
       #x38 #x39 #x3A #x3B #x3C #x3D #x3E #x3F
       #x0C #x00 #x0F #x08 #x00)))


(defconstant +vga-misc-read+ #x0c)
(defconstant +vga-misc-write+ #x02)

(defconstant VGA-MISC-WRITE #x3C2)
(defconstant VGA-AC-INDEX #x3C0)
(defconstant VGA-AC-WRITE #x3C0)
(defconstant VGA-AC-READ #x3C1)
(defconstant VGA-SEQ-INDEX #x3C4)
(defconstant VGA-SEQ-DATA #x3C5)
(defconstant VGA-DAC-READ-INDEX #x3C7)
(defconstant VGA-DAC-WRITE-INDEX #x3C8)
(defconstant VGA-DAC-DATA #x3C9)
(defconstant VGA-MISC-READ #x3CC)
(defconstant VGA-GC-INDEX  #x3CE)
(defconstant VGA-GC-DATA  #x3CF)
(defconstant VGA-CRTC-INDEX #x3D4)
(defconstant VGA-CRTC-DATA #x3D5)
(defconstant VGA-INSTAT-READ #x3DA)

(defun vga-state ()
  "Dump the state of the VGA register set."
  (prog1
      (list
       (cons :misc
	     (vga-port +vga-misc-read+))
       (cons :sequencer
	     (loop for i from 0 below 5
		 collect (vga-sequencer-register i)))
       (cons :crtc
	     (loop for i from 0 below 25
		 collect (vga-crt-controller-register i)))
       (cons :graphics
	     (loop for i from 0 below 9
		 collect  (vga-graphics-register i)))
       (cons :attribute
	     (loop for i from 0 below 21
		 collect (vga-attribute-register i))))
    ;; lock 16-color palette and unblank display
    (io-port VGA-INSTAT-READ :unsigned-byte8)
    (setf (io-port VGA-AC-INDEX :unsigned-byte8) #x20)))

(defun (setf vga-state) (state &optional unsafe-p)
  "Initialize the state of the VGA register set."
  (let ((old-state (if unsafe-p nil (vga-state))))
    (flet ((vga-reset (&optional c)
	     (declare (ignore c))
	     (when old-state
	       (warn "Something bad happened, resetting VGA state..")
	       (setf (vga-state t) old-state
		     old-state nil)))
	   (assert-register-set (state register-set)
	     (let ((set (assoc register-set state)))
	       (assert set () "VGA state is missing ~A." register-set)
	       (cdr set))))
      (unwind-protect
	  (handler-bind ((serious-condition #'vga-reset))
	    ;; write MISCELLANEOUS reg
	    (setf (vga-port +vga-misc-write+)
	      (assert-register-set state :misc))
	    ;; write SEQUENCER regs
	    (loop for x in (assert-register-set state :sequencer)
		as i upfrom 0
		do (setf (vga-sequencer-register i) x))
	    (loop
	      ;; unlock CRTC registers
		initially (setf (vga-crt-controller-register 3)
			    (logior #x80 (vga-crt-controller-register 3)))
			  (setf (vga-crt-controller-register #x11)
			    (logand #x7f (vga-crt-controller-register #x11)))
		for x in (assert-register-set state :crtc)
		as i upfrom 0
		do (setf (vga-crt-controller-register i)
		     (case i
		       ;; make sure they remain unlocked
		       (#x03 (logior #x80 x))
		       (#x11 (logand #x7f x))
		       (t x))))
	    ;; write GRAPHICS CONTROLLER regs
	    (loop for x in (assert-register-set state :graphics)
		as i upfrom 0
		do (setf (vga-graphics-register i) x))
	    ;; write ATTRIBUTE CONTROLLER regs
	    (loop for x in (assert-register-set state :attribute)
		as i upfrom 0
		do (setf (vga-attribute-register i) x))
	    ;; lock 16-color palette and unblank display
	    (io-port VGA-INSTAT-READ :unsigned-byte8)
	    (setf (io-port VGA-AC-INDEX :unsigned-byte8) #x20)
	    (setf old-state nil))
	(vga-reset))))
  state)

(defun set-plane (p)
  (check-type p (integer 0 3))
  (let* ((p (logand p 3))
	 (pmask (ash 1 p)))
    ;; set read plane
    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 4)
    (setf (io-port VGA-GC-DATA :unsigned-byte8) p)
    ;; set write plane
    (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 2)
    (setf (io-port VGA-SEQ-DATA :unsigned-byte8) pmask))
  (values))

(defun vmemwr (dst-off src start end)
  (loop for i from start below end as dst upfrom dst-off
      do (setf (memref-int (vga-memory-map) :index dst :type :unsigned-byte8)
	   (aref src i)))
  (values))

(defun write-font (buf font-height)
  (let* ((seq2
	  (progn
	    ;; set_plane() modifies GC 4 and SEQ 2, so save them as well
	    (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 2)
	    (io-port VGA-SEQ-DATA :unsigned-byte8)))
	 (seq4
	  (progn
	    (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 4)
	    (io-port VGA-SEQ-DATA :unsigned-byte8)))
	 (gc4
	  (progn
	    ;; turn off even-odd addressing (set flat addressing)
	    ;; assume: chain-4 addressing already off
	    (setf (io-port VGA-SEQ-DATA :unsigned-byte8)
	      (logior #x04 seq4))
	    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 4)
	    (io-port VGA-GC-DATA :unsigned-byte8)))
	 (gc5
	  (progn
	    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 5)
	    (io-port VGA-GC-DATA :unsigned-byte8)))
	 (gc6
	  (progn
	    ;; turn off even-odd addressing
	    (setf (io-port VGA-GC-DATA :unsigned-byte8)
	      (logand gc5 (logxor #x10 #xff)))
	    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 6)
	    (io-port VGA-GC-DATA :unsigned-byte8))))
    ;; turn off even-odd addressing
    (setf (io-port VGA-GC-DATA :unsigned-byte8)
      (logand gc6 (logxor #xff #x02)))
    ;; write font to plane P4
    (set-plane 2)			; set_plane(2)
    ;; write font 0
    (dotimes (i 256)
      (vmemwr (* i 32) buf (* i font-height) (* (1+ i) font-height)))

    ;; restore registers
    (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 2)
    (setf (io-port VGA-SEQ-DATA :unsigned-byte8) seq2)
    (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 4)
    (setf (io-port VGA-SEQ-DATA :unsigned-byte8) seq4)
    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 4)
    (setf (io-port VGA-GC-DATA :unsigned-byte8) gc4)
    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 5)
    (setf (io-port VGA-GC-DATA :unsigned-byte8) gc5)
    (setf (io-port VGA-GC-INDEX :unsigned-byte8) 6)
    (setf (io-port VGA-GC-DATA :unsigned-byte8) gc6))
  (values))


(defconstant +vga-font-8x8+
    #{#x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x7E #x81 #xA5 #x81 #xBD #x99 #x81 #x7E
    #x7E #xFF #xDB #xFF #xC3 #xE7 #xFF #x7E
    #x6C #xFE #xFE #xFE #x7C #x38 #x10 #x00
    #x10 #x38 #x7C #xFE #x7C #x38 #x10 #x00
    #x38 #x7C #x38 #xFE #xFE #x92 #x10 #x7C
    #x00 #x10 #x38 #x7C #xFE #x7C #x38 #x7C
    #x00 #x00 #x18 #x3C #x3C #x18 #x00 #x00
    #xFF #xFF #xE7 #xC3 #xC3 #xE7 #xFF #xFF
    #x00 #x3C #x66 #x42 #x42 #x66 #x3C #x00
    #xFF #xC3 #x99 #xBD #xBD #x99 #xC3 #xFF
    #x0F #x07 #x0F #x7D #xCC #xCC #xCC #x78
    #x3C #x66 #x66 #x66 #x3C #x18 #x7E #x18
    #x3F #x33 #x3F #x30 #x30 #x70 #xF0 #xE0
    #x7F #x63 #x7F #x63 #x63 #x67 #xE6 #xC0
    #x99 #x5A #x3C #xE7 #xE7 #x3C #x5A #x99
    #x80 #xE0 #xF8 #xFE #xF8 #xE0 #x80 #x00
    #x02 #x0E #x3E #xFE #x3E #x0E #x02 #x00
    #x18 #x3C #x7E #x18 #x18 #x7E #x3C #x18 
    #x66 #x66 #x66 #x66 #x66 #x00 #x66 #x00 
    #x7F #xDB #xDB #x7B #x1B #x1B #x1B #x00 
    #x3E #x63 #x38 #x6C #x6C #x38 #x86 #xFC 
    #x00 #x00 #x00 #x00 #x7E #x7E #x7E #x00 
    #x18 #x3C #x7E #x18 #x7E #x3C #x18 #xFF
    #x18 #x3C #x7E #x18 #x18 #x18 #x18 #x00
    #x18 #x18 #x18 #x18 #x7E #x3C #x18 #x00
    #x00 #x18 #x0C #xFE #x0C #x18 #x00 #x00 
    #x00 #x30 #x60 #xFE #x60 #x30 #x00 #x00 
    #x00 #x00 #xC0 #xC0 #xC0 #xFE #x00 #x00 
    #x00 #x24 #x66 #xFF #x66 #x24 #x00 #x00 
    #x00 #x18 #x3C #x7E #xFF #xFF #x00 #x00 
    #x00 #xFF #xFF #x7E #x3C #x18 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x18 #x3C #x3C #x18 #x18 #x00 #x18 #x00
    #x6C #x6C #x6C #x00 #x00 #x00 #x00 #x00 
    #x6C #x6C #xFE #x6C #xFE #x6C #x6C #x00 
    #x18 #x7E #xC0 #x7C #x06 #xFC #x18 #x00 
    #x00 #xC6 #xCC #x18 #x30 #x66 #xC6 #x00
    #x38 #x6C #x38 #x76 #xDC #xCC #x76 #x00
    #x30 #x30 #x60 #x00 #x00 #x00 #x00 #x00
    #x18 #x30 #x60 #x60 #x60 #x30 #x18 #x00 
    #x60 #x30 #x18 #x18 #x18 #x30 #x60 #x00
    #x00 #x66 #x3C #xFF #x3C #x66 #x00 #x00 
    #x00 #x18 #x18 #x7E #x18 #x18 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x30
    #x00 #x00 #x00 #x7E #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x00
    #x06 #x0C #x18 #x30 #x60 #xC0 #x80 #x00
    #x7C #xCE #xDE #xF6 #xE6 #xC6 #x7C #x00 
    #x30 #x70 #x30 #x30 #x30 #x30 #xFC #x00 
    #x78 #xCC #x0C #x38 #x60 #xCC #xFC #x00 
    #x78 #xCC #x0C #x38 #x0C #xCC #x78 #x00 
    #x1C #x3C #x6C #xCC #xFE #x0C #x1E #x00 
    #xFC #xC0 #xF8 #x0C #x0C #xCC #x78 #x00 
    #x38 #x60 #xC0 #xF8 #xCC #xCC #x78 #x00
    #xFC #xCC #x0C #x18 #x30 #x30 #x30 #x00
    #x78 #xCC #xCC #x78 #xCC #xCC #x78 #x00 
    #x78 #xCC #xCC #x7C #x0C #x18 #x70 #x00 
    #x00 #x18 #x18 #x00 #x00 #x18 #x18 #x00 
    #x00 #x18 #x18 #x00 #x00 #x18 #x18 #x30 
    #x18 #x30 #x60 #xC0 #x60 #x30 #x18 #x00 
    #x00 #x00 #x7E #x00 #x7E #x00 #x00 #x00 
    #x60 #x30 #x18 #x0C #x18 #x30 #x60 #x00
    #x3C #x66 #x0C #x18 #x18 #x00 #x18 #x00 
    #x7C #xC6 #xDE #xDE #xDC #xC0 #x7C #x00 
    #x30 #x78 #xCC #xCC #xFC #xCC #xCC #x00 
    #xFC #x66 #x66 #x7C #x66 #x66 #xFC #x00 
    #x3C #x66 #xC0 #xC0 #xC0 #x66 #x3C #x00 
    #xF8 #x6C #x66 #x66 #x66 #x6C #xF8 #x00 
    #xFE #x62 #x68 #x78 #x68 #x62 #xFE #x00 
    #xFE #x62 #x68 #x78 #x68 #x60 #xF0 #x00
    #x3C #x66 #xC0 #xC0 #xCE #x66 #x3A #x00 
    #xCC #xCC #xCC #xFC #xCC #xCC #xCC #x00 
    #x78 #x30 #x30 #x30 #x30 #x30 #x78 #x00 
    #x1E #x0C #x0C #x0C #xCC #xCC #x78 #x00 
    #xE6 #x66 #x6C #x78 #x6C #x66 #xE6 #x00 
    #xF0 #x60 #x60 #x60 #x62 #x66 #xFE #x00 
    #xC6 #xEE #xFE #xFE #xD6 #xC6 #xC6 #x00
    #xC6 #xE6 #xF6 #xDE #xCE #xC6 #xC6 #x00 
    #x38 #x6C #xC6 #xC6 #xC6 #x6C #x38 #x00 
    #xFC #x66 #x66 #x7C #x60 #x60 #xF0 #x00 
    #x7C #xC6 #xC6 #xC6 #xD6 #x7C #x0E #x00 
    #xFC #x66 #x66 #x7C #x6C #x66 #xE6 #x00
    #x7C #xC6 #xE0 #x78 #x0E #xC6 #x7C #x00 
    #xFC #xB4 #x30 #x30 #x30 #x30 #x78 #x00
    #xCC #xCC #xCC #xCC #xCC #xCC #xFC #x00 
    #xCC #xCC #xCC #xCC #xCC #x78 #x30 #x00
    #xC6 #xC6 #xC6 #xC6 #xD6 #xFE #x6C #x00 
    #xC6 #xC6 #x6C #x38 #x6C #xC6 #xC6 #x00 
    #xCC #xCC #xCC #x78 #x30 #x30 #x78 #x00
    #xFE #xC6 #x8C #x18 #x32 #x66 #xFE #x00
    #x78 #x60 #x60 #x60 #x60 #x60 #x78 #x00
    #xC0 #x60 #x30 #x18 #x0C #x06 #x02 #x00
    #x78 #x18 #x18 #x18 #x18 #x18 #x78 #x00 
    #x10 #x38 #x6C #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF 
    #x30 #x30 #x18 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x78 #x0C #x7C #xCC #x76 #x00 
    #xE0 #x60 #x60 #x7C #x66 #x66 #xDC #x00 
    #x00 #x00 #x78 #xCC #xC0 #xCC #x78 #x00
    #x1C #x0C #x0C #x7C #xCC #xCC #x76 #x00
    #x00 #x00 #x78 #xCC #xFC #xC0 #x78 #x00 
    #x38 #x6C #x64 #xF0 #x60 #x60 #xF0 #x00 
    #x00 #x00 #x76 #xCC #xCC #x7C #x0C #xF8 
    #xE0 #x60 #x6C #x76 #x66 #x66 #xE6 #x00 
    #x30 #x00 #x70 #x30 #x30 #x30 #x78 #x00 
    #x0C #x00 #x1C #x0C #x0C #xCC #xCC #x78 
    #xE0 #x60 #x66 #x6C #x78 #x6C #xE6 #x00
    #x70 #x30 #x30 #x30 #x30 #x30 #x78 #x00 
    #x00 #x00 #xCC #xFE #xFE #xD6 #xD6 #x00 
    #x00 #x00 #xB8 #xCC #xCC #xCC #xCC #x00 
    #x00 #x00 #x78 #xCC #xCC #xCC #x78 #x00 
    #x00 #x00 #xDC #x66 #x66 #x7C #x60 #xF0 
    #x00 #x00 #x76 #xCC #xCC #x7C #x0C #x1E 
    #x00 #x00 #xDC #x76 #x62 #x60 #xF0 #x00 
    #x00 #x00 #x7C #xC0 #x70 #x1C #xF8 #x00
    #x10 #x30 #xFC #x30 #x30 #x34 #x18 #x00 
    #x00 #x00 #xCC #xCC #xCC #xCC #x76 #x00 
    #x00 #x00 #xCC #xCC #xCC #x78 #x30 #x00 
    #x00 #x00 #xC6 #xC6 #xD6 #xFE #x6C #x00 
    #x00 #x00 #xC6 #x6C #x38 #x6C #xC6 #x00 
    #x00 #x00 #xCC #xCC #xCC #x7C #x0C #xF8 
    #x00 #x00 #xFC #x98 #x30 #x64 #xFC #x00
    #x1C #x30 #x30 #xE0 #x30 #x30 #x1C #x00 
    #x18 #x18 #x18 #x00 #x18 #x18 #x18 #x00 
    #xE0 #x30 #x30 #x1C #x30 #x30 #xE0 #x00 
    #x76 #xDC #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x10 #x38 #x6C #xC6 #xC6 #xFE #x00
    #x7C #xC6 #xC0 #xC6 #x7C #x0C #x06 #x7C 
    #x00 #xCC #x00 #xCC #xCC #xCC #x76 #x00
    #x1C #x00 #x78 #xCC #xFC #xC0 #x78 #x00 
    #x7E #x81 #x3C #x06 #x3E #x66 #x3B #x00
    #xCC #x00 #x78 #x0C #x7C #xCC #x76 #x00 
    #xE0 #x00 #x78 #x0C #x7C #xCC #x76 #x00 
    #x30 #x30 #x78 #x0C #x7C #xCC #x76 #x00
    #x00 #x00 #x7C #xC6 #xC0 #x78 #x0C #x38
    #x7E #x81 #x3C #x66 #x7E #x60 #x3C #x00
    #xCC #x00 #x78 #xCC #xFC #xC0 #x78 #x00
    #xE0 #x00 #x78 #xCC #xFC #xC0 #x78 #x00 
    #xCC #x00 #x70 #x30 #x30 #x30 #x78 #x00 
    #x7C #x82 #x38 #x18 #x18 #x18 #x3C #x00 
    #xE0 #x00 #x70 #x30 #x30 #x30 #x78 #x00 
    #xC6 #x10 #x7C #xC6 #xFE #xC6 #xC6 #x00 
    #x30 #x30 #x00 #x78 #xCC #xFC #xCC #x00 
    #x1C #x00 #xFC #x60 #x78 #x60 #xFC #x00
    #x00 #x00 #x7F #x0C #x7F #xCC #x7F #x00
    #x3E #x6C #xCC #xFE #xCC #xCC #xCE #x00 
    #x78 #x84 #x00 #x78 #xCC #xCC #x78 #x00 
    #x00 #xCC #x00 #x78 #xCC #xCC #x78 #x00 
    #x00 #xE0 #x00 #x78 #xCC #xCC #x78 #x00 
    #x78 #x84 #x00 #xCC #xCC #xCC #x76 #x00 
    #x00 #xE0 #x00 #xCC #xCC #xCC #x76 #x00 
    #x00 #xCC #x00 #xCC #xCC #x7C #x0C #xF8
    #xC3 #x18 #x3C #x66 #x66 #x3C #x18 #x00 
    #xCC #x00 #xCC #xCC #xCC #xCC #x78 #x00 
    #x18 #x18 #x7E #xC0 #xC0 #x7E #x18 #x18 
    #x38 #x6C #x64 #xF0 #x60 #xE6 #xFC #x00 
    #xCC #xCC #x78 #x30 #xFC #x30 #xFC #x30 
    #xF8 #xCC #xCC #xFA #xC6 #xCF #xC6 #xC3 
    #x0E #x1B #x18 #x3C #x18 #x18 #xD8 #x70 
    #x1C #x00 #x78 #x0C #x7C #xCC #x76 #x00
    #x38 #x00 #x70 #x30 #x30 #x30 #x78 #x00 
    #x00 #x1C #x00 #x78 #xCC #xCC #x78 #x00 
    #x00 #x1C #x00 #xCC #xCC #xCC #x76 #x00 
    #x00 #xF8 #x00 #xB8 #xCC #xCC #xCC #x00 
    #xFC #x00 #xCC #xEC #xFC #xDC #xCC #x00 
    #x3C #x6C #x6C #x3E #x00 #x7E #x00 #x00 
    #x38 #x6C #x6C #x38 #x00 #x7C #x00 #x00
    #x18 #x00 #x18 #x18 #x30 #x66 #x3C #x00 
    #x00 #x00 #x00 #xFC #xC0 #xC0 #x00 #x00 
    #x00 #x00 #x00 #xFC #x0C #x0C #x00 #x00 
    #xC6 #xCC #xD8 #x36 #x6B #xC2 #x84 #x0F 
    #xC3 #xC6 #xCC #xDB #x37 #x6D #xCF #x03
    #x18 #x00 #x18 #x18 #x3C #x3C #x18 #x00 
    #x00 #x33 #x66 #xCC #x66 #x33 #x00 #x00
    #x00 #xCC #x66 #x33 #x66 #xCC #x00 #x00 
    #x22 #x88 #x22 #x88 #x22 #x88 #x22 #x88
    #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA 
    #xDB #xF6 #xDB #x6F #xDB #x7E #xD7 #xED 
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x18 #x18 #x18 #x18 #xF8 #x18 #x18 #x18
    #x18 #x18 #xF8 #x18 #xF8 #x18 #x18 #x18
    #x36 #x36 #x36 #x36 #xF6 #x36 #x36 #x36
    #x00 #x00 #x00 #x00 #xFE #x36 #x36 #x36 
    #x00 #x00 #xF8 #x18 #xF8 #x18 #x18 #x18 
    #x36 #x36 #xF6 #x06 #xF6 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x00 #x00 #xFE #x06 #xF6 #x36 #x36 #x36 
    #x36 #x36 #xF6 #x06 #xFE #x00 #x00 #x00 
    #x36 #x36 #x36 #x36 #xFE #x00 #x00 #x00
    #x18 #x18 #xF8 #x18 #xF8 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #xF8 #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x1F #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #xFF #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #xFF #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x1F #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #xFF #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #xFF #x18 #x18 #x18
    #x18 #x18 #x1F #x18 #x1F #x18 #x18 #x18 
    #x36 #x36 #x36 #x36 #x37 #x36 #x36 #x36 
    #x36 #x36 #x37 #x30 #x3F #x00 #x00 #x00 
    #x00 #x00 #x3F #x30 #x37 #x36 #x36 #x36 
    #x36 #x36 #xF7 #x00 #xFF #x00 #x00 #x00 
    #x00 #x00 #xFF #x00 #xF7 #x36 #x36 #x36 
    #x36 #x36 #x37 #x30 #x37 #x36 #x36 #x36 
    #x00 #x00 #xFF #x00 #xFF #x00 #x00 #x00
    #x36 #x36 #xF7 #x00 #xF7 #x36 #x36 #x36 
    #x18 #x18 #xFF #x00 #xFF #x00 #x00 #x00 
    #x36 #x36 #x36 #x36 #xFF #x00 #x00 #x00 
    #x00 #x00 #xFF #x00 #xFF #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #xFF #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x3F #x00 #x00 #x00 
    #x18 #x18 #x1F #x18 #x1F #x00 #x00 #x00
    #x00 #x00 #x1F #x18 #x1F #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #x3F #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #xFF #x36 #x36 #x36
    #x18 #x18 #xFF #x18 #xFF #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #xF8 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x1F #x18 #x18 #x18 
    #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF
    #x00 #x00 #x00 #x00 #xFF #xFF #xFF #xFF 
    #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0
    #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F 
    #xFF #xFF #xFF #xFF #x00 #x00 #x00 #x00 
    #x00 #x00 #x76 #xDC #xC8 #xDC #x76 #x00
    #x00 #x78 #xCC #xF8 #xCC #xF8 #xC0 #xC0
    #x00 #xFC #xCC #xC0 #xC0 #xC0 #xC0 #x00
    #x00 #x00 #xFE #x6C #x6C #x6C #x6C #x00
    #xFC #xCC #x60 #x30 #x60 #xCC #xFC #x00
    #x00 #x00 #x7E #xD8 #xD8 #xD8 #x70 #x00
    #x00 #x66 #x66 #x66 #x66 #x7C #x60 #xC0
    #x00 #x76 #xDC #x18 #x18 #x18 #x18 #x00
    #xFC #x30 #x78 #xCC #xCC #x78 #x30 #xFC
    #x38 #x6C #xC6 #xFE #xC6 #x6C #x38 #x00
    #x38 #x6C #xC6 #xC6 #x6C #x6C #xEE #x00
    #x1C #x30 #x18 #x7C #xCC #xCC #x78 #x00
    #x00 #x00 #x7E #xDB #xDB #x7E #x00 #x00
    #x06 #x0C #x7E #xDB #xDB #x7E #x60 #xC0
    #x38 #x60 #xC0 #xF8 #xC0 #x60 #x38 #x00
    #x78 #xCC #xCC #xCC #xCC #xCC #xCC #x00
    #x00 #x7E #x00 #x7E #x00 #x7E #x00 #x00
    #x18 #x18 #x7E #x18 #x18 #x00 #x7E #x00
    #x60 #x30 #x18 #x30 #x60 #x00 #xFC #x00
    #x18 #x30 #x60 #x30 #x18 #x00 #xFC #x00
    #x0E #x1B #x1B #x18 #x18 #x18 #x18 #x18
    #x18 #x18 #x18 #x18 #x18 #xD8 #xD8 #x70
    #x18 #x18 #x00 #x7E #x00 #x18 #x18 #x00
    #x00 #x76 #xDC #x00 #x76 #xDC #x00 #x00
    #x38 #x6C #x6C #x38 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x18 #x00 #x00 #x00
    #x0F #x0C #x0C #x0C #xEC #x6C #x3C #x1C
    #x58 #x6C #x6C #x6C #x6C #x00 #x00 #x00
    #x70 #x98 #x30 #x60 #xF8 #x00 #x00 #x00
    #x00 #x00 #x3C #x3C #x3C #x3C #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 })

(defconstant +vga-font-8x16+
    #{#x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x7E #x81 #xA5 #x81 #x81 #xBD #x99 #x81 #x81 #x7E #x00 #x00 #x00 #x00 
    #x00 #x00 #x7E #xFF #xDB #xFF #xFF #xC3 #xE7 #xFF #xFF #x7E #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x6C #xFE #xFE #xFE #xFE #x7C #x38 #x10 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x10 #x38 #x7C #xFE #x7C #x38 #x10 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x18 #x3C #x3C #xE7 #xE7 #xE7 #x99 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x18 #x3C #x7E #xFF #xFF #x7E #x18 #x18 #x3C #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x18 #x3C #x3C #x18 #x00 #x00 #x00 #x00 #x00 #x00 
    #xFF #xFF #xFF #xFF #xFF #xFF #xE7 #xC3 #xC3 #xE7 #xFF #xFF #xFF #xFF #xFF #xFF
    #x00 #x00 #x00 #x00 #x00 #x3C #x66 #x42 #x42 #x66 #x3C #x00 #x00 #x00 #x00 #x00 
    #xFF #xFF #xFF #xFF #xFF #xC3 #x99 #xBD #xBD #x99 #xC3 #xFF #xFF #xFF #xFF #xFF 
    #x00 #x00 #x1E #x0E #x1A #x32 #x78 #xCC #xCC #xCC #xCC #x78 #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x66 #x66 #x66 #x66 #x3C #x18 #x7E #x18 #x18 #x00 #x00 #x00 #x00
    #x00 #x00 #x3F #x33 #x3F #x30 #x30 #x30 #x30 #x70 #xF0 #xE0 #x00 #x00 #x00 #x00
    #x00 #x00 #x7F #x63 #x7F #x63 #x63 #x63 #x63 #x67 #xE7 #xE6 #xC0 #x00 #x00 #x00 
    #x00 #x00 #x00 #x18 #x18 #xDB #x3C #xE7 #x3C #xDB #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x80 #xC0 #xE0 #xF0 #xF8 #xFE #xF8 #xF0 #xE0 #xC0 #x80 #x00 #x00 #x00 #x00 
    #x00 #x02 #x06 #x0E #x1E #x3E #xFE #x3E #x1E #x0E #x06 #x02 #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x3C #x7E #x18 #x18 #x18 #x18 #x7E #x3C #x18 #x00 #x00 #x00 #x00
    #x00 #x00 #x66 #x66 #x66 #x66 #x66 #x66 #x66 #x00 #x66 #x66 #x00 #x00 #x00 #x00
    #x00 #x00 #x7F #xDB #xDB #xDB #x7B #x1B #x1B #x1B #x1B #x1B #x00 #x00 #x00 #x00 
    #x00 #x7C #xC6 #x60 #x38 #x6C #xC6 #xC6 #x6C #x38 #x0C #xC6 #x7C #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFE #xFE #xFE #xFE #x00 #x00 #x00 #x00
    #x00 #x00 #x18 #x3C #x7E #x18 #x18 #x18 #x18 #x7E #x3C #x18 #x7E #x00 #x00 #x00 
    #x00 #x00 #x18 #x3C #x7E #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x7E #x3C #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x18 #x0C #xFE #x0C #x18 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x30 #x60 #xFE #x60 #x30 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xC0 #xC0 #xC0 #xC0 #xFE #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x28 #x6C #xFE #x6C #x28 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x10 #x38 #x38 #x7C #x7C #xFE #xFE #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #xFE #xFE #x7C #x7C #x38 #x38 #x10 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x3C #x3C #x3C #x18 #x18 #x18 #x00 #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x66 #x66 #x66 #x24 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x6C #x6C #xFE #x6C #x6C #x6C #xFE #x6C #x6C #x00 #x00 #x00 #x00 
    #x18 #x18 #x7C #xC6 #xC2 #xC0 #x7C #x06 #x86 #xC6 #x7C #x18 #x18 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #xC2 #xC6 #x0C #x18 #x30 #x60 #xC6 #x86 #x00 #x00 #x00 #x00
    #x00 #x00 #x38 #x6C #x6C #x38 #x76 #xDC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x30 #x30 #x30 #x60 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x0C #x18 #x30 #x30 #x30 #x30 #x30 #x30 #x18 #x0C #x00 #x00 #x00 #x00 
    #x00 #x00 #x30 #x18 #x0C #x0C #x0C #x0C #x0C #x0C #x18 #x30 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x66 #x3C #xFF #x3C #x66 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x7E #x18 #x18 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x18 #x30 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFE #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x02 #x06 #x0C #x18 #x30 #x60 #xC0 #x80 #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #xC6 #xCE #xD6 #xD6 #xE6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x38 #x78 #x18 #x18 #x18 #x18 #x18 #x18 #x7E #x00 #x00 #x00 #x00
    #x00 #x00 #x7C #xC6 #x06 #x0C #x18 #x30 #x60 #xC0 #xC6 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #x06 #x06 #x3C #x06 #x06 #x06 #xC6 #x7C #x00 #x00 #x00 #x00
    #x00 #x00 #x0C #x1C #x3C #x6C #xCC #xFE #x0C #x0C #x0C #x1E #x00 #x00 #x00 #x00 
    #x00 #x00 #xFE #xC0 #xC0 #xC0 #xFC #x0E #x06 #x06 #xC6 #x7C #x00 #x00 #x00 #x00
    #x00 #x00 #x38 #x60 #xC0 #xC0 #xFC #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #xFE #xC6 #x06 #x06 #x0C #x18 #x30 #x30 #x30 #x30 #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #xC6 #xC6 #x7C #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #xC6 #xC6 #x7E #x06 #x06 #x06 #x0C #x78 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00 #x18 #x18 #x30 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x06 #x0C #x18 #x30 #x60 #x30 #x18 #x0C #x06 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #xFE #x00 #x00 #xFE #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x60 #x30 #x18 #x0C #x06 #x0C #x18 #x30 #x60 #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #xC6 #x0C #x18 #x18 #x18 #x00 #x18 #x18 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x7C #xC6 #xC6 #xDE #xDE #xDE #xDC #xC0 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x10 #x38 #x6C #xC6 #xC6 #xFE #xC6 #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #xFC #x66 #x66 #x66 #x7C #x66 #x66 #x66 #x66 #xFC #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x66 #xC2 #xC0 #xC0 #xC0 #xC0 #xC2 #x66 #x3C #x00 #x00 #x00 #x00
    #x00 #x00 #xF8 #x6C #x66 #x66 #x66 #x66 #x66 #x66 #x6C #xF8 #x00 #x00 #x00 #x00 
    #x00 #x00 #xFE #x66 #x62 #x68 #x78 #x68 #x60 #x62 #x66 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #xFE #x66 #x62 #x68 #x78 #x68 #x60 #x60 #x60 #xF0 #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x66 #xC2 #xC0 #xC0 #xDE #xC6 #xC6 #x66 #x3A #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #xC6 #xC6 #xFE #xC6 #xC6 #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x00 #x1E #x0C #x0C #x0C #x0C #x0C #xCC #xCC #xCC #x78 #x00 #x00 #x00 #x00 
    #x00 #x00 #xE6 #x66 #x6C #x6C #x78 #x78 #x6C #x66 #x66 #xE6 #x00 #x00 #x00 #x00 
    #x00 #x00 #xF0 #x60 #x60 #x60 #x60 #x60 #x60 #x62 #x66 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xEE #xFE #xFE #xD6 #xC6 #xC6 #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xE6 #xF6 #xFE #xDE #xCE #xC6 #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x38 #x6C #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x6C #x38 #x00 #x00 #x00 #x00 
    #x00 #x00 #xFC #x66 #x66 #x66 #x7C #x60 #x60 #x60 #x60 #xF0 #x00 #x00 #x00 #x00 
    #x00 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xD6 #xDE #x7C #x0C #x0E #x00 #x00 
    #x00 #x00 #xFC #x66 #x66 #x66 #x7C #x6C #x66 #x66 #x66 #xE6 #x00 #x00 #x00 #x00
    #x00 #x00 #x7C #xC6 #xC6 #x60 #x38 #x0C #x06 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x7E #x7E #x5A #x18 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x6C #x38 #x10 #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xD6 #xD6 #xFE #x6C #x6C #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #x6C #x6C #x38 #x38 #x6C #x6C #xC6 #xC6 #x00 #x00 #x00 #x00
    #x00 #x00 #x66 #x66 #x66 #x66 #x3C #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00
    #x00 #x00 #xFE #xC6 #x86 #x0C #x18 #x30 #x60 #xC2 #xC6 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x30 #x30 #x30 #x30 #x30 #x30 #x30 #x30 #x3C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x80 #xC0 #xE0 #x70 #x38 #x1C #x0E #x06 #x02 #x00 #x00 #x00 #x00 
    #x00 #x00 #x3C #x0C #x0C #x0C #x0C #x0C #x0C #x0C #x0C #x3C #x00 #x00 #x00 #x00 
    #x10 #x38 #x6C #xC6 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF #x00 #x00 
    #x30 #x30 #x18 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #xE0 #x60 #x60 #x78 #x6C #x66 #x66 #x66 #x66 #xDC #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x7C #xC6 #xC0 #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x1C #x0C #x0C #x3C #x6C #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x7C #xC6 #xFE #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x38 #x6C #x64 #x60 #xF0 #x60 #x60 #x60 #x60 #xF0 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x76 #xCC #xCC #xCC #xCC #xCC #x7C #x0C #xCC #x78 #x00
    #x00 #x00 #xE0 #x60 #x60 #x6C #x76 #x66 #x66 #x66 #x66 #xE6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x18 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x00 #x06 #x06 #x00 #x0E #x06 #x06 #x06 #x06 #x06 #x06 #x66 #x66 #x3C #x00 
    #x00 #x00 #xE0 #x60 #x60 #x66 #x6C #x78 #x78 #x6C #x66 #xE6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #xEC #xFE #xD6 #xD6 #xD6 #xD6 #xD6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xDC #x66 #x66 #x66 #x66 #x66 #x66 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xDC #x66 #x66 #x66 #x66 #x66 #x7C #x60 #x60 #xF0 #x00
    #x00 #x00 #x00 #x00 #x00 #x76 #xCC #xCC #xCC #xCC #xCC #x7C #x0C #x0C #x1E #x00 
    #x00 #x00 #x00 #x00 #x00 #xDC #x76 #x62 #x60 #x60 #x60 #xF0 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x7C #xC6 #x60 #x38 #x0C #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x10 #x30 #x30 #xFC #x30 #x30 #x30 #x30 #x36 #x1C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xCC #xCC #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x66 #x66 #x66 #x66 #x66 #x3C #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xC6 #xC6 #xC6 #xD6 #xD6 #xFE #x6C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xC6 #x6C #x38 #x38 #x38 #x6C #xC6 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x7E #x06 #x0C #xF8 #x00 
    #x00 #x00 #x00 #x00 #x00 #xFE #xCC #x18 #x30 #x60 #xC6 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #x0E #x18 #x18 #x18 #x70 #x18 #x18 #x18 #x18 #x0E #x00 #x00 #x00 #x00 
    #x00 #x00 #x18 #x18 #x18 #x18 #x00 #x18 #x18 #x18 #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x70 #x18 #x18 #x18 #x0E #x18 #x18 #x18 #x18 #x70 #x00 #x00 #x00 #x00
    #x00 #x00 #x76 #xDC #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x10 #x38 #x6C #xC6 #xC6 #xC6 #xFE #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x3C #x66 #xC2 #xC0 #xC0 #xC0 #xC2 #x66 #x3C #x0C #x06 #x7C #x00 #x00 
    #x00 #x00 #xCC #xCC #x00 #xCC #xCC #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x0C #x18 #x30 #x00 #x7C #xC6 #xFE #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x10 #x38 #x6C #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #xCC #xCC #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x60 #x30 #x18 #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00
    #x00 #x38 #x6C #x38 #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x3C #x66 #x60 #x60 #x66 #x3C #x0C #x06 #x3C #x00 #x00 #x00 
    #x00 #x10 #x38 #x6C #x00 #x7C #xC6 #xFE #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #x00 #x7C #xC6 #xFE #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x60 #x30 #x18 #x00 #x7C #xC6 #xFE #xC0 #xC0 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x66 #x66 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00
    #x00 #x18 #x3C #x66 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x60 #x30 #x18 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00
    #x00 #xC6 #xC6 #x10 #x38 #x6C #xC6 #xC6 #xFE #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x38 #x6C #x38 #x00 #x38 #x6C #xC6 #xC6 #xFE #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00
    #x18 #x30 #x60 #x00 #xFE #x66 #x60 #x7C #x60 #x60 #x66 #xFE #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xCC #x76 #x36 #x7E #xD8 #xD8 #x6E #x00 #x00 #x00 #x00 
    #x00 #x00 #x3E #x6C #xCC #xCC #xFE #xCC #xCC #xCC #xCC #xCE #x00 #x00 #x00 #x00 
    #x00 #x10 #x38 #x6C #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00
    #x00 #x60 #x30 #x18 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00
    #x00 #x30 #x78 #xCC #x00 #xCC #xCC #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x60 #x30 #x18 #x00 #xCC #xCC #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #xC6 #xC6 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x7E #x06 #x0C #x78 #x00 
    #x00 #xC6 #xC6 #x00 #x38 #x6C #xC6 #xC6 #xC6 #xC6 #x6C #x38 #x00 #x00 #x00 #x00
    #x00 #xC6 #xC6 #x00 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x18 #x18 #x3C #x66 #x60 #x60 #x60 #x66 #x3C #x18 #x18 #x00 #x00 #x00 #x00 
    #x00 #x38 #x6C #x64 #x60 #xF0 #x60 #x60 #x60 #x60 #xE6 #xFC #x00 #x00 #x00 #x00 
    #x00 #x00 #x66 #x66 #x3C #x18 #x7E #x18 #x7E #x18 #x18 #x18 #x00 #x00 #x00 #x00
    #x00 #xF8 #xCC #xCC #xF8 #xC4 #xCC #xDE #xCC #xCC #xCC #xC6 #x00 #x00 #x00 #x00 
    #x00 #x0E #x1B #x18 #x18 #x18 #x7E #x18 #x18 #x18 #x18 #x18 #xD8 #x70 #x00 #x00 
    #x00 #x18 #x30 #x60 #x00 #x78 #x0C #x7C #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x0C #x18 #x30 #x00 #x38 #x18 #x18 #x18 #x18 #x18 #x3C #x00 #x00 #x00 #x00 
    #x00 #x18 #x30 #x60 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x18 #x30 #x60 #x00 #xCC #xCC #xCC #xCC #xCC #xCC #x76 #x00 #x00 #x00 #x00 
    #x00 #x00 #x76 #xDC #x00 #xDC #x66 #x66 #x66 #x66 #x66 #x66 #x00 #x00 #x00 #x00 
    #x76 #xDC #x00 #xC6 #xE6 #xF6 #xFE #xDE #xCE #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00 
    #x00 #x3C #x6C #x6C #x3E #x00 #x7E #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x38 #x6C #x6C #x38 #x00 #x7C #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x30 #x30 #x00 #x30 #x30 #x60 #xC0 #xC6 #xC6 #x7C #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #xFE #xC0 #xC0 #xC0 #xC0 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #xFE #x06 #x06 #x06 #x06 #x00 #x00 #x00 #x00 #x00 
    #x00 #xC0 #xC0 #xC2 #xC6 #xCC #x18 #x30 #x60 #xCE #x93 #x06 #x0C #x1F #x00 #x00 
    #x00 #xC0 #xC0 #xC2 #xC6 #xCC #x18 #x30 #x66 #xCE #x9A #x3F #x06 #x0F #x00 #x00
    #x00 #x00 #x18 #x18 #x00 #x18 #x18 #x18 #x3C #x3C #x3C #x18 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x33 #x66 #xCC #x66 #x33 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xCC #x66 #x33 #x66 #xCC #x00 #x00 #x00 #x00 #x00 #x00 
    #x11 #x44 #x11 #x44 #x11 #x44 #x11 #x44 #x11 #x44 #x11 #x44 #x11 #x44 #x11 #x44 
    #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA #x55 #xAA 
    #xDD #x77 #xDD #x77 #xDD #x77 #xDD #x77 #xDD #x77 #xDD #x77 #xDD #x77 #xDD #x77
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #xF8 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x18 #xF8 #x18 #xF8 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #xF6 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFE #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x00 #x00 #x00 #x00 #x00 #xF8 #x18 #xF8 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x36 #x36 #x36 #x36 #x36 #xF6 #x06 #xF6 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36
    #x00 #x00 #x00 #x00 #x00 #xFE #x06 #xF6 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #xF6 #x06 #xFE #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #xFE #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #x18 #xF8 #x18 #xF8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xF8 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x1F #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x1F #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #xFF #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x18 #x1F #x18 #x1F #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x37 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x37 #x30 #x3F #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x3F #x30 #x37 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #xF7 #x00 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #xFF #x00 #xF7 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x37 #x30 #x37 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x00 #x00 #x00 #x00 #x00 #xFF #x00 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x36 #x36 #x36 #x36 #x36 #xF7 #x00 #xF7 #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x18 #x18 #x18 #x18 #x18 #xFF #x00 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #xFF #x00 #xFF #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x3F #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x18 #x18 #x18 #x18 #x18 #x1F #x18 #x1F #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 
    #x00 #x00 #x00 #x00 #x00 #x1F #x18 #x1F #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x3F #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x36 #x36 #x36 #x36 #x36 #x36 #x36 #xFF #x36 #x36 #x36 #x36 #x36 #x36 #x36 #x36 
    #x18 #x18 #x18 #x18 #x18 #xFF #x18 #xFF #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #xF8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x1F #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 
    #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF 
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF #xFF 
    #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 
    #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F #x0F 
    #xFF #xFF #xFF #xFF #xFF #xFF #xFF #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x76 #xDC #xD8 #xD8 #xD8 #xDC #x76 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #xFC #xC6 #xFC #xC6 #xC6 #xFC #xC0 #xC0 #xC0 #x00 #x00
    #x00 #x00 #xFE #xC6 #xC6 #xC0 #xC0 #xC0 #xC0 #xC0 #xC0 #xC0 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x80 #xFE #x6C #x6C #x6C #x6C #x6C #x6C #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #xFE #xC6 #x60 #x30 #x18 #x30 #x60 #xC6 #xFE #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x7E #xD8 #xD8 #xD8 #xD8 #xD8 #x70 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x66 #x66 #x66 #x66 #x66 #x7C #x60 #x60 #xC0 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x76 #xDC #x18 #x18 #x18 #x18 #x18 #x18 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x7E #x18 #x3C #x66 #x66 #x66 #x3C #x18 #x7E #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x38 #x6C #xC6 #xC6 #xFE #xC6 #xC6 #x6C #x38 #x00 #x00 #x00 #x00
    #x00 #x00 #x38 #x6C #xC6 #xC6 #xC6 #x6C #x6C #x6C #x6C #xEE #x00 #x00 #x00 #x00
    #x00 #x00 #x1E #x30 #x18 #x0C #x3E #x66 #x66 #x66 #x66 #x3C #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x7E #xDB #xDB #xDB #x7E #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x03 #x06 #x7E #xCF #xDB #xF3 #x7E #x60 #xC0 #x00 #x00 #x00 #x00
    #x00 #x00 #x1C #x30 #x60 #x60 #x7C #x60 #x60 #x60 #x30 #x1C #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x7C #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #xC6 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #xFE #x00 #x00 #xFE #x00 #x00 #xFE #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x18 #x18 #x7E #x18 #x18 #x00 #x00 #xFF #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x30 #x18 #x0C #x06 #x0C #x18 #x30 #x00 #x7E #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x0C #x18 #x30 #x60 #x30 #x18 #x0C #x00 #x7E #x00 #x00 #x00 #x00
    #x00 #x00 #x0E #x1B #x1B #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18
    #x18 #x18 #x18 #x18 #x18 #x18 #x18 #x18 #xD8 #xD8 #xD8 #x70 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x18 #x18 #x00 #x7E #x00 #x18 #x18 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x76 #xDC #x00 #x76 #xDC #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x38 #x6C #x6C #x38 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x18 #x18 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x18 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x0F #x0C #x0C #x0C #x0C #x0C #xEC #x6C #x6C #x3C #x1C #x00 #x00 #x00 #x00
    #x00 #xD8 #x6C #x6C #x6C #x6C #x6C #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x70 #x98 #x30 #x60 #xC8 #xF8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x7C #x7C #x7C #x7C #x7C #x7C #x7C #x00 #x00 #x00 #x00 #x00
    #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 })


