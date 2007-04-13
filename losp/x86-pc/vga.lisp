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
;;;; $Id: vga.lisp,v 1.14 2007/04/13 22:59:26 ffjeld Exp $
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

(defconstant +vga-state-320x200x256-modex+
  '((:misc . #x63)
    (:sequencer
     #x03 #x01 #x0F #x00 #x06)
    (:crtc
     #x5F #x4F #x50 #x82 #x54 #x80 #xBF #x1F
     #x00 #x41 #x00 #x00 #x00 #x00 #x00 #x00
     #x9C #x0E #x8F #x28 #x00 #x96 #xB9 #xE3
     #xFF)
    (:graphics
     #x00 #x00 #x00 #x00 #x00 #x40 #x05 #x0F
     #xFF)
    (:attribute
     #x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07
     #x08 #x09 #x0A #x0B #x0C #x0D #x0E #x0F
     #x41 #x00 #x0F #x00 #x00)))


;; intended future wrapper for graphics modes
(defconstant +graphical-mode-modex+
  '(+vga-state-320x200x256-modex+       ; vga state
    320                                 ; width
    200                                 ; height
    3))                                 ; page count


(defvar *vga-current-page* 0)
(defvar *vga-page-count* 0)
(defvar *vga-width* 0)
(defvar *vga-height* 0)
(defvar *vga-viewport* '(0 0 0 0))

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

(defun set-plane-by-bitmask (p)
  (check-type p (integer 0 15))
  ;; set read plane
  (setf (io-port VGA-GC-INDEX :unsigned-byte8) 4)
  (setf (io-port VGA-GC-DATA :unsigned-byte8) p)
  ;; set write plane
  (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) 2)
  (setf (io-port VGA-SEQ-DATA :unsigned-byte8) p))

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


;; run-length compressed: color count color count ...
(defvar *vga-g-splash*
  #{7 255 7 255 7 255 7 255 7 255 7 255 7 255 7 35 0 3 7 255 7 58 0 4 7 255 7 58 0
  1 4 1 0 0 7 255 7 57 0 1 4 2 0 0 7 255 7 57 0 1 4 2 0 0 1 6 7 255 7 50 0 1 4 2
  0 0 1 16 7 255 7 40 0 0 4 2 0 0 1 21 7 255 7 35 0 1 4 2 0 0 1 2 7 1 1 8 7 1 1
  9 7 255 7 31 0 1 4 2 0 0 1 2 7 1 1 8 7 1 1 11 7 255 7 29 0 1 4 1 0 1 1 1 7 2 1
  8 7 1 1 2 7 4 1 5 7 255 7 26 0 1 4 2 0 0 1 2 7 1 1 8 7 2 1 1 7 7 1 5 7 255 7
  24 0 1 4 2 0 0 1 2 7 1 1 8 7 2 1 1 7 2 1 0 7 4 1 5 7 255 7 23 0 1 4 1 0 1 1 2
  7 1 1 8 7 1 1 1 7 2 1 3 7 3 1 5 7 255 7 22 0 0 4 2 0 0 1 2 7 2 1 8 7 1 1 1 7 2
  1 5 7 2 1 5 7 255 7 20 0 1 4 2 0 0 1 2 7 1 1 9 7 1 1 2 7 1 1 6 7 1 1 6 7 255 7
  19 0 1 4 2 0 0 1 2 7 1 1 8 7 2 1 2 7 2 1 15 7 255 7 18 0 1 4 1 0 1 1 1 7 2 1 8
  7 2 1 3 7 3 1 7 7 2 1 2 7 255 7 17 0 1 4 2 0 0 1 2 7 1 1 9 7 1 1 5 7 4 1 4 7 4
  1 2 7 255 7 16 0 1 4 2 0 0 1 2 7 1 1 9 7 1 1 6 7 4 1 3 7 5 1 2 7 255 7 15 0 1
  4 1 0 1 1 2 7 1 1 9 7 1 1 8 7 3 1 2 7 1 1 0 7 3 1 2 7 255 7 14 0 0 4 2 0 0 1 2
  7 2 1 9 7 1 1 10 7 2 1 1 7 1 1 1 7 2 1 3 7 255 7 12 0 1 4 2 0 0 1 2 7 1 1 9 7
  2 1 1 7 1 1 6 7 2 1 0 7 2 1 2 7 2 1 2 7 255 7 12 0 1 4 2 0 0 1 2 7 1 1 4 7 1 1
  2 7 2 1 1 7 2 1 5 7 2 1 0 7 2 1 3 7 1 1 4 7 255 7 10 0 1 4 1 0 1 1 2 7 9 1 1 7
  1 1 3 7 3 1 3 7 2 1 0 7 2 1 3 7 2 1 4 7 255 7 8 0 1 4 2 0 0 1 2 7 9 1 9 7 4 1
  0 7 2 1 1 7 3 1 2 7 2 1 5 7 255 7 7 0 1 4 2 0 0 1 23 7 7 1 1 7 8 1 8 7 255 7 5
  0 1 4 1 0 1 1 25 7 4 1 1 7 2 1 0 7 5 1 9 7 255 7 4 0 0 4 2 0 1 1 13 7 7 1 10 7
  2 1 2 7 2 1 12 7 255 7 1 0 1 4 2 0 1 7 1 1 4 7 16 1 8 7 2 1 20 7 255 0 1 4 2 0
  0 7 25 1 7 7 1 1 23 7 253 0 1 4 1 0 1 7 27 1 5 7 1 1 25 7 251 0 0 4 2 0 1 7 28
  1 4 7 1 1 23 7 157 0 7 7 86 0 1 4 2 0 1 7 30 1 25 7 159 0 1 7 6 0 0 7 85 0 1 4
  1 0 1 7 33 1 20 7 157 0 6 7 2 0 2 7 0 0 6 7 79 0 0 4 2 0 1 7 35 1 14 7 159 0 2
  7 3 0 1 7 1 0 8 7 2 0 3 7 71 2 4 4 2 0 1 7 39 1 4 7 164 0 1 7 7 0 0 7 1 0 4 7
  8 0 1 7 68 2 6 4 2 0 0 7 210 0 0 7 3 0 1 7 3 0 0 7 1 0 1 7 7 0 3 7 0 0 0 7 65
  2 8 4 1 0 1 7 209 0 1 7 1 0 11 7 7 0 4 7 0 0 0 7 64 2 10 4 0 0 0 2 0 7 209 0 0
  7 2 0 4 7 4 0 2 7 7 0 3 7 1 0 0 7 62 2 14 7 208 0 1 7 2 0 3 7 7 0 1 7 0 0 9 7
  1 0 0 7 61 2 17 7 206 0 0 7 4 0 1 7 3 0 2 7 2 0 1 7 5 0 1 7 3 0 0 7 61 2 17 7
  206 0 1 7 4 0 0 7 3 0 3 7 0 0 1 7 3 0 2 7 0 0 0 7 3 0 0 7 60 2 19 7 198 2 7 0
  1 7 3 0 0 7 3 0 3 7 0 0 0 7 4 0 5 7 0 0 2 7 60 2 9 0 0 2 8 7 193 2 13 0 5 7 3
  0 3 7 0 0 0 7 5 0 1 7 1 0 2 2 0 7 61 2 8 0 1 4 1 2 7 7 187 2 23 0 0 7 3 0 2 7
  1 0 1 7 7 0 1 2 5 7 57 2 9 0 0 4 2 0 0 2 5 7 184 2 27 0 0 7 9 0 0 7 6 0 1 2 8
  7 55 2 9 0 0 4 2 0 0 2 5 7 181 2 30 0 1 7 8 0 7 2 11 7 53 2 21 7 178 2 34 0 1
  7 5 0 1 2 21 7 49 2 22 7 176 2 39 0 6 2 23 7 46 2 23 7 174 2 74 7 43 2 25 7
  171 2 78 7 40 2 16 0 0 2 10 7 168 2 81 7 37 2 18 0 0 4 2 2 7 7 166 2 83 7 35 2
  20 0 0 4 2 0 0 2 6 7 164 2 86 7 33 2 20 0 1 4 1 0 1 2 6 7 162 2 88 7 31 2 22 0
  0 4 2 0 0 2 6 7 161 2 91 7 28 2 24 0 0 4 2 0 0 2 3 7 162 2 94 7 26 2 15 7 9 0
  0 4 2 0 0 7 165 2 95 7 24 2 15 7 10 0 1 4 1 0 0 7 164 2 98 7 22 2 14 7 12 0 0
  4 2 0 0 7 163 2 100 7 19 2 14 7 14 0 0 4 2 0 0 7 161 2 61 0 1 2 39 7 17 2 14 7
  15 0 3 7 161 2 61 0 5 2 38 7 13 2 14 7 182 2 62 0 0 7 0 0 0 7 1 0 3 2 38 7 7 2
  16 7 182 2 63 0 0 7 0 0 0 7 1 0 0 7 1 0 2 2 60 7 181 2 64 0 3 7 1 0 0 7 1 0 0
  7 0 0 2 2 57 7 182 2 64 0 0 7 0 0 4 7 0 0 1 7 0 0 0 7 0 0 4 2 51 7 183 2 65 0
  0 7 0 0 0 7 0 0 2 7 0 0 0 7 1 0 0 7 1 0 0 7 1 0 2 2 48 7 183 2 67 0 1 7 1 0 4
  7 0 0 0 7 1 0 0 7 1 0 3 2 46 7 183 2 69 0 1 7 0 0 0 7 1 0 4 7 0 0 0 7 1 0 0 7
  1 0 1 2 44 7 183 2 71 0 2 7 1 0 0 7 1 0 6 7 1 0 0 2 43 7 185 2 72 0 4 7 0 0 1
  7 0 0 1 7 0 0 4 2 42 7 185 2 76 0 3 7 1 0 0 7 1 0 0 7 1 0 0 2 15 7 1 2 23 7
  187 2 78 0 4 7 1 0 0 7 0 0 0 2 16 7 6 2 16 7 189 2 82 0 4 2 17 7 15 2 2 7 193
  2 106 7 212 2 105 7 213 2 105 7 212 2 106 7 212 2 105 7 213 2 105 7 213 2 105
  7 212 2 105 7 213 2 105 7 213 2 104 7 214 2 103 7 215 2 103 7 214 2 103 7 215
  2 103 7 215 2 104 7 214 2 104 7 214 2 82 7 10 2 10 7 213 2 81 7 13 2 9 7 213 2
  36 7 33 2 10 7 13 2 9 7 213 2 26 7 44 2 9 7 13 2 9 7 213 2 13 7 4 2 7 7 44 2 8
  7 14 2 9 7 213 2 8 7 9 2 7 7 44 2 8 7 14 2 9 7 212 2 8 7 10 2 7 7 44 2 8 7 15
  2 8 7 212 2 7 7 11 2 7 7 44 2 8 7 15 2 8 7 212 2 7 7 11 2 6 7 45 2 8 7 15 2 8
  7 212 2 7 7 11 2 6 7 45 2 7 7 16 2 8 7 212 2 6 7 11 2 7 7 45 2 7 7 16 2 8 7
  211 2 7 7 11 2 7 7 45 2 7 7 16 2 8 7 211 2 7 7 11 2 7 7 45 2 7 7 17 2 8 7 210
  2 7 7 11 2 7 7 45 2 7 7 17 2 8 7 210 2 6 7 12 2 7 7 45 2 7 7 17 2 8 7 210 2 6
  7 12 2 6 7 46 2 6 7 18 2 8 7 210 2 6 7 12 2 6 7 46 2 6 7 18 2 8 7 209 2 7 7 12
  2 6 7 45 2 7 7 18 2 8 7 209 2 6 7 12 2 7 7 45 2 7 7 18 2 8 7 209 2 6 7 12 2 7
  7 45 2 7 7 19 2 7 7 209 2 6 7 12 2 7 7 45 2 7 7 19 2 7 7 209 2 6 7 12 2 6 7 46
  2 7 7 19 2 7 7 208 2 7 7 12 2 6 7 46 2 6 7 20 2 7 7 208 2 6 7 13 2 6 7 46 2 6
  7 20 2 7 7 208 2 6 7 13 2 6 7 46 2 6 7 20 2 7 7 208 2 6 7 13 2 6 7 46 2 6 7 20
  2 7 7 208 2 6 7 12 2 7 7 46 2 6 7 21 2 7 7 207 2 6 7 12 2 7 7 45 2 7 7 21 2 7
  7 206 2 6 7 13 2 6 7 46 2 7 7 21 2 7 7 206 2 6 7 13 2 6 7 46 2 6 7 22 2 7 7
  206 2 6 7 13 2 6 7 46 2 6 7 22 2 7 7 206 2 6 7 13 2 6 7 46 2 6 7 22 2 7 7 206
  2 6 7 13 2 6 7 46 2 6 7 22 2 7 7 205 2 6 7 14 2 6 7 46 2 6 7 23 2 6 7 205 2 6
  7 13 2 6 7 47 2 6 7 23 2 6 7 205 2 6 7 13 2 6 7 47 2 6 7 23 2 6 7 205 2 6 7 13
  2 6 7 47 2 6 7 23 2 6 7 205 2 6 7 13 2 6 7 46 2 7 7 23 2 6 7 205 2 6 7 13 2 6
  7 46 2 6 7 24 2 6 7 204 2 6 7 14 2 6 7 46 2 6 7 24 2 6 7 201 2 10 7 13 2 6 7
  46 2 6 7 24 2 6 7 200 2 12 7 9 2 10 7 45 2 6 7 24 2 6 7 200 2 13 7 7 2 12 7 44
  2 6 7 24 2 7 7 198 2 15 7 5 2 14 7 43 2 6 7 21 2 11 7 197 2 15 7 5 2 14 7 41 2
  9 7 19 2 14 7 195 2 15 7 5 2 14 7 40 2 12 7 17 2 14 7 196 2 14 7 5 2 14 7 39 2
  14 7 15 2 16 7 195 2 13 7 6 2 14 7 39 2 14 7 15 2 16 7 197 2 3 7 1 2 4 7 8 2
  12 7 40 2 14 7 15 2 16 7 218 2 3 7 2 2 3 7 41 2 14 7 16 2 6 7 1 2 5 7 255 7 16
  2 14 7 17 2 4 7 3 2 2 7 255 7 19 2 12 7 255 7 51 2 3 7 1 2 4 7 255 7 255 7 255
  7 255 7 255 7 255 7 255 7 255 7 255 7 255 7 255 7 255 7 255 7 208 0 2 7 255 7
  50 0 1 7 6 0 3 7 72 0 1 7 230 0 2 7 5 0 4 7 72 0 1 7 1 0 4 7 222 0 3 7 4 0 4 7
  72 0 10 7 220 0 3 7 5 0 4 7 71 0 12 7 82 0 1 7 133 0 4 7 4 0 4 7 70 0 6 7 5 0
  2 7 80 0 2 7 132 0 4 7 4 0 5 7 69 0 5 7 8 0 1 7 79 0 2 7 132 0 5 7 3 0 2 7 0 0
  1 7 70 0 5 7 8 0 1 7 79 0 2 7 132 0 1 7 0 0 1 7 4 0 1 7 0 0 2 7 30 0 1 7 5 0 1
  7 29 0 1 7 0 0 1 7 9 0 1 7 78 0 2 7 132 0 1 7 0 0 1 7 4 0 1 7 1 0 1 7 30 0 2 7
  4 0 2 7 31 0 2 7 9 0 1 7 78 0 1 7 132 0 1 7 1 0 1 7 3 0 2 7 0 0 1 7 30 0 3 7 4
  0 1 7 32 0 1 7 9 0 1 7 78 0 2 7 131 0 2 7 0 0 1 7 4 0 1 7 0 0 2 7 30 0 2 7 4 0
  1 7 32 0 2 7 8 0 2 7 77 0 2 7 132 0 1 7 1 0 1 7 3 0 1 7 1 0 1 7 31 0 1 7 4 0 2
  7 32 0 2 7 8 0 2 7 77 0 2 7 131 0 1 7 1 0 2 7 2 0 1 7 1 0 2 7 38 0 6 7 27 0 2
  7 8 0 2 7 77 0 2 7 131 0 2 7 1 0 1 7 2 0 2 7 1 0 1 7 38 0 7 7 27 0 2 7 6 0 3 7
  78 0 2 7 130 0 2 7 1 0 2 7 2 0 1 7 1 0 2 7 36 0 5 7 30 0 2 7 6 0 3 7 78 0 2 7
  131 0 1 7 2 0 1 7 2 0 1 7 2 0 1 7 8 0 2 7 23 0 4 7 33 0 2 7 4 0 4 7 5 0 2 7 17
  0 1 7 50 0 2 7 130 0 2 7 2 0 1 7 1 0 2 7 2 0 1 7 7 0 4 7 4 0 1 7 2 0 1 7 5 0 1
  7 2 0 4 7 4 0 9 7 15 0 5 7 1 0 6 7 5 0 4 7 15 0 2 7 5 0 3 7 7 0 1 7 3 0 2 7 6
  0 3 7 7 0 6 7 131 0 1 7 2 0 2 7 1 0 1 7 2 0 2 7 6 0 5 7 4 0 1 7 1 0 2 7 5 0 1
  7 4 0 1 7 5 0 9 7 16 0 11 7 6 0 5 7 5 0 1 7 7 0 2 7 4 0 4 7 6 0 2 7 1 0 4 7 5
  0 4 7 6 0 6 7 131 0 1 7 3 0 1 7 1 0 1 7 3 0 1 7 6 0 2 7 1 0 1 7 3 0 2 7 1 0 2
  7 4 0 1 7 4 0 1 7 11 0 3 7 17 0 9 7 7 0 2 7 1 0 1 7 4 0 2 7 2 0 1 7 2 0 1 7 3
  0 2 7 1 0 1 7 6 0 1 7 1 0 3 7 5 0 2 7 1 0 1 7 5 0 1 7 2 0 2 7 130 0 2 7 3 0 1
  7 1 0 1 7 2 0 2 7 5 0 2 7 2 0 1 7 3 0 1 7 1 0 2 7 4 0 2 7 3 0 2 7 10 0 3 7 18
  0 6 7 9 0 2 7 2 0 1 7 3 0 2 7 2 0 2 7 1 0 2 7 2 0 2 7 2 0 0 7 6 0 1 7 0 0 3 7
  4 0 0 7 0 0 2 7 2 0 0 7 5 0 1 7 3 0 1 7 131 0 1 7 3 0 2 7 0 0 1 7 3 0 1 7 5 0
  2 7 2 0 1 7 3 0 2 7 1 0 2 7 2 0 0 7 0 0 1 7 4 0 1 7 10 0 2 7 19 0 2 7 13 0 2 7
  2 0 1 7 3 0 2 7 2 0 2 7 2 0 2 7 1 0 2 7 2 0 1 7 6 0 0 7 0 0 3 7 2 0 6 7 2 0 1
  7 4 0 1 7 3 0 2 7 130 0 2 7 3 0 5 7 2 0 2 7 5 0 1 7 2 0 2 7 3 0 1 7 2 0 2 7 0
  0 5 7 3 0 2 7 9 0 2 7 20 0 2 7 13 0 1 7 2 0 2 7 3 0 2 7 2 0 1 7 2 0 2 7 2 0 1
  7 2 0 1 7 6 0 12 7 0 0 1 7 2 0 1 7 5 0 1 7 3 0 1 7 131 0 1 7 4 0 1 7 0 0 1 7 3
  0 2 7 4 0 1 7 2 0 3 7 2 0 1 7 3 0 5 7 0 0 1 7 4 0 1 7 5 0 0 7 2 0 2 7 20 0 2 7
  13 0 1 7 2 0 3 7 2 0 2 7 2 0 2 7 2 0 2 7 1 0 2 7 1 0 1 7 7 0 3 7 0 0 5 7 1 0 2
  7 1 0 1 7 5 0 1 7 3 0 2 7 130 0 2 7 4 0 3 7 4 0 1 7 5 0 1 7 3 0 1 7 3 0 1 7 2
  0 5 7 0 0 2 7 4 0 1 7 4 0 1 7 1 0 2 7 21 0 2 7 13 0 1 7 3 0 1 7 2 0 2 7 2 0 2
  7 2 0 2 7 2 0 1 7 0 0 2 7 3 0 1 7 1 0 3 7 1 0 4 7 2 0 1 7 0 0 2 7 3 0 1 7 0 0
  1 7 3 0 2 7 130 0 1 7 5 0 3 7 3 0 2 7 4 0 1 7 3 0 1 7 4 0 0 7 3 0 1 7 4 0 1 7
  4 0 1 7 4 0 1 7 1 0 2 7 21 0 2 7 13 0 1 7 3 0 1 7 3 0 2 7 1 0 3 7 2 0 1 7 2 0
  5 7 3 0 1 7 2 0 2 7 9 0 5 7 3 0 1 7 0 0 1 7 3 0 2 7 130 0 2 7 5 0 2 7 4 0 2 7
  4 0 1 7 2 0 2 7 3 0 1 7 2 0 1 7 4 0 2 7 4 0 1 7 3 0 2 7 0 0 2 7 22 0 2 7 13 0
  1 7 2 0 2 7 2 0 2 7 1 0 3 7 2 0 2 7 2 0 3 7 4 0 1 7 2 0 3 7 9 0 3 7 4 0 1 7 1
  0 1 7 3 0 2 7 130 0 1 7 14 0 1 7 5 0 1 7 1 0 2 7 4 0 1 7 1 0 1 7 5 0 1 7 5 0 1
  7 2 0 2 7 0 0 2 7 22 0 2 7 14 0 1 7 1 0 2 7 3 0 2 7 0 0 1 7 0 0 1 7 1 0 2 7 3
  0 1 7 5 0 1 7 3 0 2 7 10 0 1 7 5 0 1 7 2 0 1 7 2 0 3 7 129 0 2 7 13 0 2 7 5 0
  5 7 5 0 5 7 5 0 1 7 5 0 1 7 1 0 2 7 1 0 1 7 0 0 5 7 16 0 2 7 14 0 5 7 4 0 4 7
  1 0 5 7 4 0 2 7 2 0 2 7 4 0 1 7 11 0 2 7 2 0 2 7 3 0 1 7 1 0 1 7 0 0 1 7 129 0
  1 7 14 0 2 7 5 0 4 7 6 0 4 7 5 0 2 7 5 0 5 7 1 0 9 7 16 0 1 7 15 0 4 7 5 0 3 7
  2 0 4 7 5 0 7 7 4 0 2 7 11 0 7 7 4 0 5 7 0 0 1 7 128 0 2 7 14 0 2 7 6 0 2 7 8
  0 1 7 7 0 1 7 7 0 2 7 3 0 2 7 22 0 2 7 16 0 2 7 7 0 1 7 3 0 3 7 7 0 4 7 6 0 1
  7 13 0 4 7 6 0 4 7 1 0 2 7 127 0 1 7 15 0 2 7 28 0 1 7 40 0 2 7 57 0 1 7 26 0
  2 7 3 0 1 7 126 0 2 7 15 0 2 7 71 0 1 7 223 0 1 7 17 0 0 7 255 7 255 7 255 7
  255 7 255 7 255 7 255 7 255 7 255 7 127
  })

;;

(defun restore-textmode (textmode-state)
  (setf (vga-state) textmode-state)
  (ecase (vga-character-height)
    (8 (write-font +vga-font-8x8+ 8))
    (16 (write-font +vga-font-8x16+ 16)))
  nil)

(defun invoke-debugger-with-textmode (debugger textmode-state condition)
  (let ((interrupted-vga-state (vga-state))
        (muerte::*debugger-function* debugger))
    (restore-textmode textmode-state)
    (unwind-protect
         (invoke-debugger condition)
      (setf (vga-state) interrupted-vga-state)
      (g-clear))))

(defmacro with-textmode-restored (options &body body)
  "Reset current VGA textmode after body completes, or debugger is entered."
  (declare (ignore options))
  (let ((real-debugger-var (gensym "real-debugger-"))
        (vga-state-var (gensym "vga-state-")))
    `(let* ((,vga-state-var
             (vga-state))
            (,real-debugger-var
             muerte::*debugger-function*)
            (muerte::*debugger-function*
             (lambda (c)
               (invoke-debugger-with-textmode ,real-debugger-var ,vga-state-var c))))
       (unwind-protect
            (progn ,@body)
         (restore-textmode ,vga-state-var)))))

;; graphics functions below
;;



;; TODO: This can be optimised through two methods
;;   1. Either write all of plane 1, then plane 2 etc (plane switches are slow)
;;   2. Use multiple plane writes at once (see g-clear for idea)
;;       -  Probably better because of large areas of the same colour
(defun rle-blit-splash (splash)
  (loop with index = 0
      for i from 0 below (length splash) by 2
      for value = (aref splash i)
      for count = (1+ (aref splash (1+ i)))
      do (loop repeat count
             do (setf (pixel (mod index *vga-width*) ; ugly hackitude :(
                             (truncate index *vga-width*))
                      value)
             (incf index)))
  nil)

;; show the splash screen
(defun g-show-splash ()
  (with-textmode-restored ()
    (g-start)
    (rle-blit-splash *vga-g-splash*)
    (page-flip)
    (read-char)
    (g-clear))
  (values))

;; read a pixel from the DISPLAYED page
(defun pixel (x y)
  (memref-int (vga-memory-map)
   :index (+ (* (truncate *vga-width* 4) y)
             (truncate x y)
             (* (truncate *vga-width* 2)
                *vga-height*
                (mod (1+ *vga-current-page*)
                     *vga-page-count*)))
   :type :unsigned-byte8))

;; set a pixel to a colour of our choice
;; write to the NEXT page
(defun (setf pixel) (color x y)
  (cond
    ((< x (nth 0 (viewport))))
    ((>= x (nth 1 (viewport))))
    ((< y (nth 2 (viewport))))
    ((>= y (nth 3 (viewport))))
    (t (set-plane (logand x 3))
       (setf (memref-int (vga-memory-map)
              :index (+ (* (truncate *vga-width* 4) y) ; pixel
                        (truncate x 4)
                        (* (truncate *vga-width* 2) ; page
                           *vga-height*
                           *vga-current-page*))
              :type :unsigned-byte8)
             color)))
  color)



; return the current viewport as a list
(defun viewport ()
  *vga-viewport*)


; sets the viewport
; rectangle is a list of left-bound, right-bound, top-bound, bottom-bound
(defun (setf viewport) (rectangle)
  (setf *vga-viewport* rectangle))


;; clear the screen
(defun g-clear ()
  ;; set read plane to all (bitmask 1111)
  (set-plane-by-bitmask 15)
  ;; writing to all 4 planes here thus 1/4 of the bytes
  ;; and by writing 16 bits a time we get double plus good optimisation :)
  ;; However, we wish to cover four planes, thus four times the memory
  (loop for x from 0 below (* *vga-width* *vga-height*)
      do (setf (memref-int (vga-memory-map) 
                :index x
                :type :unsigned-byte16)
               #x0000)))


(defun unchain-video-mode ()
  ;; disable chain-4
  (setf (io-port VGA-SEQ-INDEX :unsigned-byte8) #x04)
  (setf (io-port VGA-SEQ-DATA :unsigned-byte8) #x06)
  ;; disable long mode
  (setf (io-port VGA-CRTC-INDEX :unsigned-byte8) #x14)
  (setf (io-port VGA-CRTC-DATA :unsigned-byte8) #x00)
  ;; enable byte mode
  (setf (io-port VGA-CRTC-INDEX :unsigned-byte8) #x17)
  (setf (io-port VGA-CRTC-DATA :unsigned-byte8) #xE3))


(defun set-page (page)
  (setf (io-port VGA-CRTC-INDEX :unsigned-byte8) #x0C)
  (setf (io-port VGA-CRTC-DATA :unsigned-byte8) (ldb (byte 8 8)
                                                     (* page
                                                        (truncate *vga-width* 2)
                                                        *vga-height*)))
  (setf (io-port VGA-CRTC-INDEX :unsigned-byte8) #x00)
  (setf (io-port VGA-CRTC-DATA :unsigned-byte8) (ldb (byte 8 0)
                                                     (* page
                                                        (truncate *vga-width* 2)
                                                        *vga-height*))))
  

;; Simple wrapper to swap pages
(defun page-flip ()
  (set-page *vga-current-page*)
  (setf *vga-current-page*
        (mod (1+ *vga-current-page*)
             *vga-page-count*)))


;; easy way to get into graphics mode
(defun g-start ()
  (setf (vga-state) +vga-state-320x200x256-modex+)
  (setf *vga-width* 320)
  (setf *vga-height* 200)
  (setf *vga-page-count* 2)
  (setf *vga-current-page* 0)           ; writing page
  (setf (viewport) `(0 ,(1- *vga-width*) 0 ,(1- *vga-height*)))
  (unchain-video-mode)
  (g-clear)
  (page-flip))


;; draw-line from ch-image
;; originally written by Cyrus Harmon
;; modified for movitz by Martin Bealby
(defun draw-line (y0 x0 y1 x1 col)
  (let ((dx (- x1 x0))
        (dy (- y1 y0)))
    (declare (type fixnum dx dy))
    (let ((absdx (abs dx))
          (absdy (abs dy)))
      (declare (type fixnum absdx absdy))
      (let ((xstep (if (minusp dx) -1 1))
            (ystep (if (minusp dy) -1 1)))
        (if (>= absdx absdy)
            (let ((d (- (* 2 absdy) absdx))
                  (incr-e (* 2 absdy))
                  (incr-ne (* 2 (- absdy absdx)))
                  (x x0)
                  (y y0))
              (declare (type fixnum d incr-e incr-ne x y))
              (setf (pixel y x) col)
              (dotimes (i absdx)
                (cond
                  ((<= d 0)
                   (incf d incr-e)
                   (incf x xstep))
                  (t
                   (incf d incr-ne)
                   (incf x xstep)
                   (incf y ystep)))
                (setf (pixel y x) col)))
            (let ((d (- (* 2 absdy) absdx))
                  (incr-n (* 2 absdx))
                  (incr-ne (* 2 (- absdx absdy)))
                  (x x0)
                  (y y0))
              (declare (type fixnum d incr-n incr-ne x y))
              (setf (pixel y x) col)
              (dotimes (i absdy)
                (cond
                  ((<= d 0)
                   (incf d incr-n)
                   (incf y ystep))
                  (t
                   (incf d incr-ne)
                   (incf y ystep)
                   (incf x xstep)))
                (setf (pixel y x) col))))))))

;; draw-circle from ch-image
;; originally written by Cyrus Harmon
;; modified for movitz by Martin Bealby
(defmethod draw-circle (center-y center-x radius col)
  (declare (type fixnum center-y center-x radius))
  (flet ((circle-points (y x col)
           (setf (pixel (+ center-y y) (+ center-x x)) col) 
           (setf (pixel (+ center-y x) (+ center-x y)) col) 
           (setf (pixel (- center-y x) (+ center-x y)) col) 
           (setf (pixel (- center-y y) (+ center-x x)) col) 
           (setf (pixel (- center-y y) (- center-x x)) col) 
           (setf (pixel (- center-y x) (- center-x y)) col) 
           (setf (pixel (+ center-y x) (- center-x y)) col) 
           (setf (pixel (+ center-y y) (- center-x x)) col)))
    (let ((x 0)
          (y radius)
          (d (- 1 radius))
          (delta-e 3)
          (delta-se (+ (* -2 radius) 5)))
      (declare (type fixnum x y d delta-e delta-se))
      (circle-points y x col)
      (do () ((>= x y))
        (if (< d 0)
            (progn
              (incf d delta-e)
              (incf delta-e 2)
              (incf delta-se 2))
            (progn
              (incf d delta-se)
              (incf delta-e 2)
              (incf delta-se 4)
              (decf y)))
        (incf x)
        (circle-points y x col)))))

;; additional drawing functions (rectangle / triangle)
(defmethod draw-rectangle (x1 y1 x2 y2 col)
  (draw-line x1 y1 x1 y2 col)
  (draw-line x1 y1 x2 y1 col)
  (draw-line x1 y2 x2 y2 col)
  (draw-line x2 y1 x2 y2 col))


(defmethod draw-triangle (x1 y1 x2 y2 x3 y3 col)
  (draw-line x1 y1 x2 y2 col)
  (draw-line x2 y2 x3 y3 col)
  (draw-line x3 y3 x1 y1 col))

