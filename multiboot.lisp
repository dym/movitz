;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      multiboot.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Jun 12 12:14:12 2002
;;;;                
;;;; $Id: multiboot.lisp,v 1.5 2004/07/28 14:23:37 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

;;;    The layout of the Multiboot header must be as follows:
;;;    
;;;    Offset  Type    Field Name     Note
;;;    0       u32     magic          required
;;;    4       u32     flags          required
;;;    8       u32     checksum       required
;;;    12      u32     header_addr    if flags[16] is set
;;;    16      u32     load_addr      if flags[16] is set
;;;    20      u32     load_end_addr  if flags[16] is set
;;;    24      u32     bss_end_addr   if flags[16] is set
;;;    28      u32     entry_addr     if flags[16] is set
;;;    32      u32     mode_type      if flags[2] is set
;;;    36      u32     width          if flags[2] is set
;;;    40      u32     height         if flags[2] is set
;;;    44      u32     depth          if flags[2] is set


(defconstant +multiboot-header-magic-value+  #x1BADB002)

(define-binary-class multiboot-header (movitz-heap-object)
  ((scan-skip-header
    :binary-type lu32
    :initform +scan-skip-word+)
   (scan-skip-length
    :binary-type lu32
    :initform 0
    :map-binary-write (lambda (x type)
			(declare (ignore x type))
			(- (sizeof 'multiboot-header) 8)))
   (magic
    :accessor magic
    :initform +multiboot-header-magic-value+
    :initarg :magic
    :binary-type lu32)
   (flags
    :accessor flags
    :initarg :flags
    :initform '(:addresses-included)
    :binary-type (define-bitfield multiboot-flags (lu32)
		   (((:bits)
		     ;; Align modules to 4K boundaries?
		     :align-modules-4k 0
		     ;; Pass memory information to the kernel?
		     :pass-memory-info 1
		     ;; Pass video modes information to the kernel
		     :pass-video-info  2
		     ;; Is the address fiels below included in the header?
		     :addresses-included 16))))
   (checksum
    :accessor checksum
    :initform (ldb (byte 32 0)
		   (- (+ +multiboot-header-magic-value+
			 (enum-value 'multiboot-flags '(:addresses-included)))))
    :binary-type lu32)
   (header-address 
    ;; Contains the address corresponding to the beginning of the
    ;; Multiboot header -- the physical memory location at which the
    ;; magic value is supposed to be loaded. This field serves to
    ;; "synchronize" the mapping between OS image offsets and physical
    ;; memory addresses.
    :accessor header-address
    :initarg :header-address
    :binary-type lu32)
   (load-address
    ;; Contains the physical address of the beginning of the text
    ;; segment. The offset in the OS image file at which to start
    ;; loading is defined by the offset at which the header was found,
    ;; minus (header_addr - load_addr). load_addr must be less than or
    ;; equal to header_addr.
    :accessor load-address
    :initarg :load-address
    :binary-type lu32)
   (load-end-address
    ;; Contains the physical address of the end of the data segment.
    ;; (load_end_addr - load_addr) specifies how much data to load.
    ;; This implies that the text and data segments must be
    ;; consecutive in the OS image; this is true for existing a.out
    ;; executable formats.  If this field is zero, the boot loader
    ;; assumes that the text and data segments occupy the whole OS
    ;; image file.
    :accessor load-end-address
    :initarg :load-end-address
    :binary-type lu32)
   (bss-end-address
    ;; Contains the physical address of the end of the bss
    ;; segment. The boot loader initializes this area to zero, and
    ;; reserves the memory it occupies to avoid placing boot modules
    ;; and other data relevant to the operating system in that
    ;; area. If this field is zero, the boot loader assumes that no
    ;; bss segment is present.
    :accessor bss-end-address
    :initarg :bss-end-address
    :initform 0
    :binary-type lu32)
   (entry-address
    ;; The physical address to which the boot loader should jump in
    ;; order to start running the operating system.
    :accessor entry-address
    :initarg :entry-address
    :binary-type lu32)
   (video-mode-type
    ;; Valid numbers for `mode_type' is 0 for linear graphics mode and
    ;; 1 for EGA-standard text mode. Everything else is reserved for
    ;; future expansion. Please note that even if you set this field
    ;; to indicate that you want a graphics mode, you might get a text
    ;; mode.
    :accessor video-mode-type
    :initarg :video-mode-type
    :initform 0
    :binary-type lu32)
   (video-width
    ;; `width' and `height' is specified in pixels, if graphics mode,
    ;; or characters in EGA text mode. `depth' is given in bits per
    ;; pixel for graphics, or zero for EGA text modes.
    :accessor video-width
    :initarg :video-width
    :initform 0
    :binary-type lu32)
   (video-height
    :accessor video-height
    :initarg :video-height
    :initform 0
    :binary-type lu32)
   (video-depth
    :accessor video-depth
    :initarg :video-depth
    :initform 0
    :binary-type lu32)))

(defmethod movitz-object-offset ((obj multiboot-header)) 0)
