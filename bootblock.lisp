;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001,2000, 2002-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      bootblock.lisp
;;;; Description:   A simple, single-stage, floppy bootloader.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon Oct  9 20:47:19 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: bootblock.lisp,v 1.16 2008/03/03 22:40:55 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package movitz)

(defvar *bootblock-build-file* #p"bootblock-id.txt")
(defvar *bootblock-build*
    ;; make this variable persistent.
    (or (ignore-errors
	 (with-open-file (s *bootblock-build-file* :direction :input)
	   (with-standard-io-syntax (read s))))
	(warn "Unable to read ~S from ~A, resetting to zero."
	      '*bootblock-build*
	      *bootblock-build-file*)
	0))

(defvar *floppy-size* (* 512 18 2 80))

(defun make-segment-descriptor-byte (&rest descriptor-args)
  (list (complex (binary-types::bitfield-compute-numeric-value
		  (find-binary-type 'segment-descriptor)
		  (apply #'make-segment-descriptor descriptor-args))
		 8)))

(defun mkasm16-bios-print ()
  "Print something to the terminal.  [es:si] points to the text"
  `((:movzxb (:si) :cx)
    (:incw :si)
    (:movb #xe :ah)
    (:movw 7 :bx)
    print-loop
    (:lodsb)
    (:int #x10)
    (:loop 'print-loop)
    (:ret)))

(defun mkasm16-format-hex ()
  "Format a 16-bit word (in DX) into hex string (in DI)"
  `((:std)
    (:movw 4 :cx)
    (:addw :cx :di)
    (:decw :di)
    format-loop
    (:movb :dl :bl)
    (:andw #x0f bx)
    (:movb ('hex-table bx) :al)
    (:stosb)
    (:shrw :dx 4)
    (:decw :cx)
    (:jnz 'format-loop)
    (:cld)
    (:ret)
    hex-table (% format nil "0123456789abcdef")))

(defconstant +SECTOR-SIZE+ 512)
(defconstant +HEAD+ 0)
(defconstant +TRACK+ 1)
(defconstant +NOSEC+ 2)
(defconstant +DADDR+ 4)
(defconstant +DADDRSEG+ 6)
(defconstant +STARTSEC+ 8)

(defconstant +linear-sector+ -4)
(defconstant +destination+ -8)
(defconstant +sectors-per-track+ -12)
(defconstant +stack-frame-size+ 16)

(defconstant +read-buffer+ #x10000)

(defun mkasm16-bios-bootloader (image-size load-address &optional (skip-sectors 0))
  (let* ((first-sector (1+ skip-sectors))
	 (last-sector (+ first-sector (ceiling image-size +sector-size+)))
	 (read-buffer-segment (floor +read-buffer+ #x10)))
    `((:jmp (:pc+ 0))		   ; some BIOSes might check for this.
      ;;
      ;; We are running at address #x7c00.
      ;;
      (:xorw :ax :ax)
      (:movw :ax :ds)
      (:movw :ax :es)

      (:movw #x9000 :ax)
      (:movw :ax :ss)
      (:movw #xfffc :bp)
      (:leaw (:bp ,(- +stack-frame-size+)) :sp)
      (:movw 'welcome :si)		; Print welcome message)
      (:callw 'print)
       
      ;;
      ;; Enable the A20 gate
      ;;
      (:callw 'empty-8042)
      (:movb #xd1 :al)
      (:outb :al #x64)

      (:callw 'empty-8042)
      (:movb #xdf :al)
      (:outb :al #x60)
      (:callw 'empty-8042)

      ;; Poll the floppy's sectors per track

      (:movw 5 (:bp ,+sectors-per-track+))
      check-geometry
      (:incb (:bp ,+sectors-per-track+))
      (:jz 'read-error)
      (:movw (:bp ,+sectors-per-track+) :cx )
      (:movw #x0201 :ax)
      (:xorw :dx :dx)
      (:movw ,read-buffer-segment :bx)
      (:movw :bx :es)
      (:xorw :bx :bx)
      (:int #x13)			; Call BIOS routine
      (:testb :ah :ah)
      (:jz 'check-geometry)
      (:decb (:bp ,+sectors-per-track+))
       
      ;;
      ;; Read sectors into memory
      ;;
       
      (:movw ,first-sector (:bp ,+linear-sector+))
      (:movl ,load-address (:bp ,+destination+))

      read-loop
       
      (:cmpw ,last-sector (:bp ,+linear-sector+))
      (:jg 'read-done)
  
      (:movw 'track-start-msg :si) ; Print '(' to screen for each track
      (:callw 'print)
       
      (:movw (:bp ,+linear-sector+) :ax)
      (:movb (:bp ,+sectors-per-track+) :cl)
      (:divb :cl :ax)		; al=quotient, ah=remainder of :ax/:cl

      (:movb :ah :cl)			; sector - 1
      (:movb :al :dh)
      (:andb 1 :dh)			; head
      (:movb :al :ch)
      (:shrb 1 :ch)			; track
      (:xorb :dl :dl)			; drive = 0
      (:movw (:bp ,+sectors-per-track+) :ax)
      (:subb :cl :al)		   ; number of sectors (rest of track)
      (:incb :cl)
      (:addw :ax (:bp ,+linear-sector+))  ; update read pointer
      (:movw (:bp ,+linear-sector+) :bx) ; subtract some if it's the last track.
      (:subw ,last-sector :bx)
      (:jc 'subtract-zero-sectors)
      (:subw :bx :ax)
      (:jz 'read-done)
      subtract-zero-sectors
      (:movb 2 :ah)

      (:movw ,read-buffer-segment :bx)
      (:movw :bx :es)
      (:xorw :bx :bx)
      (:int #x13)			; Call BIOS routine

      (:jc 'read-error)
      (:movzxb :al :ecx)

      ;;
      ;; Install GS as 4GB segment
      ;; http://www.faqs.org/faqs/assembly-language/x86/general/part2/
      ;;
      (:cli)
      (:lgdt ('gdt-addr))		; load gdt
      (:movcr :cr0 :eax)
      (:orb 1 :al)
      (:movcr :eax :cr0)
      (:jmp (:pc+ 0))
      (:movw 16 :bx)
      (:movw :bx :gs)
      (:andb #xfe :al)
      (:movcr :eax :cr0)
      (:jmp (:pc+ 0))
      (:sti)
      ;; Completed install GS as 4GB segment.
       
      ;; Copy data to destination
      (:shll ,(+ 9 -2) :ecx)	       ; 512/4 = sector-size/word-size
      (:movl ,+read-buffer+ :ebx)
      (:movl (:bp ,+destination+) :esi)
      (:leal (:esi (:ecx 4)) :edx)

      (:movl :edx (:bp ,+destination+))

      copy-loop
      (:decl :ecx)
      ((:gs-override) :movl (:ebx (:ecx 4)) :edx)
      ((:gs-override) :movl :edx (:esi (:ecx 4)))
      (:jnz 'copy-loop)

      (:movw 'track-end-msg :si) ; Print ')' to screen after each track
      (:callw 'print)
       
      (:jmp 'read-loop)
       
      read-done
       
      motor-loop			; Wait for floppy motor
      (:btw 8 (#x43e))
      (:jc 'motor-loop)
       
      (:movw 'entering :si)		; Print welcome message
      (:callw 'print)
       
      ;; Read the cursor position into DH (row) and DL (column).
      (:movb 3 :ah)
      (:movb 0 :bh)
      (:int #x10)

      (:cli)				; Disable interrupts
      (:lgdt ('gdt-addr))		; load gdt

      (:xorw :ax :ax)
      (:movw :ax :es)			; reset es

      ;;
      ;; Turn off the cursor
      ;;
       
;;;       (movb #x01 :ah)
;;;       (movw #x0100 :cx)
;;;       (int  #x10)
       

      ;;
      ;; Load machine status word.  This will enable
      ;; protected mode.  The subsequent instruction MUST
      ;; reload the code segment register with a selector for
      ;; the protected mode code segment descriptor (see
      ;; GDT specification).
      ;;
      (:movw 1 :ax)
      (:lmsw :ax)			; load word 0 of cr0

      ;;
      ;; Do a longjump to new-world.  This will cause the CS to
      ;; be loaded with the correct descriptor, and the processor
      ;; will now run in 32 bit mode.
      ;;

      (:jmp 8 ('new-world))

      ;;
      ;; Display error message and hang
      ;;
      read-error
      (:movw 'error :si)		; Print error message
      (:callw 'print)
      halt-cpu
      (:halt)
      (:jmp 'halt-cpu)			; Infinite loop

      ;;
      ;; Empty the 8042 Keyboard controller
      ;;
      empty-8042
      (:callw 'delay)
      (:inb #x64 :al)			; 8042 status port
      (:testb 1 :al)		     ; if ( no information available )
      (:jz 'no-output)			;   goto no_output
      (:callw 'delay)
      (:inb #x60 :al)			; read it
      (:jmp 'empty-8042)
      no-output
      (:testb 2 :al)			; if ( input buffer is full )
      (:jnz 'empty-8042)		;   goto empty_8042
      (:ret)

      delay
      (:xorw :cx :cx)
      delay-loop
      (:loop 'delay-loop)
      (:ret)

      print ,@(mkasm16-bios-print)
       
      ;; Data
      welcome         (:% :format 8 "Loading Movitz ~D..~%"
			 ,(incf *bootblock-build*))
      entering        (:% :format 8 "~%Enter..")
      error           (:% :format 8 "Failed!)")
      track-start-msg (:% :format 8 "(")
      track-end-msg   (:% :format 8 ")")
      sector-msg      (:% :format 8 "-")
     
      (:% :align 16)
      gdt
      (:% :bytes 16 0)
      gdt-addr
      (:% :bytes 16 ,(1- (* 3 8)))
      (:% :bytes 32 'gdt) ; both the null and pointer to gdt
      ;; (% fun (make-segment-descriptor-byte)) ; dummy null descriptor
      (:% :fun (make-segment-descriptor-byte :base 0 :limit #xfffff ; 1: code segment
						     :type 10 :dpl 0
						     :flags (s p d/b g)))
      (:% :fun (make-segment-descriptor-byte :base 0 :limit #xfffff ; 2: data segment
						     :type 2 :dpl 0
						     :flags (s p d/b g)))
      ;; (% align 4)
      new-world
      ;; ..must be concatenated onto here.
      )))


(defconstant +screen-base+ #xb8000)
(defparameter +message+ "Ok.")
(defparameter +halt-message+ "Halt!")

(defun make-vga-string (string)
  (loop for char across string
     collect (char-code char)
     collect #x07))

(defun mkasm-loader (image-size load-address call-address)
  "Make the 32-bit loader."
  (assert (<= load-address call-address (+ load-address image-size)) ()
    "Call-address #x~X is not in range #x~X to #x~X."
    call-address load-address (+ load-address image-size))
  `((:movw ,(* 2 8) :ax) ; Load DS, ES and SS with the correct data segment descriptors
    (:movw :ax :ds)
    (:movw :ax :es)
    (:movw :ax :fs)
    (:movw :ax :gs)
    (:movw :ax :ss)

    (:movl #x20000 :esp)
;;;     (pushl -1)				; stack-end-marker

    ;; If we are not on a 386, perform WBINVD to flush caches.
    ;; (:testl :edi :edi)			; clear ZF
    (:pushfl)				; push original EFLAGS
    (:popl :eax)			; get original EFLAGS
    (:movl :eax :ecx)			; save original EFLAGS
    (:xorl #x40000 :eax)		; flip AC bit in EFLAGS
    (:pushl :eax)		      ; save new EFLAGS value on stack
    (:popfl)				; replace current EFLAGS value
    (:pushfl)				; get new EFLAGS
    (:popl :eax)			; store new EFLAGS in EAX
    (:xorl :ecx :eax)	  ; can't toggle AC bit, processor=80386, ZF=1
    (:jz 'skip-wbinvd)			; jump if 80386 processor
    (:wbinvd)
    skip-wbinvd

    (:movzxb :dl :eax)			; cursor column
    (:movzxb :dh :ebx)			; cursor row
     
    (:imull 160 :ebx :ebx)
    (:movl 'i-am-32 :esi)
     
    os-loop
    (:leal ((:eax 2) :ebx ,+screen-base+) :edi)
    (:xorl :ecx :ecx)
    (:movb ,(length +message+) :cl)
    ((:repz) :movsw)			; print i-am-32

    (:movl ,call-address :eax)
    (:jmp :eax)				; call OS

;;;     (:movl ,(length +halt-message+) :ecx)
;;;     (:movl 'halt-msg :esi)
;;;     (:movl ,(+ +screen-base+ (* 2 80 11) (* 2 35)) :edi)
;;;     ((:repz) movsw)
;;;     
;;;     (:movw #x7400 (:edi))
;;;     eternal
;;;     (:incb (:edi))
;;;     (:halt)
;;;     (:jmp 'eternal)			; OS returned?
    ;; (% align 2)
    i-am-32 (:% :bytes 8 ,@(make-vga-string +message+))
;;;     halt-msg (% fun ((lambda () 
;;;			(loop for char across ,+halt-message+
;;;			    collect (complex (logior #x4700 (char-code char)) 2)))))
    ))

(defun make-bootblock (image-size load-address call-address
		       &key (skip-sectors 0) (include-records))
  (when *floppy-size*
    (let ((floppy-room (- *floppy-size* 512))) ; Size of floppy minus the bootloader.
      (if (> image-size floppy-room)
          (warn "The image is ~D bytes too big to fit on a ~,2F MB floppy."
                (- image-size floppy-room)
                (/ *floppy-size* (* 1024 1000)))
          (format t "~&;; Bootloader has room for ~,1F KB more."
                  (/ (- floppy-room image-size) 1024)))))
  (multiple-value-bind (bios-loader bb-symtab)
      (let ((asm-x86:*position-independent-p* nil)
	    (asm-x86:*cpu-mode* :16-bit))
	(asm:assemble-proglist (mkasm16-bios-bootloader image-size load-address skip-sectors)
			       :start-pc #x7c00))
    (multiple-value-bind (protected-loader protected-symtab)
	(let ((asm-x86:*position-independent-p* nil)
	      (asm-x86:*cpu-mode* :32-bit))
	  (asm:assemble-proglist (mkasm-loader image-size load-address call-address)
				 :start-pc (cdr (or (assoc 'new-world bb-symtab)
						    (error "No new-world defined in bios-loader.")))))
      (let* ((loader-length (+ (length bios-loader)
			       (length protected-loader)))
	     (bootblock (progn
			  (assert (<= loader-length 510) ()
				  "Bootblock size of ~D octets is too big, max is 510!" loader-length)
			  (make-array 512 :element-type '(unsigned-byte 8)
				      :fill-pointer loader-length))))
	(setf (subseq bootblock 0) bios-loader
	      (subseq bootblock (length bios-loader)) protected-loader)
	(loop until (zerop (mod (fill-pointer bootblock) 4))
	   do (vector-push 0 bootblock))
	(dolist (record include-records)
	  (let ((*endian* :little-endian))
	    (with-binary-output-to-vector (stream bootblock)
	      (write-binary-record record stream))))	
	(setf (fill-pointer bootblock) 512
	      (subseq bootblock 510) #(#x55 #xaa)) ; bootblock signature
	(format t "~&;; Bootblock size is ~D octets.~%" loader-length)
	(format t "~&;; Bootblock build ID: ~D.~%" *bootblock-build*)
	(with-open-file (s #p"bootblock-id.txt"
			   :direction :output
			   :if-exists :supersede)
	  (with-standard-io-syntax
	    (write *bootblock-build* :stream s)))
	(values bootblock (append bb-symtab protected-symtab))))))
      
