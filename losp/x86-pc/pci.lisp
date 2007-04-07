;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2005, 
;;;;    Department of Computer Science, University of Tromsoe, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pci.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Dec 14 22:33:42 2003
;;;;                
;;;; $Id: pci.lisp,v 1.13 2007/04/07 08:03:03 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package muerte.x86-pc)

(provide :x86-pc/pci)

(defun pci-word (designator)
  "Map an integer or 4-character string to an (unsigned-byte 32)."
  (etypecase designator
    ((unsigned-byte 32)
     designator)
    ((signed-byte 32)
     (ldb (byte 32 0) designator))
    (string
     (loop for c across designator as i upfrom 0 by 8
	 summing (ash (char-code c) i)))))

(defun pci-string (integer)
  "Map a 32-bit value to a 4-character string."
  (check-type integer (or (signed-byte 32)
			  (unsigned-byte 32)))
  (let ((string (make-string 4)))
    (setf (char string 0) (code-char (ldb (byte 8 0) integer))
	  (char string 1) (code-char (ldb (byte 8 8) integer))
	  (char string 2) (code-char (ldb (byte 8 16) integer))
	  (char string 3) (code-char (ldb (byte 8 24) integer)))
    string))

(defun find-bios32-base ()
  (loop for bios32 from #xe0000 to #xffff0 by 16
      if (and (= (memref-int bios32) #x5f32335f)
	      (loop with checksum = 0
		  as i from 0 below (* 16 (memref-int bios32 :offset 9 :type :unsigned-byte8))
		  do (incf checksum
			   (memref-int bios32 :offset i :type :unsigned-byte8))
		  finally (return (= 0 (ldb (byte 8 0 ) checksum)))))
      return bios32))

(defvar *bios32-base* nil)
(defvar *pcibios-entry* nil)

(defun pci-far-call (address &key (eax 0) (ebx 0) (ecx 0) (edx 0) (esi 0) (edi 0)
				  (cs 8) (ds (segment-register :gs)))
  "Make a 'far call' to cs:address with the provided values for eax and ebx.
Returns the boolean status of CF, and the values of registers EAX, EBX, ECX, and EDX.
The stack discipline is broken during this call, so we disable interrupts
in a somewhat feeble attempt to avoid trouble."
  (check-type address (unsigned-byte 32))
  (without-interrupts
    (with-inline-assembly (:returns :multiple-values)
      ;; Enter atomically mode
      (:declare-label-set restart-pci-far-call (restart))
      (:locally (:pushl (:edi (:edi-offset :dynamic-env))))
      (:pushl 'restart-pci-far-call)
      (:locally (:pushl (:edi (:edi-offset :atomically-continuation))))
      (:pushl :ebp)
     restart
      (:movl (:esp) :ebp)
      (:locally (:movl :esp (:edi (:edi-offset :atomically-continuation))))
      (:pushl :edi)			; Save EDI so we can restore it later.
      (:pushw :ds)			; Ditto for DS
      (:load-lexical (:lexical-binding cs) :untagged-fixnum-ecx)
      (:pushl :ecx)			; Code segment
      (:load-lexical (:lexical-binding address) :untagged-fixnum-ecx)
      (:pushl :ecx)			; Code address
      (:load-lexical (:lexical-binding eax) :untagged-fixnum-ecx)
      (:pushl :ecx)			; push EAX
      (:load-lexical (:lexical-binding ebx) :untagged-fixnum-ecx)
      (:pushl :ecx)			; push EBX
      (:load-lexical (:lexical-binding edx) :untagged-fixnum-ecx)
      (:pushl :ecx)			; push EDX
      (:load-lexical (:lexical-binding esi) :untagged-fixnum-ecx)
      (:pushl :ecx)			; push ESI
      (:load-lexical (:lexical-binding edi) :untagged-fixnum-ecx)
      (:pushl :ecx)			; push EDI
      (:load-lexical (:lexical-binding ds) :untagged-fixnum-ecx)
      (:movl :ecx :ebx)
      (:load-lexical (:lexical-binding ecx) :untagged-fixnum-ecx)
      (:movw :bx :ds)
      (:popl :edi)
      (:popl :esi)
      (:popl :edx)
      (:popl :ebx)
      (:popl :eax)
      ((:ss-override) :call-segment (:esp))
      (:leal (:esp 8) :esp)		; Skip cs:address
      (:popw :ds)			; First of all, restore DS..
      (:popl :edi)			; .. and EDI.
      (:locally (:movl :edi (:edi (:edi-offset scratch2))))
      (:jnc 'cf=0)
      (:locally (:pushl (:edi (:edi-offset t-symbol))))
      (:locally (:popl (:edi (:edi-offset scratch2))))
     cf=0
      (:pushl :eax)
      (:pushl :ebx)
      (:pushl :edx)
      (:locally (:movl 3 (:edi (:edi-offset num-values))))
      (:call-local-pf box-u32-ecx)	; ECX
      (:locally (:movl :eax (:edi (:edi-offset values) 4)))
      (:popl :ecx)			; EDX
      (:call-local-pf box-u32-ecx)
      (:locally (:movl :eax (:edi (:edi-offset values) 8)))
      (:popl :ecx)			; EBX
      (:call-local-pf box-u32-ecx)
      (:locally (:movl :eax (:edi (:edi-offset values) 0)))
      (:popl :ecx)			; EAX
      (:call-local-pf box-u32-ecx)
      (:movl :eax :ebx)
      (:locally (:movl (:edi (:edi-offset scratch2)) :eax))
      (:movl 5 :ecx)
      (:movl (:ebp -4) :esi)
      (:stc)
      ;; Exit atomical-mode
      (:locally (:movl 0 (:edi (:edi-offset atomically-continuation))))
      (:leal (:esp 16) :esp))))

(defun find-bios32-pci ()
  (let ((bios32-base (find-bios32-base)))
    (assert bios32-base "No bios32 found.")
    (multiple-value-bind (cf eax ebx ecx edx)
	(pci-far-call (memref-int bios32-base :offset 4)
		      :eax (pci-word "$PCI"))
      (declare (ignore cf ecx))
      (ecase (ldb (byte 8 0) eax)
	(#x80 (error "The PCI bios32 service isn't present."))
	(#x81 (error "The PCI bios32 service doesn't exist."))
	(#x00 (+ ebx edx))))))

(defun pci-bios-present ()
  (multiple-value-bind (cf eax ebx ecx edx)
      (pci-far-call (find-bios32-pci) :eax #xb101)
    (unless cf
      (values (pci-string edx)
	      (ldb (byte 8 8) eax)	; AH: Present status
	      (ldb (byte 8 0) eax)	; AL: Hardware mechanism
	      (ldb (byte 8 8) ebx)	; BH: Interface Level Major Version
	      (ldb (byte 8 0) ebx)	; BL: Interface Level Minor Version
	      (ldb (byte 8 0) ecx)))))	; CL: Number of last PCI bus in the system
		
(defun find-pci-device (vendor device &optional (index 0))
  (multiple-value-bind (cf eax ebx)
      (pci-far-call (find-bios32-pci)
		    :eax #xb102
		    :ecx device
		    :edx vendor
		    :esi index)
    (unless cf
      (values (ldb (byte 8 8) ebx)	; Bus
	      (ldb (byte 5 3) ebx)	; Device
	      (ldb (byte 3 0) ebx)	; Function
	      (ecase (ldb (byte 8 8) eax)
		(#x00 :successful)
		(#x86 :device-not-found)
		(#x83 :bad-vendor-id))))))

(defun find-pci-class-code (class-code &optional (index 0))
  (multiple-value-bind (cf eax ebx)
      (pci-far-call (find-bios32-pci)
		    :eax #xb103
		    :ecx class-code
		    :esi index)
    (unless cf
      (values (ldb (byte 8 8) ebx)	; Bus
	      (ldb (byte 5 3) ebx)	; Device
	      (ldb (byte 3 0) ebx)	; Function
	      (pci-return-code eax)))))

(defun pci-return-code (code)
  (ecase (ldb (byte 8 8) code)
    (#x00 :successful)
    (#x81 :function-not-supported)
    (#x83 :bad-vendor-id)
    (#x86 :device-not-found)
    (#x87 :bad-register-number)))

(defun pci-location (bus device function)
  "Compute 16-bit location from bus, device, and function numbers."
  (dpb bus (byte 8 8) (dpb device (byte 5 3) (ldb (byte 3 0) function))))

(defun pci-class (code)
  "Return the symbolic class-code sub-class code, and interface, if known."
  (let* ((decode-table
	  #((:pre-pci2.0-device
	     :non-vga :vga-compatible)
	    (:mass-storage
	     :scsi :ide :floppy :ipi :raid)
	    (:network
	     :ethernet :token-ring :fddi :atm)
	    (:display
	     (:non-xga :vga :8514) :xga)
	    (:multimedia
	     :video :audio)
	    (:memory
	     :ram :flash)
	    (:bridge
	     :host/pci :pci/isa :pci/eisa :pci/micro-channel
	     :pci/pci :pci/pcmcia :pci/nubus :pci/cardbus)
	    (:simple-communication
	     (:serial-port :xt :16450 :16550)
	     (:parallel-port :generic :bi-directional :ecp-1.x))
	    (:base-system-peripheral
	     (:pic :generic :isa :eisa)
	     (:dma :generic :isa :eisa)
	     (:timer :generic :isa :eisa)
	     (:rtc :generic :isa))
	    (:input
	     :keyboard :digitizer :mouse)
	    (:docking-station
	     :generic)
	    (:processor
	     :386 :486 :pentium nil nil nil nil nil nil nil nil nil nil nil nil nil
	     :alpha nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil
	     :powerpc nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil
	     :co-processor)
	    (:serial-bus
	     :firewire :access.bus :ssa :usb :fibre-channel)))
	 (class-code (ldb (byte 8 16) code))
	 (class-table (and (< class-code (length decode-table))
			   (svref decode-table class-code)))
	 (sub-class-table (nth (ldb (byte 8 8) code) (cdr class-table)))
	 (sub-class sub-class-table)
	 (sub-class-if (when (consp sub-class)
			 (setf sub-class (pop sub-class-table))
			 (nth (ldb (byte 8 0) code) sub-class-table))))
    (values (car class-table) sub-class sub-class-if)))

(defun pci-bios-config-space (bus device function register command size)
  (multiple-value-bind (cf eax ebx ecx)
      (pci-far-call (find-bios32-pci)
		    :eax command
		    :ebx (pci-location bus device function)
		    :edi register)
    (declare (ignore ebx))
    (unless cf
      (values (ldb (byte size 0) ecx)
	      (pci-return-code eax)))))

(defun (setf pci-bios-config-space) (value bus device function register command size)
  (declare (ignore size))
  (multiple-value-bind (cf eax)
      (pci-far-call (find-bios32-pci)
		    :eax command
		    :ebx (pci-location bus device function)
		    :ecx value
		    :edi register)
    (unless cf
      (pci-return-code eax))))

(defun pci-bios-config-space-dword (bus device function register)
  (pci-bios-config-space bus device function register #xb10a 32))

(defun pci-bios-config-space-word (bus device function register)
  (pci-bios-config-space bus device function register #xb109 16))

(defun pci-bios-config-space-byte (bus device function register)
  (pci-bios-config-space bus device function register #xb108 8))

(defun (setf pci-bios-config-space-dword) (value bus device function register)
  (setf (pci-bios-config-space bus device function register #xb10d 32)
    value))

(defun (setf pci-bios-config-space-word) (value bus device function register)
  (setf (pci-bios-config-space bus device function register #xb10c 16)
    value))

(defun (setf pci-bios-config-space-byte) (value bus device function register)
  (setf (pci-bios-config-space bus device function register #xb10b 8)
    value))


(defmacro pci-config (register)
  (cdr (or (assoc register
		  '((:interrupt-line . #x3c)
		    (:interrupt-pin . #x3d)
		    (:base-addr . #x10)
		    (:memspace . #x00)
		    (:iospace . #x01)
		    (:type . #x06)
		    (:memspace64 . #x01)))
	   (error "Unknown pci-config register: ~S" register))))

(defun pci-device-address-maps (bus device function)
  (loop with io-keys = '(:io :io-2 :io-3 :io-4 :io-5 :io-6)
      with mem-keys = '(:mem :mem-2 :mem-3 :mem-4 :mem-5 :mem-6)
      with mem64-keys = '(:mem64 :mem64-2 :mem64-3 :mem64-4 :mem64-5 :mem64-6)
      for i upfrom (pci-config :base-addr) by 4 repeat 6
      as base = (pci-bios-config-space-dword bus device function i)
      unless (= 0 base) nconc
	(cond
	 ((logbitp 0 base)
	  (list (pop io-keys) (logand base -4)))
	 ((= 1 (ldb (byte 2 1) base))
	  (list (pop mem64-keys) (logand base -16)))
	 (t
	  (list (pop mem-keys) (logand base -16))))))
	    
(defun scan-pci-bus (&optional (bus 0))
  (loop for device from 0 to 31
      do (multiple-value-bind (vendor-id return-code)
	     (pci-bios-config-space-word bus device 0 0)
	   (when (and vendor-id
		      (not (= vendor-id #xffff))
		      (eq :successful return-code))
	     (let ((device-id (pci-bios-config-space-word bus device 0 2))
		   (status (pci-bios-config-space-word bus device 0 6))
		   (class-rev (pci-bios-config-space-dword bus device 0 8)))
	       (format *query-io*
		       "~&~D: Vendor #x~X, ID #x~X, Class #x~X, Rev. ~D, Status #x~X.~%"
		       device vendor-id device-id
		       (ldb (byte 24 8) class-rev)
		       (ldb (byte 8 0) class-rev)
		       status)
	       (format *query-io* "    Class:~{~@[ ~A~]~}."
		       (multiple-value-list (pci-class (ldb (byte 24 8) class-rev))))
	       (format *query-io* "~@[~{ ~A: #x~X~^,~}.~]"
		       (pci-device-address-maps bus device 0))))))
  (values))

(defmacro $pci-config (reg)
  "PCI config header registers for all devices."
  (or (case reg
	(:pcir-devvendor #x00)
	(:pcir-vendor #x00)
	(:pcir-device #x02)
	(:pcir-command #x04)
	(:pcim-cmd-porten #x0001)
	(:pcim-cmd-memen #x0002)
	(:pcim-cmd-busmasteren #x0004)
	(:pcim-cmd-mwricen #x0010)
	(:pcim-cmd-perrespen #x0040)
	(:pcim-cmd-serrespen #x0100)
	(:pcir-status #x06)
	(:pcim-status-cappresent #x0010)
	(:pcim-status-66capable #x0020)
	(:pcim-status-backtoback #x0080)
	(:pcim-status-perrreport #x0100)
	(:pcim-status-sel-fast #x0000)
	(:pcim-status-sel-medimum #x0200)
	(:pcim-status-sel-slow #x0400)
	(:pcim-status-sel-mask #x0600)
	(:pcim-status-stabort #x0800)
	(:pcim-status-rtabort #x1000)
	(:pcim-status-rmabort #x2000)
	(:pcim-status-serr #x4000)
	(:pcim-status-perr #x8000)
	(:pcir-revid #x08)
	(:pcir-progif #x09)
	(:pcir-subclass #x0a)
	(:pcir-class #x0b)
	(:pcir-cachelnsz #x0c)
	(:pcir-lattimer #x0d)
	(:pcir-headertype #x0e)
	(:pcim-mfdev #x80)
	(:pcir-bist #x0f)

	(:pcir-maps #x10)
	(:pcir-cardbuscis #x28)
	(:pcir-subvend-0 #x2c)
	(:pcir-subdev-0 #x2e)
	(:pcir-bios #x30)
	(:pcim-bios-enable #x01)
	(:pcir-cap-ptr #x34)
	(:pcir-intline #x3c)
	(:pcir-intpin #x3d)
	(:pcir-mingnt #x3e)
	(:pcir-maxlat #x3f))
      (error "Unknown $pci-config register ~S." reg)))
