;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003-2004, 
;;;;    Department of Computer Science, University of Tromsoe, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pci.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Dec 14 22:33:42 2003
;;;;                
;;;; $Id: pci.lisp,v 1.5 2004/11/23 13:45:51 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package muerte.x86-pc)

(provide :x86-pc/pci)

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

(defun init-pci ()
  (setf *bios32-base*
    (find-bios32-base))
  (if (not *bios32-base*)
      (error "No PCI BIOS32 found.")
    (let ((entry (memref-int *bios32-base* :offset 4))
	  (revision (memref-int *bios32-base* :offset 8 :type :unsigned-byte8))
	  (length (memref-int *bios32-base* :offset 9 :type :unsigned-byte8)))
      (values entry revision length))))

(defun pci-far-call (address &key (eax 0) (ebx 0) (cs 8))
  "Make a 'far call' to cs:address with the provided values for eax and ebx.
Returns the values of registers AL, EBX, ECX, and EDX. (Well, for now only the
lower 30 bits are actually returned.) The stack discipline is broken during
this call, so we disable interrupts in a somewhat feeble attempt to avoid trouble."
  (without-interrupts
    (with-inline-assembly (:returns :multiple-values)
      (:load-lexical (:lexical-binding cs) :untagged-fixnum-ecx)
      (:pushl :ecx)			; Code segment
      (:load-lexical (:lexical-binding address) :untagged-fixnum-ecx)
      (:pushl :ecx)			; Code address
      (:load-lexical (:lexical-binding ebx) :untagged-fixnum-ecx)
      (:pushl :ecx)			; EBX
      (:load-lexical (:lexical-binding eax) :untagged-fixnum-ecx)
      (:movl :ecx :eax)
      (:popl :ebx)
      (:call-segment (:esp))
      (:leal (:esp 8) :esp)
      (:andl #xff :eax)
      (:shll 2 :eax)
      (:shll 2 :ebx)
      (:shll 2 :ecx)
      (:shll 2 :edx)
      (:locally (:movl :ecx (:edi (:edi-offset values) 0)))
      (:locally (:movl :edx (:edi (:edi-offset values) 4)))
      (:movl 4 :ecx)
      (:stc))))

(defun pci-directory (eax &optional (ebx 0))
  "Calling with '$PCI' should find the PCI directory."
  (unless *bios32-base*
    (init-pci))
  (let ((eax (etypecase eax
	       ((unsigned-byte 32)
		eax)
	       (string
		(loop for c across eax as i upfrom 0 by 8
		    summing (ash (char-code c) i))))))
    (pci-far-call (memref-int *bios32-base* :offset 4)
		  :eax eax :ebx ebx)))
