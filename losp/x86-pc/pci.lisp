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
;;;; $Id: pci.lisp,v 1.4 2004/11/14 22:58:02 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package muerte.x86-pc)

(provide :x86-pc/pci)

(defun find-bios32 ()
  (loop for bios32 from #xe0000 to #xffff0 by 16
      if (and (= (memref-int bios32) #x5f32335f)
	      (loop with checksum = 0
				    ;; initially (warn "PCI magic found at #x~X" bios32)
		  as i from 0 below (* 16 (memref-int bios32 :offset 9 :type :unsigned-byte8))
		  do (incf checksum
			   (memref-int bios32 :offset i :type :unsigned-byte8))
		  finally (return (= 0 (ldb (byte 8 0 ) checksum)))))
      return bios32))
