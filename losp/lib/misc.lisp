;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      misc.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon May 12 17:13:31 2003
;;;;                
;;;; $Id: misc.lisp,v 1.5 2004/08/14 17:52:35 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/misc)

(in-package muerte.lib)

(defun checksum-octets (packet &optional (start 0) (end (length packet)))
  "Generate sum of 16-bit big-endian words for a sequence of octets."
  (typecase packet
    (muerte:vector-u8
     (assert (<= 0 start end (length packet)))
     (with-inline-assembly (:returns :eax)
       (:compile-form (:result-mode :ebx) packet)
       (:compile-form (:result-mode :eax) start)
       (:compile-form (:result-mode :esi) end)
       (:movl :eax :ecx)		; ecx = start
       (:subl :eax :esi)		; esi = (- end start)
       (:movl 0 :eax)
       (:jz 'end-checksum-loop)
       (:shrl #.movitz::+movitz-fixnum-shift+ :ecx)
       (:xorl :edx :edx)
       (:std)
      checksum-loop
       (:movw (:ebx 2 :ecx) :ax)
       (:xchgb :al :ah)
       (:addl 2 :ecx)
       (:addl :eax :edx)
       (:subl #.(cl:* 2 movitz:+movitz-fixnum-factor+) :esi)
       (:jnbe 'checksum-loop)
       (:movw :dx :ax)
       (:shrl 16 :edx)
       (:addw :dx :ax)
       (:movl (:ebp -4) :esi)
      end-checksum-loop
       (:shll #.movitz:+movitz-fixnum-shift+ :eax)
       (:cld)))
    (t (muerte:with-subvector-accessor (packet-ref packet start end)
	 (cond
	  ((or (and (evenp start) (evenp end))
	       (and (oddp start) (oddp end)))
	   (loop for i of-type (unsigned-byte 16) from start below end by 2
	       sum (packet-ref i) into hi of-type (unsigned-byte 24)
	       sum (packet-ref (1+ i)) into lo of-type (unsigned-byte 24)
	       finally (return (+ lo (ash hi 8)))))
	  (t (+ (loop for i of-type (unsigned-byte 16) from start below (1- end) by 2
		    sum (packet-ref i) into hi
		    sum (packet-ref (1+ i)) into lo
		    finally (return (+ lo (ash hi 8))))
		(ash (packet-ref (1- end)) 8))))))))


(defstruct (counter-u32 (:constructor make-counter-u32-object)) lo hi)

(defun make-counter-u32 (&optional (x 0))
  (make-counter-u32-object :lo (ldb (byte 16 0) x)
			   :hi (ash x -16)))

(defun u32-add (c x)
  (let ((y (+ (ldb (byte 16 0) x)
	      (counter-u32-lo c))))
    (setf (counter-u32-lo c) (ldb (byte 16 0) y)
	  (counter-u32-hi c) (ldb (byte 16 0)
				  (+ (ldb (byte 12 16) y)
				     (ash x -16)
				     (counter-u32-hi c)))))
  c)


(defmethod print-object ((c counter-u32) stream)
  (print-unreadable-object (c stream :type nil :identity nil)
    (if (plusp (counter-u32-hi c))
	(format stream "u32 #x~X~4,'0X"
		(counter-u32-hi c)
		(counter-u32-lo c))
      (format stream "u32 #x~X" (counter-u32-lo c))))
  c)
