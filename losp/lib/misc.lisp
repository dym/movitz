;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003, 
;;;;    Department of Computer Science, University of Tromsø, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      misc.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Mon May 12 17:13:31 2003
;;;;                
;;;; $Id: misc.lisp,v 1.1 2004/01/13 11:05:04 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :lib/package)
(provide :lib/misc)

(in-package muerte.lib)

(defpackage muerte.lib
  (:export checksum-octets
	   make-counter-u32
	   u32-add
	   ))

(defun checksum-octets (packet &optional (start 0) (end (length packet)))
  "Generate sum of 16-bit big-endian words for a sequence of octets."
  (cond
   ((or (and (evenp start) (evenp end))
	(and (oddp start) (oddp end)))
    (loop for i of-type (unsigned-byte 16) from start below end by 2
	sum (aref packet i) into hi of-type (unsigned-byte 24)
	sum (aref packet (1+ i)) into lo of-type (unsigned-byte 24)
	finally (return (+ lo (ash hi 8)))))
   (t (+ (loop for i of-type (unsigned-byte 16) from start below (1- end) by 2
	     sum (aref packet i) into hi
	     sum (aref packet (1+ i)) into lo
	     finally (return (+ lo (ash hi 8))))
	 (ash (aref packet (1- end)) 8))))
  #+ignore
  (with-inline-assembly (:returns :eax)
    (:load-lexical)))


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
