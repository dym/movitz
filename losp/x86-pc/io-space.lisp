;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      io-space.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Tue May  6 10:50:36 2003
;;;;                
;;;; $Id: io-space.lisp,v 1.3 2004/03/22 17:08:14 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :x86-pc/io-space)
(require :x86-pc/package)

(in-package muerte.x86-pc)

(deftype io-address ()
  '(unsigned-byte 16))

(deftype io-address-range ()
  '(cons io-address io-address))

(deftype io-space ()
  'list)				; a list of io-addresses and io-ranges.

(defun io-addresses-overlap-p (x y)
  (etypecase x
    (io-address
     (etypecase y
       (io-address
	(= x y))
       (io-address-range
	(<= (car y) x (cdr y)))))
    (io-address-range
     (etypecase y
       (io-address
	(<= (car x) y (cdr x)))
       (io-address-range
	(or (<= (car x) (car y) (cdr x))
	    (<= (car x) (cdr y) (cdr x))))))))

(defun io-range-start (x)
  (etypecase x
    (io-address x)
    (io-address-range (car x))))

(defun io-range-end (x)
  (etypecase x
    (io-address x)
    (io-address-range (cdr x))))

(defun io-range-in-space-p (range space)
  (loop for sub-range in space
      thereis (io-addresses-overlap-p range sub-range)))

(defun io-spaces-overlap-p (space1 space2)
  (loop for sub-range in space1
      thereis (io-range-in-space-p sub-range space2)))

(defun io-space< (x y)
  (< (loop for address-range in x minimize (io-range-start address-range))
     (loop for address-range in y minimize (io-range-start address-range))))

(defclass io-space-device ()
  ((device-name
    :initarg :device-name
    :initform nil
    :accessor device-name)
   (allocated-io-space
    :initarg :io-space
    :initform nil
    :accessor io-space)))

(defmethod print-object ((device io-space-device) stream)
  (print-unreadable-object (device stream :type t)
    (format stream "~@[ ~A~]~@[ @ I/O #x~X~]"
	    (when (slot-boundp device 'device-name)
	      (device-name device))
	    (when (slot-boundp device 'allocated-io-space)
	      (io-range-start (first (io-space device))))))
  device)

(defvar *io-space-register* nil)	; a list of io-space devices.

(defmethod allocate-io-space ((device io-space-device) io-space &optional (errorp t))
  (with-symbol-mutex (*io-space-register*)
    (let ((blocking-devices (io-space-occupants io-space)))
      (cond
       ((null blocking-devices)
	(setf (io-space device) io-space)
	(setf *io-space-register*
	  (merge 'list *io-space-register* (list device) #'io-space< :key #'io-space))
	t)
       (t (if errorp
	      (error "Cannot allocate the io-space ~S for ~S, it is occupied by ~S."
		     io-space device blocking-devices)
	    nil))))))

(defmethod free-io-space ((device io-space-device))
  (setf *io-space-register*
    (delete device *io-space-register*))
  (setf (io-space device) nil))

  
(defmacro with-io-space-lock (options &body body)
  (declare (ignore options))
  `(with-symbol-mutex (*io-space-register*) ,@body))

(defun io-space-occupants (io-space)
  "Return any devices that occupies io-space.
Should be called whith io-space-lock held."
  (remove-if (lambda (s)
	       (not (io-spaces-overlap-p s io-space)))
	     *io-space-register*
	     :key #'io-space))


(defun make-io-space (&rest spec)
  (declare (dynamic-extent spec))
  (let ((io-space nil))
    (do () ((endp spec) io-space)
      (setq io-space
	(merge 'list io-space
	       (list
		(ecase (pop spec)
		  (:range
		   (let* ((start (pop spec))
			  (end (+ start (pop spec) -1)))
		     (cons start end)))
		  (:address
		   (pop spec))))
	       #'io-space<)))))
	
