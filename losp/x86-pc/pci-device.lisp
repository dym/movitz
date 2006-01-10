;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003, 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pci-device.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Sun Aug 14 20:18:52 2005
;;;;                
;;;; $Id: pci-device.lisp,v 1.1 2006/01/10 11:04:38 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(in-package muerte.x86-pc)

(require :x86-pc/pci)
(provide :x86-pc/pci-device)

(defmacro define-slot-shadowing ((class-name slot-name &optional writer-name) shadow-place)
  (let ((value-var (gensym)))
    `(progn
       ,(when writer-name
	  `(defmethod (setf ,writer-name) :after (,value-var (,class-name ,class-name))
	     (setf ,shadow-place ,value-var)
	     (slot-makunbound ,class-name ',slot-name)))
       (defmethod slot-unbound (,(gensym) (,class-name ,class-name) (,(gensym) (eql ',slot-name)))
	 (setf (slot-value ,class-name ',slot-name) ,shadow-place)))))

(defmacro define-pci-config-register-shadowing (slot/writer-name register size)
  (let ((place-op (cdr (or (assoc size '((1 . pci-bios-config-space-byte)
					 (2 . pci-bios-config-space-word)
					 (4 . pci-bios-config-space-dword)))
			   (error "Illegal PCI config register size ~S." size)))))
    `(define-slot-shadowing (pci-config-space-mixin ,slot/writer-name ,slot/writer-name)
	 (,place-op (pci-bus pci-config-space-mixin)
		    (pci-device pci-config-space-mixin)
		    (pci-function pci-config-space-mixin)
		    ($pci-config ,register)))))

(defclass pci-config-space-mixin ()
  ((pci-config-vendor
    :accessor pci-config-vendor)
   (pci-config-device
    :accessor pci-config-device)
   (pci-config-cmdreg
    :accessor pci-config-cmdreg)
   (pci-config-statreg
    :accessor pci-config-statreg)
   (pci-config-baseclass
    :accessor pci-config-baseclass)
   (pci-config-subclass
    :accessor pci-config-subclass)
   (pci-config-progif
    :accessor pci-config-progif)
   (pci-config-revid
    :accessor pci-config-revid)
   (pci-config-hdrtype
    :accessor pci-config-hdrtype)
   (pci-config-cachelnsz
    :accessor pci-config-cachelnsz)
   (pci-config-lattimer
    :accessor pci-config-lattimer)
   (pci-config-intpin
    :accessor pci-config-intpin)
   (pci-config-intline
    :accessor pci-config-intline)))

(define-pci-config-register-shadowing pci-config-vendor :pcir-vendor 2)
(define-pci-config-register-shadowing pci-config-device :pcir-device 2)
(define-pci-config-register-shadowing pci-config-cmdreg :pcir-command 2)
(define-pci-config-register-shadowing pci-config-statreg :pcir-status 2)
(define-pci-config-register-shadowing pci-config-baseclass :pcir-class 1)
(define-pci-config-register-shadowing pci-config-subclass :pcir-subclass 1)
(define-pci-config-register-shadowing pci-config-progif :pcir-progif 1)
(define-pci-config-register-shadowing pci-config-revid :pcir-revid 1)
(define-pci-config-register-shadowing pci-config-hdrtype :pcir-headertype 1)
(define-pci-config-register-shadowing pci-config-cachelnsz :pcir-cachelnsz 1)
(define-pci-config-register-shadowing pci-config-lattimer :pcir-lattimer 1)
(define-pci-config-register-shadowing pci-config-intpin :pcir-intpin 1)
(define-pci-config-register-shadowing pci-config-intline :pcir-intline 1)

(defclass pci-device (pci-config-space-mixin)
  ((bus
    :initarg :bus
    :reader pci-bus)
   (device
    :initarg :device
    :reader pci-device)
   (function
    :initarg :function
    :reader pci-function)))
