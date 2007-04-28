;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003, 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      pcnet.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Aug 12 23:39:20 2005
;;;;                
;;;; $Id: pcnet.lisp,v 1.1 2007/04/28 16:29:18 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :x86-pc/pcnet)

(in-package muerte.x86-pc)

(defmacro select (keyform &rest clauses)
  (let* ((select-var (gensym "select-key-"))
	 (cc (loop for (key . consequents) in clauses
		 collecting
		   (cond
		    ((member key '(t otherwise))
		     (cons t consequents))
		    (t
		     (cons `(eql ,key ,select-var)
			   consequents))))))
    `(let ((,select-var ,keyform))
       (cond ,@cc))))

(defmacro $am7990 (reg &optional sub-reg)
  (or (cond
       ((integerp reg)
	reg)
       ((not sub-reg)
	(case reg
	  (:csr0 0) (:csr1 1) (:csr2 2) (:csr3 3)
	  (:csr88 88) (:csr89 89)
	  (:bcr49 49) (:bcr32 32) (:bcr33 33) (bcr34 34)))
       (t (if (integerp sub-reg)
	      sub-reg
	    (case reg
	      (:csr0
	       (case sub-reg
		 (:err #x8000)
		 (:babl #x4000)
		 (:cerr #x2000)
		 (:miss #x1000)
		 (:merr #x0800)
		 (:rint #x0400)
		 (:tint #x0200)
		 (:idon #x0100)
		 (:intr #x0080)
		 (:inea #x0040)
		 (:rxon #x0020)
		 (:txon #x0010)
		 (:tdmd #x0008)
		 (:stop #x0004)
		 (:strt #x0002)
		 (:init #x0001)))
	      (:csr88
	       (case sub-reg
		 (:AMD-MASK #x003)
		 (:PART-MASK #xffff)
		 (:|Am79C960| #x0003)
		 (:|Am79C961| #x2260)
		 (:|Am79C961A| #x2261)
		 (:|Am79C965| #x2430)
		 (:|Am79C970| #x0242)
		 (:|Am79C970A| #x2621)
		 (:|Am79C971| #x2623)
		 (:|Am79C972| #x2624)
		 (:|Am79C973| #x2625)
		 (:|Am79C978| #x2626)
		 ))))))
      (error "Unknown Am7990 register: ~S~@[ ~S~]" reg sub-reg)))

(defmacro $pcnet (reg)
  "PCNet is one Am7990 implementation."
  (or (cond
       ((integerp reg) reg)
       (t (case reg
	    (:rdp #x10)
	    (:rap #x12)
	    (:reset #x14)
	    (:bdp #x16)
	    (:vsw #x18))))
      `($am7990 ,reg)))

(defmacro with-am7990 ((name io-base regdef) &body body)
  (let ((pcnet-io (gensym "pcnet-io-")))
    `(with-io-register-syntax (,pcnet-io ,io-base)
       (macrolet
	   ((,name (op &optional reg)
	      (ecase op
		(:rdp
		 `(,',pcnet-io (,',regdef :rdp) :unsigned-byte16))
		(:csr
		 `(,',pcnet-io (progn
				 (setf (,',pcnet-io (,',regdef :rap) :unsigned-byte16)
				   (,',regdef ,reg))
				 (,',regdef :rdp))
			       :unsigned-byte16))
		)))
	 ,@body))))

(defmacro with-am7990-ports ((name rap rdp bdp) &body body)
  `(macrolet ((,name (reg)
		(case reg
		  (:rap ',rap) (:rdp ',rdp) (:bdp ',bdp)
		  (t `($am7990 ,reg)))))
     ,@body))

(defun lance-probe (io-base rap rdp bdp)
  (declare (ignorable bdp))
  (with-am7990-ports ($lance rap rdp bdp)
    (with-am7990 (pcnet io-base $lance)
      (setf (pcnet :csr :csr0) ($am7990 :csr0 :stop))
      (when (and (/= 0 (logand (pcnet :rdp) ($am7990 :csr0 :stop)))
		 (= 0 (pcnet :csr :csr3)))
	(setf (pcnet :csr :csr0) ($am7990 :csr0 :inea))
	(if (/= 0 (logand (pcnet :csr :csr0) ($am7990 :csr0 :inea)))
	    'c-lance
	  'lance)))))

(defun am7990-probe (io-base rap rdp bdp)
  (let ((type (lance-probe io-base rap rdp bdp)))
    (when type
      (with-am7990-ports ($ports rap rdp bdp)
	(with-am7990 (pcnet io-base $ports)
	  (let ((chip-id (dpb (pcnet :csr :csr89)
			      (byte 16 16)
			      (pcnet :csr :csr88))))
	    (when (/= 0 (logand chip-id ($am7990 :csr88 :amd-mask)))
	      (select (ldb (byte 16 12) chip-id)
		(($am7990 :csr88 :|Am79C960|) 'PCnet-ISA)
		(($am7990 :csr88 :|Am79C961|) 'PCnet-ISAplus)
		(($am7990 :csr88 :|Am79C961A|) 'PCnet-ISA-II)
		(($am7990 :csr88 :|Am79C965|) (values 'PCnet-32 t))
		(($am7990 :csr88 :|Am79C970|) (vaues 'PCnet-PCI t))
		(($am7990 :csr88 :|Am79C970A|) (values 'PCnet-PCI-II t))
		(($am7990 :csr88 :|Am79C971|) (values 'PCnet-FAST t))
		(($am7990 :csr88 :|Am79C972|) (values 'PCnet-FASTplus t))
		(($am7990 :csr88 :|Am79C973|) (values 'PCnet-FASTplus t))
		(($am7990 :csr88 :|Am79C978|) (values 'PCnet-Home t))
		(t type)))))))))


(defclass ne2100-pci (muerte.ethernet:ethernet-device)
  ())

(defun pcnet-probe-pci ()
  (multiple-value-bind (bus device function)
      (find-pci-device #x1022 #x2000)
    (apply #'attach-ne2100-pci 
	   (pci-device-address-maps bus device function))))
      
(defun attach-ne2100-pci (&key io &allow-other-keys)
  (check-type io (unsigned-byte 16) "an I/O port")
  (multiple-value-bind (ic 32bit-p)
      (am7990-probe io ($pcnet :rap) ($pcnet :rdp) ($pcnet :bdp))
    (when 32bit-p
      (make-instance 'ne2100-pci
	:mac-address (coerce (loop for i from 0 below 6
				 collect (io-port (+ io i) :unsigned-byte8))
			     'muerte.ethernet:mac-address)))))

