;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2003, 2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      am7990.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Aug 12 23:39:20 2005
;;;;                
;;;; $Id: am7990.lisp,v 1.1 2005/08/24 07:33:09 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(provide :x86-pc/am7990)

(in-package muerte.x86-pc)

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
  (let ((am7990-io (gensym "am7990-io-")))
    `(with-io-register-syntax (,am7990-io ,io-base)
       (macrolet
	   ((,name (op &optional reg)
	      (ecase op
		(:rdp
		 `(,',am7990-io (,',regdef :rdp) :unsigned-byte16))
		(:csr
		 `(,',am7990-io (progn
				  (setf (,',am7990-io (,',regdef :rap) :unsigned-byte16)
				    (,',regdef ,reg))
				  (,',regdef :rdp))
				:unsigned-byte16))
		)))
	 ,@body))))

(defmacro with-am7990-ports ((name rap rdp bdp) &body body)
  (let ((rapvar (gensym "rap-"))
	(rdpvar (gensym "rdp-")))
    `(let ((,rapvar (muerte::check-the (unsigned-byte 16) ,rap))
	   (,rdpvar (muerte::check-the (unsigned-byte 16) ,rdp)))
       (macrolet ((,name (reg)
		    (case reg
		      (:rap ',rapvar) (:rdp ',rdpvar) (:bdp ',bdp)
		      (t `($am7990 ,reg)))))
	 ,@body))))

(defun lance-foo (io-base rap rdp bdp)
  (declare (ignorable bdp))
  (with-am7990-ports ($lance rap rdp bdp)
    (with-am7990 (lance io-base $lance)
      (setf (lance :csr :csr0) ($am7990 :csr0 :stop)))))

(defun blurgh (rap io-base)
  (let ((checked-rap (let ((check-rap rap))
		       (check-type check-rap (unsigned-byte #x10))
		       check-rap)))
    (let ((checked-io-base (let ((check-io-base io-base))
			     (check-type check-io-base (unsigned-byte #x10))
			     check-io-base)))
      (values checked-io-base checked-rap)
      #+ignore
      (setf (io-port (+ io-base-1188579
			(progn (setf (io-port (+ io-base-1188579 rap-1188023)
					      :unsigned-byte16)
				 #x0)
			       rdp))
		     :unsigned-byte16)
	#x4))
    #+ignore
    (with-io-register-syntax (am7990-io-1188025 io-base)
      (setf (am7990-io-1188025 (progn
				 (setf (am7990-io-1188025 rap-1188023 :unsigned-byte16) 0)
				 rdp)
			       :unsigned-byte16)
	4))))


(defun lance-probe (io-base rap rdp bdp)
  (declare (ignorable bdp))
  (with-am7990-ports ($lance rap rdp bdp)
    (with-am7990 (lance io-base $lance)
      (setf (lance :csr :csr0) ($am7990 :csr0 :stop))
      (when (and (/= 0 (logand (lance :rdp) ($am7990 :csr0 :stop)))
		 (= 0 (lance :csr :csr3)))
	(setf (lance :csr :csr0) ($am7990 :csr0 :inea))
	(if (/= 0 (logand (lance :csr :csr0) ($am7990 :csr0 :inea)))
	    'c-lance
	  'lance)))))

(defun am7990-probe (io-base rap rdp bdp)
  (let ((type (lance-probe io-base rap rdp bdp)))
    (when type
      (with-am7990-ports ($ports rap rdp bdp)
	(with-am7990 (am7990 io-base $ports)
	  (let ((chip-id (dpb (am7990 :csr :csr89)
			      (byte 16 16)
			      (am7990 :csr :csr88))))
	    (when (/= 0 (logand chip-id ($am7990 :csr88 :amd-mask)))
	      (macrolet ((match (&rest kv)
			   `(let ((x (ldb (byte 16 12) chip-id)))
			      (cond ,@(loop for (k v) in kv collect
					    `((eql ($am7990 :csr88 ,k) x) ,v))))))
		(or (match
		     (:|Am79C960| 'PCnet-ISA)
		     (:|Am79C961| 'PCnet-ISAplus)
		     (:|Am79C961A| 'PCnet-ISA-II))
		    (values (match
			     (:|Am79C965| 'PCnet-32)
			     (:|Am79C970| 'PCnet-PCI)
			     (:|Am79C970A| 'PCnet-PCI-II)
			     (:|Am79C971| 'PCnet-FAST)
			     (:|Am79C972| 'PCnet-FASTplus)
			     (:|Am79C973| 'PCnet-FASTplus)
			     (:|Am79C978| 'PCnet-Home))
			    t))))))))))

(defclass ne2100-pci (pci-device muerte.ethernet:ethernet-device)
  ;; ident = NE2100
  ;; mem_mode = DMA_FIXED
  ((io-base
    :initarg :io-base
    :reader io-base)
   (irq
    :initarg :irq
    :accessor irq)))

(defun pcnet ()
  (multiple-value-bind (bus device function status)
      (find-pci-device #x1022 #x2000)
    (when (eq status :successful)
      (make-pci-pcnet bus device function))))
      
(defun make-pci-pcnet (bus device function)
  (let ((io (muerte::check-the (unsigned-byte 16)
			       (getf (pci-device-address-maps bus device function) :io))))
    ;; Make this device a bus master.
    (setf (pci-bios-config-space-dword bus device function
				       ($pci-config :pcir-command))
      (logior (pci-bios-config-space-dword bus device function
					   ($pci-config :pcir-command))
	      ($pci-config :pcim-cmd-porten)
	      ($pci-config :pcim-cmd-busmasteren)))
    (multiple-value-bind (ic 32bit-p)
	(am7990-probe io ($pcnet :rap) ($pcnet :rdp) ($pcnet :bdp))
      (when 32bit-p
	(make-instance 'ne2100-pci
	  :io-base io
	  :bus bus
	  :device device
	  :function function
	  :mac-address (coerce (loop for i from 0 below 6
				   collect (io-port (+ io i) :unsigned-byte8))
			       'muerte.ethernet:mac-address)
	  )))))

(defun lnc-attach-sc (sc)
  )
  

(defmethod init ((sc ne2100-pci))
  (setf (recv-next sc) 0
	(trans-tring sc) (+ (recv-ring sc) 8)
	))
	
