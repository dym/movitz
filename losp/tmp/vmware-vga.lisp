;;;; vmware.lisp
;;;; Basic VMWare video driver based upon the one from idyllaos

;;;; Martin Bealby 2007
;;;; Currently supports changing video mode only
;;;; Acceleration functions left to implement  (need fifo)

(require :x86-pc/package)
(provide :tmp/vmware)

(in-package muerte.x86-pc)

(defconstant +vmware-card-ids+ '((#x15AD #x0405 "VMWare Video (v2)")))

(defconstant +vmware-magic-version-2+ #x90000002)
(defconstant +vmware-magic-version-1+ #x90000001)

(defconstant +vmware-register-id+ 0)
(defconstant +vmware-register-enable+ 1)
(defconstant +vmware-register-width+ 2)
(defconstant +vmware-register-height+ 3)
(defconstant +vmware-register-max-width+ 4)
(defconstant +vmware-register-max-height+ 5)
(defconstant +vmware-register-depth+ 6)
(defconstant +vmware-register-bits-per-pixel+ 7)
(defconstant +vmware-register-pseudocolor+ 8)
(defconstant +vmware-register-red-mask+ 9)
(defconstant +vmware-register-green-mask+ 10)
(defconstant +vmware-register-blue-mask+ 11)
(defconstant +vmware-register-bytes-per-line+ 12)
(defconstant +vmware-register-fb-start+ 13)
(defconstant +vmware-register-fb-offset+ 14)
(defconstant +vmware-register-vram-size+ 15)
(defconstant +vmware-register-fb-size+ 16)
(defconstant +vmware-register-capabilities+ 17)
(defconstant +vmware-register-mem-start+ 18)
(defconstant +vmware-register-mem-size+ 19)
(defconstant +vmware-register-config-done+ 20)
(defconstant +vmware-register-sync+ 21)
(defconstant +vmware-register-busy+ 22)
(defconstant +vmware-register-guest-id+ 23)
(defconstant +vmware-register-cursor-id+ 24)
(defconstant +vmware-register-cursor-x+ 25)
(defconstant +vmware-register-cursor-y+ 26)
(defconstant +vmware-register-cursor-on+ 27)
(defconstant +vmware-register-host-bits-per-pixel+ 28)
(defconstant +vmware-register-top+ 30)
(defconstant +vmware-svga-palette-base+ 1024)
(defconstant +vmware-fifo-command-size+ 4) ; 32 bits

(defvar vmware-svga-index 0)
(defvar vmware-svga-value 0)
(defvar vmware-framebuffer-location 0)
(defvar vmware-framebuffer-size 0)
(defvar vmware-framebuffer-width 0)
(defvar vmware-framebuffer-height 0)
(defvar vmware-framebuffer-bpp 0)
(defvar vmware-fifo-location 0)
(defvar vmware-fifo-size 0)


;
; internal functions
;
(defmethod vmware-attach (&key io &allow-other-keys)
  "Attach the driver to a VMWare device."
  (setf (vmware-svga-index) io)
  (setf (vmware-svga-value) (+ 1 io)))

(defmethod vmware-register-write (index value)
  "Write to the VMWare video register."
  (setf (io-port (vmware-svga-index) :unsigned-byte32) index)
  (setf (io-port (vmware-svga-value) :unsigned-byte32) value))

(defmethod vmware-register-read (index)
  "Read from the VMWare video register."
  (setf (io-port (vmware-svga-index) :unsigned-byte32) index)
  (io-port (vmware-svga-value) :unsigned-byte32))


;;
;;  Public methods
;;
(defmethod initialise ()
  "Initialise the vmware driver."
  (loop for i in +vmware-card-ids+ do
		(multiple-value-bind (bus device function)
			(find-pci-device (car i) (car (cdr i)))
		  (apply #'attach
				 (list pci-device-address-maps bus device function)))))

(defmethod get-framebuffer ()
  "Return a pointer to the framebuffer."
  (return vmware-framebuffer-location))


(defmethod set-resolution (width height bpp)
  "Sets the current display resolution."
  ;; test for vmware version 2 (only supported version at the moment)
  (vmware-register-write +vmware-register-id+ +vmware-magic-version-2+)
  (if (equal (vmware-register-read +vmware-register-id+)
			 +vmware-magic-version-2+)
  (progn
	(setf vmware-framebuffer-location
		  (vmware-register-read +vmware-register-fb-start+))
	(setf vmware-framebuffer-size
		  (vmware-register-read +vmware-register-fb-size+))
	(setf vmware-fifo-location
		  (vmware-register-read +vmware-register-mem-start+))
	(setf vmware-fifo-size	  
		  (vmware-register-read  +vmware-register-mem-size+))
	(setf vmware-framebuffer-width
		  (vmware-register-write +vmware-register-width+ width))
	(setf vmware-framebuffer-height
		  (vmware-register-write +vmware-register-height+ height))
	(vmware-register-write +vmware-register-bits-per-pixel+ bpp)
	(vmware-register-read +vmware-register-fb-offset+)
	(vmware-register-read +vmware-register-bytes-per-line+)
	(vmware-register-read +vmware-register-depth+)
	(vmware-register-read +vmware-register-pseudocolor+)
	(vmware-register-read +vmware-register-red-mask+)
	(vmware-register-read +vmware-register-green-mask+)
	(vmware-register-read +vmware-register-blue-mask+)
	(vmware-register-write +vmware-register-enable+ #x1))
  (error "Bad Magic - Not VMware version 2 graphics.")))


(defmethod update-region (x y width height)
  "Update a region on screen.  With no parameters it updates the whole screen."
  (if (= width 0)
	  (progn
		(vmware-fifo-push +vmware-cmd-update+)
		(vmware-fifo-push 0)
		(vmware-fifo-push 0)
		(vmware-fifo-push vmware-framebuffer-width)
		(vmware-fifo-push vmware-framebuffer-height))
	  (progn
		(vmware-fifo-push +vmware-cmd-update+)
		(vmware-fifo-push x)
		(vmware-fifo-push y)
		(vmware-fifo-push width)
		(vmware-fifo-push height))))


;;
;; VMWare fifo functions
;; 
(defun initialise-fifo ()
  "Initialise the VMware fifo command stream."
  (setf vmware-fifo-pointer-min (* 4 +vmware-fifo-command-size+))
  (setf vmware-fifo-pointer-max (+ 16 (* 10 1024)))
  (setf vmware-fifo-pointer-next-command vmware-fifo-min)
  (setf vmware-fifo-pointer-stop vmware-fifo-min)
  (vmware-register-write +vmware-register-config-done+ 1)
  (vmware-register-read +vmware-register-config-done+))


(defun vmware-fifo-sync ()
  "Sync the fifo buffer."
  (vmware-register-write +vmware-register-sync+ 1)
  (loop until (= 0 (vmware-register-read +vmware-register-busy+))))


(defun vmware-fifo-push (data)
  "Write a piece of data to the VMWare fifo pipe."
  (if (vmware-fifo-full-p)
	  (vmware-fifo-sync))

  ;; TODO: actual append to fifo buffer ;)
  )

(defun vmware-fifo-full-p ()
  "Test for a full fifo buffer."
  (cond (= (+ vmware-fifo-pointer-next-command +vmware-fifo-command-size+)
		   vmware-fifo-pointer-stop)
		(t)
		(and (= vmware-fifo-pointer-next-command
				(- vmware-fifo-pointer-max +vmware-fifo-command-size+))
			 (= vmware-fifo-pointer-stop vmware-fifo-pointer-min))
		(t)
		(t)
		(nil)))
