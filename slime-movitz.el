;;; -*- mode: emacs-lisp; mode: outline-minor; outline-regexp: ";;;;*";
indent-tabs-mode: nil -*-
;; movitz-slime.el -- Slime key bindings for Movitz, adapted from
;;                    movitz-mode.el by Frode Vatvedt Fjeld
;; Copyright (C) 2004 Aleksandar Bakic

(defun add-movitz-key-bindings ()
  (interactive "P")
  (slime-define-key "\M-\C-z\C-d" 'movitz-dump-image)
  (slime-define-key "\M-\C-z\C-v" 'movitz-disassemble-defun)
  (slime-define-key "\M-\C-z\C-b" 'movitz-compile-file)
  (slime-define-key "\M-\C-z\C-c" 'movitz-compile-defun)
  (slime-define-key "\M-\C-z\C-m" 'movitz-macroexpand)
  (slime-define-key "\M-\C-z\C-a" 'movitz-arglist))

(defun in-movitz-package-p ()
  (let ((pkg (slime-buffer-package)))
    (and pkg
         (or (and (< 6 (length pkg))
                  (string= "MUERTE." (upcase (substring pkg 0 7))))
             (member (upcase pkg)
                     '("MUERTE" "X86" "X86-PC"))))))

(defun movitz-defun-name-and-type ()
  (interactive)
  (save-excursion
    (let ((definition-type
	    (let ((x (buffer-substring-no-properties
		      (progn 
			(beginning-of-defun)
			(forward-char)
			(point))
		      (progn
			(forward-symbol 1)
			(point)))))
	      (cond
	       ((string-equal "defun" x)
		"function")
	       ((string-match "^define-" x)
		(substring x 7))
	       ((string-match "^def" x)
		(substring x 3))
	       (t x))))
	  (definition-name
	    (buffer-substring-no-properties
	     (progn
	       (forward-char)
	       (point))
	     (progn
	       (forward-sexp 1)
	       (point))))
	  (lambda-list
	   (buffer-substring-no-properties
	    (progn
	      (forward-char)
	      (point))
	    (progn 
	      (forward-sexp 1)
	      (point)))))
      (if (and (string-equal "method" definition-type)
	       (char-equal 58 (string-to-char lambda-list)))
	  (let ((qualifier lambda-list) ; one potential qualifier only
		(lambda-list
		 (buffer-substring-no-properties
		  (progn
		    (forward-char)
		    (point))
		  (progn
		    (forward-sexp 1)
		    (point)))))
	    (values
	     definition-name definition-type lambda-list (list qualifier)))
	(values definition-name definition-type lambda-list "")))))

(defun movitz-arglist (fname &optional show-fn)
  "Show the argument list for the nearest function call, if any.  If
SHOW-FN is non-nil, it is funcalled with the argument list instead of
printing a message."
  (interactive (list (slime-read-symbol-name "Movitz arglist for: ")))
  (slime-eval-async
   `(cl:let ((funobj (movitz::movitz-env-named-function
                      (cl:let ((cl:*package*
                                (cl:find-package
                                 ,(make-symbol
                                    (concat ":" (slime-buffer-package))))))
                        (cl:read-from-string ,fname)))))
      (cl:if funobj
          (cl:format nil "~:A"
                  (movitz::movitz-print 
                   (movitz::movitz-funobj-lambda-list funobj)))
        "(-- <Unknown-Function>)"))
   (slime-buffer-package)
   (with-lexical-bindings (show-fn fname)
     (lambda (arglist)
       (if show-fn
	   (funcall show-fn arglist)
	 (slime-background-message
	  "%s" (slime-format-arglist fname arglist)))))))

(defun movitz-dump-image (dont-run-bochs-p)
  "Dump a Movitz image."
  (interactive "P")
  (slime-background-message "Dumping a Movitz image...")
  (slime-eval-async
   '(movitz::dump-image)
   (slime-buffer-package)
   (with-lexical-bindings (dont-run-bochs-p)
     (slime-background-message
      "Dumping the Movitz image done. Bootblock ID: %d."
      (slime-eval 'movitz::*bootblock-build*))
     (if dont-run-bochs-p
	 t
       (slime-background-message "Running Bochs...")
       ;; assuming that bochsrc.txt is in the current directory and
       ;; boot disk is bound to los0-image file
       (call-process "/bin/sh" nil 0 nil "-c" "xterm -e bochs -q")))))

(defun movitz-compile-file ()
  "Cross-compile buffer's file into movitz::*image*."
  (interactive)
  (movitz-compile-file* (buffer-file-name)))

(defun movitz-compile-file* (file)
  "Cross-compile FILE into movitz::*image*."
  (save-some-buffers)
  (slime-background-message "Movitz compiling \"%s\"..." file)
  (slime-eval-async
   `(movitz::movitz-compile-file ,file)
   (slime-buffer-package)
   (with-lexical-bindings (file)
     (lambda (result)
       (slime-background-message "Movitz compiling \"%s\" done." file)))))

(defun movitz-compile-defun (&optional inverse-optimize-p)
  "Cross-compile pointed function into movitz::*image*."
  (interactive "P")
  (multiple-value-bind (defun-name defun-type)
      (movitz-defun-name-and-type)
    (when defun-name
      (let ((pkg (format "(in-package %s)\n" (slime-buffer-package)))
            (fun (slime-defun-at-point))
            (file (make-temp-name "/tmp/movitz-compile-defun-")))
      (with-temp-file file
        (insert pkg fun))
      (movitz-compile-defun* 
       file defun-name defun-type inverse-optimize-p)))))

(defun movitz-compile-defun* (file fname ftype invopt)
  "Cross-compile function of name FNAME and type FTYPE in FILE, with
or without optimizations, then delete FILE."
  (slime-background-message "Movitz compiling %s %s..." ftype fname)
  (slime-eval-async
   `(cl:if ,invopt
        (cl:let ((movitz::*compiler-do-optimize*
                 (cl:not movitz::*compiler-do-optimize*)))
          (movitz::movitz-compile-file ,file :delete-file-p t))
      (movitz::movitz-compile-file ,file :delete-file-p t))
   (slime-buffer-package)
   (with-lexical-bindings (fname ftype)
     (lambda (result)
       (slime-background-message
        "Movitz compiling %s %s done." ftype fname)))))

(defun movitz-disassemble-defun (not-recursive-p)
  "Disassemble pointed function in movitz::*image*."
  (interactive "P")
  (multiple-value-bind (defun-name defun-type lambda-list options)
      (movitz-defun-name-and-type)
    (cond
     ((string= "function" defun-type)
      (slime-background-message
       "Movitz disassembling %s %s..." defun-type defun-name)
      (slime-eval-async
       `(cl:let ((defun-name (cl:let ((cl:*package*
                                       (cl:find-package
                                        ,(make-symbol
                                          (concat
                                           ":"
                                           (slime-buffer-package))))))
                               (cl:read-from-string ,defun-name)))
                 (cl:*print-base* 16))
          (movitz::movitz-disassemble
           defun-name :recursive ,(not not-recursive-p)))
       (slime-buffer-package)
       (with-lexical-bindings (defun-type defun-name)
         (lambda (result)
           (slime-background-message
            "Movitz disassembling %s %s done." defun-type defun-name)))))
     ((string= "method" defun-type)
      (slime-background-message
       "Movitz disassembling %s %s %s..." defun-type defun-name lambda-list)
      (slime-eval-async
       `(cl:let* ((method-name (cl:let ((cl:*package*
                                         (cl:find-package
                                          ,(make-symbol
                                            (concat
                                             ":"
                                             (slime-buffer-package))))))
                                 (cl:read-from-string ,defun-name)))
               (gf (movitz::movitz-env-named-function method-name))
               (qualifiers (cl:read-from-string ,options))
               (lambda-list (cl:let ((cl:*package*
                                      (cl:find-package
                                       ,(make-symbol
                                         (concat
                                          ":"
                                          (slime-buffer-package))))))
                              (cl:read-from-string ,lambda-list)))
               (specializing-lambda-list
                (cl:subseq lambda-list 0
                           (cl:position-if (cl:lambda (x)
                                           (cl:and
                                            (cl:symbolp x)
                                            (cl:char=
                                             (cl:character '&)
                                             (cl:char (cl:string x) 0))))
                                           lambda-list)))
               (specializers (cl:mapcar
                              (cl:function muerte::find-specializer)
                              (cl:mapcar (cl:lambda (x)
                                           (cl:if (cl:consp x)
                                                  (cl:second x)
                                                  'muerte.cl:t))
                                         specializing-lambda-list)))
               (method (muerte::movitz-find-method gf qualifiers specializers))
               (funobj (muerte::movitz-slot-value method 'muerte::function))
               (cl:*print-base* 16))
          (movitz::movitz-disassemble-funobj funobj))
       (slime-buffer-package)
       (with-lexical-bindings (defun-type defun-name lambda-list)
         (lambda (result)
           (slime-background-message
            "Movitz disassembling %s %s %s done."
            defun-type defun-name lambda-list)))))
     ((string= "primitive-function" defun-type)
      (slime-background-message
       "Movitz disassembling %s %s..." defun-type defun-name)
      (slime-eval-async
       nil
       (slime-buffer-package)
       (with-lexical-bindings (defun-type defun-name)
         (lambda (result)
           (slime-background-message
          "Movitz disassembling %s %s done." defun-type defun-name)))))
     (t (message
         "Don't know how to Movitz disassemble %s %s."
         defun-type defun-name)))))

(defun movitz-macroexpand ()
  "Macroexpand pointed s-expression."
  (interactive)
  (let ((sexp (slime-sexp-at-point))
        (file (make-temp-name "/tmp/movitz-macroexpand-")))
    (with-temp-file file
      (insert sexp))
    (movitz-macroexpand* file)))

(defun movitz-macroexpand* (file)
  "Macroexpand s-expression in FILE, then delete FILE."
  (slime-background-message "Movitz macroexpanding...")
  (slime-eval-async
   `(cl:with-output-to-string 
      (cl:*standard-output*)
      (cl:let ((cl:*print-pretty* cl:t)
               (cl:*package* (cl:find-package ,(make-symbol
                                                (concat
                                                 ":"
                                                 (slime-buffer-package))))))
            (cl:prin1
             (movitz::translate-program
              (movitz::movitz-macroexpand-1
               (cl:let ((cl:*package* (cl:find-package
                                       ,(make-symbol
                                         (concat
                                          ":"
                                          (slime-buffer-package))))))
                 (cl:with-open-file
                  (stream ,file :direction :input)
                  (cl:read stream))))
              :common-lisp :muerte.common-lisp))))
   (slime-buffer-package)
   (with-lexical-bindings (file)
     (lambda (result)
       (delete-file file)
       (slime-background-message "Movitz macroexpanding done.")
       (if (and (not (find 10 result))
                (< (length result) 80))
           (message "Movitz: %s" result)
         (let ((buffer (get-buffer-create "*Movitz Macroexpand*")))
           (with-current-buffer buffer
             (delete-region 1 (point-max))
             (lisp-mode)
             (insert result)
             (newline 2)
             (pop-to-buffer buffer))))))))
       

(load-library "cl-indent")
(defun cl-indent (sym indent) ;; by Pierpaolo Bernardi
  (put sym 'common-lisp-indent-function
       (if (symbolp indent)
           (get indent 'common-lisp-indent-function)
           indent)))
(cl-indent 'compiler-values 'with-open-file)
(cl-indent 'compiler-values-list 'with-open-file)
(cl-indent 'compiler-values-bind 'multiple-value-bind)
(cl-indent 'compiler-values-list-bind 'multiple-value-bind)
(cl-indent 'compiler-call 'make-instance)
(cl-indent 'compiler-values-setq 'multiple-value-setq)
(cl-indent 'named-integer-case 'with-slots)
(cl-indent 'with-ne2000-io 'with-slots)
(cl-indent 'vector-double-dispatch 'case)
(cl-indent 'sequence-dispatch 'case)
(cl-indent 'sequence-double-dispatch 'case)
(cl-indent 'simple-stream-dispatch 'case)
(cl-indent 'with-inline-assembly 'prog)
(cl-indent 'with-inline-assembly-case 'prog)
(cl-indent 'do-case 'prog)
(cl-indent 'compiler-typecase 'case)

(add-hook 'lisp-mode-hook 'turn-on-font-lock)
(add-hook 'lisp-mode-hook (lambda ()
                            (setq lisp-indent-function
                                  'common-lisp-indent-function)))
(add-hook 'lisp-mode-hook (lambda ()
                            (when (in-movitz-package-p)
                              (message "Switching to Movitz keymap.")
                              (use-local-map (add-movitz-key-bindings)))))
