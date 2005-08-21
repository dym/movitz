;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2004
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      movitz-mode.el
;;;; Description:   Modifies Franz' ELI slightly to integrate with Movitz.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Sep 27 18:12:17 2001
;;;;                
;;;; $Id: movitz-mode.el,v 1.10 2005/08/21 12:11:51 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(defvar movitz-common-lisp-mode-map nil)

(defun make-movitz-common-lisp-mode-map (&optional new)
  (interactive "P")
  (when (or new (not movitz-common-lisp-mode-map))
    ;; (setq movitz-common-lisp-mode-map (make-keymap))
    (fi::initialize-mode-map 'movitz-common-lisp-mode-map))
  (define-key movitz-common-lisp-mode-map "\C-c\C-d" 'movitz-dump-image)
  (define-key movitz-common-lisp-mode-map "\C-c\C-v" 'movitz-disassemble-defun)
  (define-key movitz-common-lisp-mode-map "\C-c\C-b" 'movitz-compile-file)
  (define-key movitz-common-lisp-mode-map "\C-\M-x" 'movitz-compile-defun)
  (define-key movitz-common-lisp-mode-map "\C-cm" 'movitz-macroexpand)
  (define-key movitz-common-lisp-mode-map "\C-ca" 'movitz-arglist)
  movitz-common-lisp-mode-map)

(defun in-movitz-package-p ()
  (or (and (< 6 (length fi:package))
	   (string= "MUERTE." (upcase (substring fi:package 0 7))))
      (member (upcase fi:package)
	      '("MUERTE" "X86" "X86-PC"))
      (member "MUERTE"
	      (fi:eval-in-lisp
	       "(cl:mapcar #'cl:package-name (cl:package-use-list \"%s\"))" (upcase fi:package)))))

(defun movitz-defun-name-and-type ()
  (interactive)
  (save-excursion
    (let ((definition-type
	    (let ((x (buffer-substring-no-properties (progn (fi:beginning-of-defun)
							    (forward-char)
							    (point))
						     (progn (forward-symbol 1)
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
	    (buffer-substring-no-properties (progn (forward-char)
						   (point))
					    (progn (forward-sexp 1)
						   (point))))
	  (lambda-list
	   (buffer-substring-no-properties (progn (forward-char)
						  (point))
					   (progn (forward-sexp 1)
						  (point)))))
      (if (and (equalp "method" definition-type)
	       (char-equal 58 (string-to-char lambda-list)))
	  (let ((qualifier lambda-list)
		;; XXX we only deal with one (potential) qualifier..
		(lambda-list (buffer-substring-no-properties (progn (forward-char)
								    (point))
							     (progn (forward-sexp 1)
								    (point)))))
	    (values definition-name
		    definition-type
		    lambda-list
		    (list qualifier)))
	(values definition-name
		definition-type
		lambda-list
		nil)))))

(defun movitz-arglist (string)
  (interactive (fi::get-default-symbol "Movitz arglist for" t t))
  (let ((message
	 (fi:eval-in-lisp
	  "(cl:let* ((cl:*print-case* :downcase)
                       (name (cl:quote %s))
                       (funobj (movitz::movitz-env-named-function name)))
            (cl:when funobj
             (cl:format nil \"~A\" (movitz::movitz-print (movitz::movitz-funobj-lambda-list funobj)))))"
	  string string)))
    (if message
	(message "Movitz args for %s: %s." string message)
      (fi:lisp-arglist string))))

(defun movitz-dump-image (dont-run-bochs-p)
  "Dump a Movitz image."
  (interactive "P")
  (message "Dumping Movitz image...")
  (fi:eval-in-lisp "(movitz::dump-image)")
;;;  (with-current-buffer "*common-lisp*"
;;;    (fi:inferior-lisp-newline))
  (cond
   (dont-run-bochs-p
    (message "Dumping Movitz image...done. Bootblock ID: %d. Running qemu.."
	     (fi:eval-in-lisp "movitz::*bootblock-build*"))
;;     (call-process "/bin/sh" nil 0 nil "-c"
;; 		  (format "DISPLAY=\"%s\" cd ~/clnet/movitz && qemu -fda los0-image -boot a"
;; 			  display-shortcut))
    )
   (t (message "Dumping Movitz image...done. Bootblock ID: %d. Running bochs on \"%s\"..."
	       (fi:eval-in-lisp "movitz::*bootblock-build*")
	       display-shortcut)
      (call-process "/bin/sh" nil 0 nil "-c"
		    (format "DISPLAY=\"%s\" cd ~/clnet/movitz && ~/tmp/bochs-cvs/bochs -nocp > bochs-parameters"
			    display-shortcut)))))

(defun movitz-compile-file ()
  (interactive)
  (save-some-buffers)
  (message "Movitz compiling \"%s\"..." (buffer-file-name))
  (fi:eval-in-lisp "(movitz:movitz-compile-file \"%s\")" (buffer-file-name))
  (message "Movitz compiling \"%s\"...done."
	   (buffer-file-name)))

(defun movitz-eval-in-acl (string msg)
  (fi::note-background-request nil)
  (let ((compilep nil)
	(buffer (current-buffer)))
    (fi::make-request
     (lep::evaluation-request
      :transaction-directory fi:emacs-to-lisp-transaction-directory
      ;; The addition of the format wrapper in the next line works
      ;; around the incredible bogosity of fsf emacs 19.x that prints
      ;; strings with non-null fontification using vector syntax.
      ;; The format call reliably if inefficiently strips the font data.
      ;; bug3330 smh 22jun94
      :text (fi::defontify-string string)
      :echo fi:echo-evals-from-buffer-in-listener-p
      :partialp nil
      :pathname (buffer-file-name)
      :compilep nil
      :return-string (eq 'minibuffer (car fi:pop-up-temp-window-behavior)))
     ((buffer compilep msg) (results stuff)
      (save-excursion
	(set-buffer buffer)
	(cond
	 ((eq 'minibuffer (car fi:pop-up-temp-window-behavior))
	  (if (and (stringp stuff) (= 0 (length stuff)))
	      (fi::note-background-reply (list compilep))
	    (fi:show-some-text nil stuff)))
	 (t
	  (fi::note-background-reply (list compilep))))
	;; (fi::note-background-reply (list compilep))
	(when (and results (null fi:echo-evals-from-buffer-in-listener-p))
	  (fi:show-some-text nil results)))
      (when fi:pop-to-sublisp-buffer-after-lisp-eval ; bug2683
	(pop-to-buffer fi:common-lisp-buffer-name)
	(goto-char (point-max)))
      (message "%sdone." msg))
     ((buffer compilep) (error)
      (save-excursion
	(set-buffer buffer)
	(fi::note-background-reply (list compilep))
	(message "Error during %s: %s"
		 (if compilep "compile" "eval")
		 error)))
     nil)))

(defun movitz-compile-defun (&optional inverse-optimize-p)
  (interactive "P")
  (multiple-value-bind (defun-name defun-type)
      (movitz-defun-name-and-type)
    (when defun-name
      (let* ((end (save-excursion (end-of-defun) (point)))
	     (start (save-excursion
		      (fi:beginning-of-defun)
		      (point)))
	     (tmp-file (make-temp-name "/tmp/movitz-compile-defun-"))
	     (in-package (format "(in-package %s)\n" fi:package))
	     (msg (format "Movitz compiling %s %s..." defun-type defun-name)))
	(with-temp-file tmp-file
	  (insert in-package))
	(write-region start end tmp-file t)
	;; (fi:eval-in-lisp "(movitz:movitz-compile-file \"%s\")" tmp-file)
	(if (not inverse-optimize-p)
	    (movitz-eval-in-acl (format "(movitz:movitz-compile-file \"%s\" :delete-file-p t)" tmp-file) msg)
	  (movitz-eval-in-acl
	   (format "(cl:let ((movitz::*compiler-do-optimize* (cl:not movitz::*compiler-do-optimize*)))
                      (movitz:movitz-compile-file \"%s\" :delete-file-p t))" tmp-file) msg))))))
;;;	(with-current-buffer (get-buffer-create "*MOVITZ-eval*")
;;;	  (erase-buffer)
;;;	  (insert (format "(movitz:movitz-compile-file \"%s\")" tmp-file))
;;;	  (movitz-eval-region-internal (point-min) (point-max) nil))))))

(defun movitz-disassemble-defun (not-recursive-p)
  (interactive "P")
  (multiple-value-bind (defun-name defun-type lambda-list options)
      (movitz-defun-name-and-type)
    (cond
     ((string= "function" defun-type)
      (message "Movitz disassembling %s %s..." defun-type defun-name)
      (fi:eval-in-lisp
       "(cl:let ((defun-name (cl:let ((cl:*package* (cl:find-package :%s))) (cl:read-from-string \"%s\")))
               (cl:*print-base* 16))
         (movitz::movitz-disassemble defun-name :recursive %s))"
       fi:package defun-name (if not-recursive-p "cl:nil" "cl:t"))
      (switch-to-buffer "*common-lisp*")
      (message "Movitz disassembling %s %s...done." defun-type defun-name))
     ((string= "method" defun-type)
      (message "Movitz disassembling %s %s %s..." defun-type defun-name lambda-list)
      (fi:eval-in-lisp
       "(cl:let* ((gf-name (cl:let ((cl:*package* (cl:find-package :%s)))
                                  (cl:read-from-string \"%s\")))
                  (qualifiers (cl:read-from-string \"%s\"))
                  (lambda-list (cl:let ((cl:*package* (cl:find-package :%s)))
                                 (cl:read-from-string \"%s\")))
                  (cl:*print-base* 16))
         (movitz::movitz-disassemble-method gf-name lambda-list qualifiers))"
       fi:package defun-name options fi:package lambda-list)
      (switch-to-buffer "*common-lisp*")
      (message "Movitz disassembling %s %s...done." defun-type defun-name))
     ((string= "primitive-function" defun-type)
      (message "Movitz disassembling %s %s..." defun-type defun-name)
      (fi:eval-in-lisp
       "(cl:let ((defun-name (cl:let ((cl:*package* (cl:find-package :%s)))
                                (cl:read-from-string \"%s\")))
               (cl:*print-base* 16))
         (movitz::movitz-disassemble-primitive defun-name))"
       fi:package defun-name)
      (switch-to-buffer "*common-lisp*")
      (message "Movitz disassembling %s %s...done." defun-type defun-name))
     (t (message "Don't know how to Movitz disassemble %s %s." defun-type defun-name)))))

(defun movitz-macroexpand ()
  (interactive)
  (let* ((start (point))
	 (end (save-excursion (forward-sexp) (point)))
	 (tmp-file (make-temp-name "/tmp/movitz-macroexpand-"))
	 (expansion (unwind-protect
			(progn
			  (write-region start end tmp-file t)
			  (fi:eval-in-lisp "
  (cl:with-output-to-string (cl:*standard-output*)
   (cl:let ((cl:*print-pretty* t) (cl:*package* (cl:find-package :%s)))
    (cl:prin1
     (movitz::translate-program     
       (movitz::movitz-macroexpand-1
        (cl:let ((cl:*package* (cl:find-package :%s)))
         (cl:with-open-file (stream \"%s\" :direction :input)
          (cl:read stream))))
       :common-lisp :muerte.common-lisp))))"
					   fi:package
					   fi:package
					   tmp-file))
		      (delete-file tmp-file))))
    (if (and (not (find 10 expansion))
	     (< (length expansion) 80))
	(message "Movitz: \"%s\"" expansion)
      (let ((buffer (get-buffer-create "*Movitz Macroexpand*")))
	(with-current-buffer buffer
	  (delete-region 1 (point-max))
	  (common-lisp-mode)
	  (insert expansion)
	  (newline 2)
	  (pop-to-buffer buffer))))))


(add-hook 'fi:inferior-common-lisp-mode-hook
	  '(lambda ()
	    (define-key fi:inferior-common-lisp-mode-map "\C-c\C-d" 'movitz-dump-image)))

(add-hook 'fi:common-lisp-mode-hook
	  '(lambda ()
	    (when (in-movitz-package-p)
	      (message "Switching to Movitz keymap.")
	      (use-local-map (make-movitz-common-lisp-mode-map)))))

(defun movitz-mode ()
  "Switch on Movitz-mode."
  (interactive)
  (use-local-map (make-movitz-common-lisp-mode-map)))

(let ((tag 'fi:common-lisp-indent-hook))
  (put 'compiler-values tag '(like with-open-file))
  (put 'compiler-values-list tag '(like with-open-file))
  (put 'compiler-values-bind tag '(like multiple-value-bind))
  (put 'compiler-values-list-bind tag '(like multiple-value-bind))
  (put 'compiler-call tag '(like make-instance))
  (put 'compiler-values-setq tag '(like multiple-value-setq))
  (put 'named-integer-case tag '(like with-slots))
  (put 'with-ne2000-io tag '(like with-slots))
  (put 'vector-double-dispatch tag '(like case))
  (put 'sequence-dispatch tag '(like case))
  (put 'sequence-double-dispatch tag '(like case))
  (put 'number-double-dispatch tag '(like case))
  (put 'simple-stream-dispatch tag '(like case))
  (put 'with-inline-assembly tag '(like prog))
  (put 'with-inline-assembly-case tag '(like prog))
  (put 'do-case tag '(like prog))
  (put 'select tag '(like case))
  (put 'compiler-typecase tag '(like case)))


