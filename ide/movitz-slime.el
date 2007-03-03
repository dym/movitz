;;; movitz-slime.el -- slime frontend for movitz
;;; Copyright 2004   Luke Gorrie <luke@member.fsf.org>
;;;
;;; This is Free Software licensed under the terms of the GNU GPL.
;;;
;;; This is a small SLIME-based mode for Movitz development. We define
;;; a few commands for manipulating the Movitz image within a host
;;; Lisp. The mode is not comprehensive: it is used as an add-on to
;;; slime-mode, and all slime commands still manipulate the host Lisp.
;;;
;;; You can enable this mode in a file with "-*- movitz-mode: t -*-"
;;; on the first line, and use a trick such as
;;; `movitz-auto-mode-setup' (below) to automatically enable it on the
;;; core Movitz sources.

(require 'slime)
(require 'cl)

;;;; Minor-mode

;; You should set this to something more convenient, e.g. "\C-cm"
(defvar movitz-command-prefix "\C-c\C-v"
  "The initial key prefixf or movitz commands.")

(define-minor-mode movitz-mode
  "\\{movitz-mode-map}"
  nil
  " Movitz"
  ;; Bogus keymap to have movitz-mode-map initialized. We'll fill in
  ;; the real bindings manually.
  `((,movitz-command-prefix . undefined)))

(defvar movitz-mode-commands-map nil
  "Keymap for movitz-mode commands.
This map is bound to a prefix sequence in `movitz-mode-map'.")

(defconst movitz-command-keys '(("k" movitz-compile-file)
                                ("c" movitz-compile-defun)
                                ("d" movitz-disassemble-fdefinition)
                                ("D" movitz-dump-image))
  "Keys to bind in `movitz-mode-commands-map'.")

(defun movitz-init-command-keymap ()
  "Bind the movitz-mode keys.
This command can be called interactively to redefine the keys."
  (interactive)
  (setq movitz-mode-commands-map (make-sparse-keymap))
  (dolist (spec movitz-command-keys)
    (define-key movitz-mode-commands-map (car spec) (cadr spec)))
  (define-key movitz-mode-map movitz-command-prefix movitz-mode-commands-map)

  (define-key movitz-mode-map "\C-cd" 'movitz-dump-image)
  (define-key movitz-mode-map "\C-c\C-v" 'movitz-disassemble-defun)
  (define-key movitz-mode-map "\C-c\C-b" 'movitz-compile-file)
  (define-key movitz-mode-map "\C-\M-x" 'movitz-compile-defun)
  (define-key movitz-mode-map "\C-cm" 'movitz-macroexpand)
  (define-key movitz-mode-map "\C-ca" 'movitz-arglist)
  (define-key movitz-mode-map "\C-cd" 'movitz-dump-image-and-qemu)
  (define-key movitz-mode-map "\M-." 'find-tag)
  (define-key movitz-mode-map "\M-," 'tags-loop-continue)
  (define-key movitz-mode-map "\r" 'newline-and-indent)
  (define-key movitz-mode-map " " 'self-insert-command))

(movitz-init-command-keymap)

(defun movitz-auto-mode-setup ()
  "Do some horrible things with regexps to auto-enable movitz-mode.
You can call this function from your init file, but first read what it
does."
  (add-hook 'find-file-hooks
            (defun movitz-auto-enable ()
              (when (string-match ".*/movitz/losp/.*\\.lisp$" (buffer-file-name))
                (movitz-mode 1)))))


;;;; Commands

(defun movitz-compile-file (filename)
  "Compile the current buffer's file as Movitz source.
If the current buffer has no file or a prefix argument is in effect
then prompt for the file to compile."
  (interactive (list (or (and (null current-prefix-arg) (buffer-file-name))
                         (read-file-name "File: "))))
  (let ((buffer (get-file-buffer filename)))
    (when (and buffer (buffer-modified-p buffer))
      (when (y-or-n-p (format "Save file %s? " filename))
        (with-current-buffer buffer (save-buffer)))))
  (message "Compiling..")
  (slime-eval-async `(movitz.ide:compile-movitz-file ,filename)
                    (lambda (_) (message "Compilation finished."))))

(defun movitz-compile-defun ()
  "Compile the defun at point as Movitz code."
  (interactive)
  (multiple-value-bind (defun-name defun-type)
      (movitz-defun-name-and-type)
    (lexical-let ((defun-name defun-name)
                  (defun-type defun-type)
                  (package-name (slime-current-package)))
      (message "Compiling %s '%s'.." defun-type defun-name)
      (slime-eval-async `(movitz.ide:compile-defun ,(slime-defun-at-point) ,package-name)
                        (lambda (_) (message "Movitz compilation of %s '%s' finished." defun-type defun-name))))))

(defun movitz-macroexpand ()
  "Macroexpand the form at point."
  (interactive)
  (lexical-let ((form (slime-sexp-at-point-or-error))
                (package-name (slime-current-package)))
    (slime-eval-async `(movitz.ide:movitz-macroexpand ,form ,package-name)
                      (lambda (expansion)
                        (if (and (not (find 10 expansion))
                                 (< (length expansion) 80))
                            (message "Movitz: \"%s\"" expansion)
                          (let ((buffer (get-buffer-create "*Movitz Macroexpand*")))
                            (with-current-buffer buffer
                              (delete-region 1 (point-max))
                              (common-lisp-mode)
                              (insert expansion)
                              (newline 2)
                              (pop-to-buffer buffer))))))))


(defun movitz-disassemble-fdefinition (symbol-name package-name)
  "Show disassembly of the (non-generic) function at point."
  (interactive (list (slime-read-symbol-name "Symbol: ")
                     (slime-current-package)))
  (slime-eval-async `(movitz.ide:movitz-disassemble ,symbol-name ,package-name)
                    (lexical-let ((package package-name))
                      (lambda (result)
                        (slime-show-description result package)))))

(defun movitz-disassemble-defun (not-recursive-p)
  (interactive "P")
  (multiple-value-bind (defun-name defun-type lambda-list options)
      (movitz-defun-name-and-type)
    (lexical-let ((defun-name defun-name)
                  (defun-type defun-type)
                  (package-name (slime-current-package))
                  (lambda-list lambda-list)
                  (options options))
      (cond
       ((string= "function" defun-type)
        (message "Movitz disassembling %s %s..." defun-type defun-name)
        (slime-eval-async `(movitz.ide:movitz-disassemble ,defun-name ,package-name)
                          (lambda (result)
                            (slime-show-description result package-name)
                            (message "Movitz disassembling %s %s...done." defun-type defun-name))))
       ((string= "method" defun-type)
        (message "Movitz disassembling %s '%s %s'..." defun-type defun-name lambda-list)
        (slime-eval-async `(movitz.ide:movitz-disassemble-method ,defun-name ,lambda-list ',options ,package-name)
                          (lambda (result)
                            (slime-show-description result package-name)
                            (message "Movitz disassembling %s '%s %s'...done." defun-type defun-name lambda-list))))
       ;; ((string= "primitive-function" defun-type)
       ;;       (message "Movitz disassembling %s %s..." defun-type defun-name)
       ;;       (fi:eval-in-lisp
       ;;        "(cl:let ((defun-name (cl:let ((cl:*package* (cl:find-package :%s)))
       ;;                                 (cl:read-from-string \"%s\")))
       ;;                (cl:*print-base* 16))
       ;;          (movitz::movitz-disassemble-primitive defun-name))"
       ;;        fi:package defun-name)
       ;;       (switch-to-buffer "*common-lisp*")
       ;;       (message "Movitz disassembling %s %s...done." defun-type defun-name))
       (t (message "Don't know how to Movitz disassemble %s '%s'." defun-type defun-name))))))

(defun movitz-arglist (string)
  (interactive (list (slime-read-symbol-name "Movitz arglist of: ")))
  (when (and string (plusp (length string)))
    (lexical-let ((string string))
      (slime-eval-async `(movitz.ide:movitz-arglist ,string ,(slime-current-package))
                        (lambda (result)
                          (message "Movitz args for %s: %s." string result))))))


(defvar movitz-default-image-file nil
  "The default filename to dump images to.
This is set by `movitz-dump-image' and can also be preinitialized in
your init file.")

(defun movitz-dump-image (filename)
  "Dump the current image to FILENAME."
  (interactive (list (if (and (null current-prefix-arg)
                              movitz-default-image-file)
                         movitz-default-image-file
                       (let ((filename (read-file-name "Image file: ")))
                         (setq movitz-default-image-file filename)
                         filename))))
  (message "Dumping..")
  (slime-eval-async `(movitz.ide:dump-image ,filename)
                    (lambda (_) (message "Finished."))))


(defun movitz-dump-image-and-qemu (filename)
  "Dump the current image to FILENAME."
  (interactive (list (if (and (null current-prefix-arg)
                              movitz-default-image-file)
                         movitz-default-image-file
                       (let ((filename (read-file-name "Image file: ")))
                         (setq movitz-default-image-file filename)
                         filename))))
  (lexical-let ((filename filename))
    (message "Dumping '%s'.." filename)
    (slime-eval-async `(movitz.ide:dump-image ,filename)
                      (lambda (_)
                        (message "Dumping '%s'..done, starting quemu." filename)
                        (call-process "c:/progra~1/qemu/qemu"
                                      nil 0 nil
                                      "-L" "c:/progra~1/qemu"
                                      "-fda" filename
                                      "-boot" "a")))))



(defun movitz-defun-name-and-type ()
  (interactive)
  (save-excursion
    (let ((definition-type
	    (let ((x (buffer-substring-no-properties (progn (beginning-of-defun)
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

;;; Indentation of Movit syntax

(let ((l '((with-inline-assembly . tagbody))))
  (dolist (el l)
    (put (car el) 'common-lisp-indent-function
         (if (symbolp (cdr el))
             (get (cdr el) 'common-lisp-indent-function)
           (car (cdr el))))))