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
  (define-key movitz-mode-map movitz-command-prefix movitz-mode-commands-map))

(movitz-init-command-keymap)

(defun movitz-auto-mode-setup ()
  "Do some horrible things with regexps to auto-enable movitz-mode.
You can call this function from your init file, but first read what it
does."
  (add-hook 'find-file-hooks
            (defun movitz-auto-enable ()
              (when (string-match "/movitz/losp/.*\\.lisp$" (buffer-file-name))
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
  (message "Compiling..")
  (slime-eval-async `(movitz.ide:compile-defun ,(slime-defun-at-point))
                    (lambda (_) (message "Compilation finished."))))

(defun movitz-disassemble-fdefinition (symbol-name package-name)
  "Show disassembly of the (non-generic) function at point."
  (interactive (list (slime-read-symbol-name "Symbol: ")
                     (slime-current-package)))
  (slime-eval-async `(movitz.ide:movitz-disassemble ,symbol-name ,package-name)
                    (lexical-let ((package package-name))
                      (lambda (result)
                        (slime-show-description result package)))))

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

