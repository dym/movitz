;;; movitz-slime.el -- slime frontend for movitz

;; 2004, Written by Luke Gorrie <luke@member.fsf.org> and placed in
;;       the public domain.

;;; Commentary:
;;
;; This is a small SLIME-based mode for Movitz development. We define
;; a few commands for manipulating the Movitz image within a host
;; Lisp. The mode is not comprehensive: it is used as an add-on to
;; slime-mode, and all slime commands still manipulate the host Lisp.
;;
;; You can enable this mode in a file with "-*- movitz-mode: t -*-"
;; on the first line, and use a trick such as
;; `movitz-auto-mode-setup' (below) to automatically enable it on the
;; core Movitz sources.

;;; Installing:
;;
;; Load this mode by adding the location of this file to your
;; load-path and invoking (require 'movitz-slime).
;;
;; If you use QEMU under GNU/Linux, you should probably also set the
;; following to some same value, for example:
;; 
;; (setq movitz-mode-qemu-binary-path "/usr/bin/qemu")
;; (setq movitz-mode-qemu-directory "/usr/share/qemu/")

(require 'slime)
(require 'cl)

(defgroup movitz-mode nil
  "*Movitz mode."
  :prefix "movitz-mode-"
  :group 'movitz)

(eval-and-compile 
  (defvar movitz-mode-slime-path
    (let ((path (or (locate-library "movitz-slime") load-file-name)))
      (when path
        (file-name-directory path)))
    "Directory containing movitz sources.
This is used to load the supporting Common Lisp library, ide.lisp.
The default value is automatically computed from the location of the
Emacs Lisp package."))

(defcustom movitz-mode-command-prefix "\C-c\C-v"
  "*The initial key prefix or movitz-slime-mode commands."
  :type 'string
  :group 'movitz)

(defcustom movitz-mode-qemu-binary-path "c:/progra~1/qemu/qemu"
  "*Location of the QEMU binary."
  :type 'string
  :group 'movitz)

(defcustom movitz-mode-qemu-directory "c:/progra~1/qemu/qemu"
  "*Location for the QEMU -L option."
  :type 'string
  :group 'movitz)

(defcustom movitz-mode-image-file nil
  "*Movitz image file.
This is set by `movitz-dump' and can also be preinitialized in
your init file."
  :type 'string
  :group 'movitz)

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
  (lexical-let ((filename filename))
    (message "Movitz compiling '%s'.." filename)
    (slime-eval-async `(movitz.ide:compile-movitz-file ,filename)
                      (lambda (_)
                        (message "Movitz compiling '%s'..done." filename)))))

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
        (message "Movitz disassembling %s '%s'..." defun-type defun-name)
        (slime-eval-async `(movitz.ide:movitz-disassemble ,defun-name ,package-name)
                          (lambda (result)
                            (slime-show-description result package-name)
                            (message "Movitz disassembling %s '%s'...done." defun-type defun-name))))
       ((string= "method" defun-type)
        (message "Movitz disassembling %s '%s %s'..." defun-type defun-name lambda-list)
        (slime-eval-async `(movitz.ide:movitz-disassemble-method ,defun-name ,lambda-list ',options ,package-name)
                          (lambda (result)
                            (slime-show-description result package-name)
                            (message "Movitz disassembling %s '%s %s'...done." defun-type defun-name lambda-list))))
       ((string= "primitive-function" defun-type)
        (message "Movitz disassembling %s '%s'..." defun-type defun-name)
        (slime-eval-async `(movitz.ide:movitz-disassemble-primitive ,defun-name ,package-name)
                          (lambda (result)
                            (slime-show-description result package-name)
                            (message "Movitz disassembling %s '%s'...done." defun-type defun-name))))
       (t (message "Don't know how to Movitz disassemble %s '%s'." defun-type defun-name))))))

(defun movitz-arglist (string)
  (interactive (list (slime-read-symbol-name "Movitz arglist of: ")))
  (when (and string (plusp (length string)))
    (lexical-let ((string string))
      (slime-eval-async `(movitz.ide:movitz-arglist ,string ,(slime-current-package))
                        (lambda (result)
                          (message "Movitz args for %s: %s." string result))))))

(defun movitz-dump (&optional run-emulator)
  "Dump the current image to a file.
If RUN-EMULATOR is non-nil, call an emulator on the resulting file."
  (when (not movitz-mode-image-file)
    (setq movitz-mode-image-file (expand-file-name (read-file-name "Image file: "))))
  (message "Dumping '%s'.." movitz-mode-image-file)
  (slime-eval-async `(movitz.ide:dump-image ,(file-name-nondirectory movitz-mode-image-file))
		    (if run-emulator
			;; choose emulator here, currently only qemu
			(lambda (_)
			  (message "Dumping '%s'..done, starting qemu" movitz-mode-image-file)
			  (call-process movitz-mode-qemu-binary-path
					nil 0 nil
					"-s"
					"-L" movitz-mode-qemu-directory
					"-fda" movitz-mode-image-file
					"-boot" "a"))	
		      (lambda (_) (message "Dumping '%s'..done" movitz-mode-image-file)))))

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

(movitz-auto-mode-setup)

(defconst movitz-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map text-mode-map)
    (define-key map (kbd "C-c d") '(lambda () (interactive) (movitz-dump)))
    (define-key map (kbd "C-c C-d") '(lambda () (interactive) (movitz-dump t)))
    (define-key map (kbd "C-c C-v") 'movitz-disassemble-defun)
    (define-key map (kbd "C-c m") 'movitz-macroexpand)
    (define-key map (kbd "C-c a") 'movitz-arglist)
    (define-key map (kbd "C-c k") 'movitz-compile-file)
    (define-key map (kbd "C-c c") 'movitz-compile-defun)
    map
    )
  "Keymap for `movitz-mode'.")

(define-minor-mode movitz-mode
  "\\{movitz-mode-map}
Interface Movitz via SLIME."
  :init-value nil
  :lighter " Movitz"
  (cond
   ((not movitz-mode))
   ((not (slime-connected-p))
    (message "Movitz-mode: SLIME is not connected."))
   ((slime-eval '(cl:and (cl:find-package :movitz.ide) t)))
   ((not (slime-eval '(cl:and (cl:find-package :movitz) t)))
    (message "Movitz-mode: The Movitz package is not loaded."))
   (t (slime-eval
       `(cl:progn (cl:load (cl:compile-file ,(concat movitz-mode-slime-path "ide.lisp")))
		  nil)))))

(provide 'movitz-slime)

;;; movitz-slime.el ends here.
