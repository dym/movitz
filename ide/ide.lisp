;;; ide.lisp -- backend functions for an interactive development environment
;;; Written in 2004 by  Luke Gorrie <luke@member.fsf.org>
;;;
;;; This program has been released into the public domain.
;;;
;;; We define a simple interface for manipulating a Movitz image
;;; within its host Lisp. The interface is intended for use by Emacs
;;; modes such as SLIME and (hopefully) ELI.

(defpackage #:movitz.ide
  (:use #:cl)
  (:export #:compile-movitz-file #:compile-defun #:dump-image
           #:disassemble-fdefinition #:movitz-disassemble))

(in-package #:movitz.ide)

(defconstant temp-source-file "/tmp/movitz-scratch.lisp"
  "Temporary file used to implement race conditions.")

(defun compile-movitz-file (filename)
  "Compile FILENAME as Movitz source."
  (movitz:movitz-compile-file filename))

(defun compile-defun (source)
  "Compile the string SOURCE as Movitz source."
  (with-open-file (s temp-source-file :direction :output :if-exists :overwrite)
    (princ source s))
  (compile-movitz-file temp-source-file))

(defun dump-image (filename)
  "Dump the current image into FILENAME."
  (movitz:dump-image :path filename))

;;; slime-friendly entry point.
(defun movitz-disassemble (symbol-printname package-printname)
  "Return the disassembly of SYMBOL-NAME's function as a string."
  (disassemble-fdefinition (get-symbol symbol-printname
                                       (get-package package-printname))))

(defun disassemble-fdefinition (symbol)
  "Return the disassembly SYMBOL's fdefinition as a string."
  (with-output-to-string (*standard-output*)
    (movitz::movitz-disassemble symbol)))


;;;; Utilities.

(defvar scratch-package (make-package '#:movitz.ide.scratch)
  "Scratch package used internally for reading symbols into.")

(defun get-symbol (printname &optional (package *package*))
  "Return the symbol with PRINTNAME in PACKAGE.
Signal an error if there is no such symbol."
  (or (find-symbol (readname printname) package)
      (error "Can't find \"~A\" as a symbol in ~S" printname package)))

(defun get-package (printname)
  "Return the package with PRINTNAME.
Signal an error if there is no such package."
  (or (find-package (readname printname))
      (error "Can't find package \"~A\"" printname)))

(defun readname (printname)
  "Read the string PRINTNAME into a symbol and return the symbol-name.
Trigger an error if PRINTNAME does not read as a symbol."
  (let ((*package* scratch-package))
    (let ((obj (read-from-string printname)))
      (if (symbolp obj)
          (symbol-name obj)
          (error "Not a symbol: ~S" obj)))))

