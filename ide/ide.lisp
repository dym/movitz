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
  (:export #:compile-movitz-file
           #:compile-defun
           #:dump-image
           #:movitz-disassemble
           #:movitz-disassemble-primitive
           #:movitz-disassemble-method
           #:movitz-arglist
           #:movitz-macroexpand))

(in-package #:movitz.ide)

(defmacro with-image ((&optional (image-form 'movitz:*image*)) &body body)
  `(let ((movitz:*image* ,image-form))
     (check-type movitz:*image* movitz::movitz-image "a Movitz image")
     ,@body))

(defun compile-movitz-file (filename)
  "Compile FILENAME as Movitz source."
  (with-image ()
    (movitz:movitz-compile-file filename)))

(defun compile-defun (source package-printname)
  "Compile the string SOURCE as Movitz source."
  (with-image ()
    (with-input-from-string (stream source)
      (movitz:movitz-compile-stream stream :path "movitz-ide-toplevel"
                                           :package (get-package package-printname)))))

(defun dump-image (filename)
  "Dump the current image into FILENAME."
  (with-image ()
    (movitz:dump-image :path filename)))

;;; slime-friendly entry point.
(defun movitz-disassemble (printname package-printname)
  "Return the disassembly of SYMBOL-NAME's function as a string."
  (with-image ()
    (with-output-to-string (*standard-output*)
      (movitz:movitz-disassemble (get-sexpr printname
                                            (get-package package-printname))))))

(defun movitz-disassemble-primitive (printname package-printname)
  "Return the disassembly of SYMBOL-NAME's function as a string."
  (with-image ()
    (with-output-to-string (*standard-output*)
      (movitz::movitz-disassemble-primitive (get-sexpr printname
                                                       (get-package package-printname))))))

(defun movitz-disassemble-method (gf-name lambda-list qualifiers package-name)
  (with-image ()
    (let ((package (get-package package-name)))
      (with-output-to-string (*standard-output*)
        (movitz:movitz-disassemble-method (get-sexpr gf-name package)
                                          (get-sexpr lambda-list package)
                                          (mapcar #'read-from-string qualifiers))))))

(defun movitz-arglist (name package-name)
  (with-image ()
    (let* ((package (get-package package-name))
           (funobj (movitz::movitz-env-named-function (get-sexpr name package))))
      (if (not funobj)
          "not defined"
          (let ((*package* package))
            (princ-to-string (movitz::movitz-print (movitz::movitz-funobj-lambda-list funobj))))))))

(defun movitz-macroexpand (string package-name)
  (with-image ()
    (let* ((*package* (get-package package-name))
           (form (get-sexpr string *package*))
           (expansion (movitz::movitz-macroexpand-1 form)))
      (princ-to-string (movitz::movitz-print expansion)))))
    


;;;; Utilities.

(defvar scratch-package (make-package '#:movitz.ide.scratch)
  "Scratch package used internally for reading symbols into.")

(defun get-symbol (printname &optional (package *package*))
  "Return the symbol with PRINTNAME in PACKAGE.
Signal an error if there is no such symbol."
  (or (find-symbol (readname printname) package)
      (error "Can't find \"~A\" as a symbol in ~S" printname package)))

(defun get-sexpr (printname &optional (package *package*))
  (let ((*package* package))
    (read-from-string printname)))

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

