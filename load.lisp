
(in-package :user)

;; (load "../binary-types/binary-types")

(compile-file #p"../binary-types/binary-types" :load-after-compile t)

(let ((*default-pathname-defaults* #+mswindows #p"c:\\src\\read-elf32\\"
				   #+unix #p"~/src/ia-x86/"))
  (load "system.lisp")
  (compile-system :ia-x86)
  (load-system :ia-x86)
  (load-system :ia-x86-instr :interpreted t))

(ia-x86:init-instruction-tables)

(let ((*default-pathname-defaults* #+mswindows #p"c:\\src\\read-elf32\\"
				   #+unix #p"~/src/read-elf32/"))
  (load "Defsystem-allegro.lisp")
  (load-system :elf32))

(compile-file #p"../infunix/procfs" :load-after-compile t)

(load "packages.lisp")
(load "movitz.lisp")
(compile-system :movitz)
(load-system :movitz)

#+allegro
(progn
  (setf excl:*tenured-bytes-limit* #x2000000)
  (setf (system::gsgc-parameter :generation-spread) 12)
  (sys:resize-areas :new (* 16 1024 1024)))