;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;    Copyright (C) 2006, 
;;    Department of Computer Science, University of Tromso, Norway.
;; 
;;    For distribution policy, see the accompanying file COPYING.
;; 
;; Filename:      subtypep.lisp
;; Description:   
;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;; Created at:    Sun Apr  2 20:47:11 2006
;;                
;; $Id: subtypep.lisp,v 1.1 2006/04/07 21:48:43 ffjeld Exp $
;;                
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require :muerte/basic-macros)
(provide :muerte/subtypep)
  
(in-package muerte)

(defun subtypep (type-1 type-2 &optional environment)
  "Is type-1 a subtype of type-2? => subtype-p, valid-p"
  (let ((class-1 (find-class type-1 nil environment))
	(class-2 (find-class type-2 nil environment)))
    (cond
     ((and class-1 class-2)
      (values (subclassp class-1 class-2) t))
     (class-2
      (dolist (c (class-precedence-list class-2) (values nil nil))
	(when (member type-1 (getf (class-plist c) :subtypes))
	  (return (values t t)))))
     (t (values nil nil)))))
      
    
  
  