;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2008, Frode V. Fjeld
;;;; 
;;;; Description:   Pathnames
;;;; Author:        Frode Vatvedt Fjeld
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: pathnames.lisp,v 1.2 2008-04-21 19:42:06 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)

(in-package muerte)

(provide :muerte/pathnames)

(defclass pathname ()
  ((name)))

(defclass logical-pathname (pathname)
  ())
