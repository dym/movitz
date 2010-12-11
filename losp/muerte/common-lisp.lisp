;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 20012000, 2002-2005,
;;;;    Department of Computer Science, University of Tromso, Norway
;;;; 
;;;; Filename:      common-lisp.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Wed Nov  8 18:41:43 2000
;;;; Distribution:  See the accompanying file COPYING.
;;;;                
;;;; $Id: common-lisp.lisp,v 1.18 2008-03-20 22:21:00 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/defmacro-bootstrap)
(require :muerte/basic-macros)
(require :muerte/setf)
(require :muerte/more-macros)
(require :muerte/arithmetic-macros)

(require :muerte/defmacro-runtime)
(include :muerte/basic-macros)
(include :muerte/more-macros)
(include :muerte/arithmetic-macros)

(require :muerte/memref)
(require :muerte/integers)
(require :muerte/basic-functions)
(require :muerte/variables)
(require :muerte/primitive-functions)
(require :muerte/equalp)
(require :muerte/typep)
(require :muerte/functions)
(require :muerte/lists)
(require :muerte/symbols)
(require :muerte/characters)
(require :muerte/arrays)
(require :muerte/sequences)
(require :muerte/inspect)
(require :muerte/strings)
(require :muerte/print)
(require :muerte/los-closette)
(require :muerte/run-time-context)
(require :muerte/defstruct)
(require :muerte/hash-tables)
(require :muerte/pathnames)
(require :muerte/complexes)
(require :muerte/ratios)
(require :muerte/packages)
(require :muerte/format)
(require :muerte/error)
(require :muerte/loop)
(require :muerte/environment)
(require :muerte/eval)
(require :muerte/streams)
(require :muerte/restarts)
(require :muerte/conditions)
(require :muerte/bignums)
(require :muerte/read)
(require :muerte/interrupt)
(require :muerte/scavenge)
(require :muerte/simple-streams)
(require :muerte/subtypep)

(require :muerte/io-port)
(require :muerte/cpu-id)
(require :muerte/segments)

(provide :muerte/common-lisp)


    
