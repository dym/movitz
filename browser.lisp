;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001-2002, 2004, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      browser.lisp
;;;; Description:   A CLIM browser/inspector of Movitz images.
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Thu Jun 14 15:14:35 2001
;;;;                
;;;; $Id: browser.lisp,v 1.2 2004/01/19 11:23:41 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(eval-when (:compile-toplevel :load-toplevel)
  #+allegro (require :climxm))

(defpackage movitz-browser
  (:use clim clim-lisp movitz binary-types)
  (:export browse-file
	   browse-pid
	   browse-word
	   browser))

(in-package movitz-browser)

(define-command-table browser-file-commands
    :menu (("Print" :command print-graph)
	   ("Print preview" :command print-graph-preview)
	   ("" :divider :line)
	   ("Quit" :command quit)))

(define-command-table browser-tree-commands
    :menu (("Set NIL as root" :command (read-and-set-root nil))
	   ("Enter word" :command set-root-word)))

(define-command quit ()
  (frame-exit *application-frame*))

(define-command print-graph ()
  (multiple-value-call #'warn
    "print!: ~S :"
    (select-file *application-frame*)))

(define-command print-graph-preview ()
  (let ((temp-name (sys:make-temp-file-name "browser-graph-preview")))
    (with-open-file (temp-file temp-name :direction :output)
      (with-output-to-postscript-stream (ps-stream temp-file)
	(display-graph *application-frame* ps-stream)))
    (excl:run-shell-command (format nil "gv -resize ~S; rm ~S" temp-name temp-name) :wait nil)))

(define-application-frame browser ()
  ((root-tuple
    :initarg :root-tuple
    :accessor browser-root-tuple))
  (:menu-bar t)
  (:pointer-documentation t)
  (:command-table (browser
		   :menu (("File" :menu browser-file-commands)
			  ("Tree" :menu browser-tree-commands))
		   :inherit-from (browser-file-commands browser-tree-commands)))
  (:panes
   (graph
    :application
    ;; :label "Object Graph"
    ;; :scroll-bars nil
    :initial-cursor-visibility nil
    :display-function 'display-graph))
  (:layouts
   (default (horizontally ()
	      graph))))


(defstruct graph-tuple
  tree
  object
  parent
  slot-name)

(define-presentation-type graph-tuple () :inherit-from t)

(defun display-graph (browser *standard-output*)
  (format-graph-from-root (browser-root-tuple browser)
			  ;; printer
			  #'(lambda (tuple *standard-output*)
			      (with-output-as-presentation (t tuple 'graph-tuple)
				(with-slots (object slot-name) tuple
				  (formatting-table ()
				    (formatting-column ()
				      (when slot-name
					(formatting-cell (t :align-x :center)
					  (display-child-spec slot-name)))
				      (formatting-cell (t :align-x :center)
					(present object)))))))
			  ;; child-producer
			  #'(lambda (tuple)
			      (with-slots (tree object parent slot-name) tuple
				;; (warn "child-of: ~S" (type-of object))
				(mapcar #'(lambda (child-slot-name)
					    (make-graph-tuple
					     :tree tree
					     :object (browser-child object child-slot-name)
					     :parent object
					     :slot-name child-slot-name))
					(browser-open-slots tree object parent slot-name))))
			  :graph-type :digraph
			  :within-generation-separation 2
			  :maximize-generations nil
			  :generation-separation 60
			  :store-objects t
			  :center-nodes nil
			  :orientation :horizontal ;; :vertical
			  ;; :duplicate-key #'cdr
			  ;; :duplicate-test #'equalp
			  :merge-duplicates t
			  :cutoff-depth 50))


(defun display-child-spec (spec)
  (case (first spec)
    (slot-value
     (with-drawing-options (t :ink +green+ :size :small)
       (princ (string-downcase (format nil "~A" (second spec))))))
    (otherwise
     (princ spec))))

(defmethod movitz-object-browser-properties ((object t)) nil)

(defmethod browser-child ((object movitz-heap-object) child-spec)
  (ecase (car child-spec)
    (slot-value
     (slot-value object (second child-spec)))))

(defclass browser-array ()
  ((type
    :initarg :type
    :reader browser-array-type)
   (elements
    :initarg :elements
    :reader browser-array-elements)))

(define-presentation-type browser-array ())

(defmethod browser-child ((object movitz-vector) child-spec)
  (destructuring-bind (operator &rest operands)
      child-spec
    (case operator
      (aref
       (nth (first operands)
	    (movitz-vector-symbolic-data object)))
      (array
       (make-instance 'browser-array
	 :type (movitz-vector-element-type object)
	 :elements (movitz-vector-symbolic-data object)))
      (t (call-next-method object child-spec)))))

(defmethod browser-child ((object movitz-struct) child-spec)
  (destructuring-bind (operator &rest operands)
      child-spec
    (case operator
      (struct-ref
       (nth (first operands)
	    (movitz-struct-slot-values object)))
      (t (call-next-method)))))


(defun browser-slot-value (object slot-name)
  (case (binary-slot-type (type-of object) slot-name)
    (word (movitz-word (binary-slot-value object slot-name)))
    (t (if (slot-boundp object slot-name)
	   (slot-value object slot-name)
	 (make-symbol "[UNBOUND]")))))

(defun browser-all-slots (object)
  (mapcar #'(lambda (slot-name) (list 'slot-value slot-name))
	  (binary-record-slot-names (type-of object))))

(defmethod browser-default-open-slots ((object movitz-heap-object))
  (reverse (set-difference (browser-all-slots object)
			   '((slot-value movitz::type))
			   :key #'second)))

(defmethod browser-default-open-slots ((object movitz-vector))
  (assert (= (length (movitz-vector-symbolic-data object))
	     (movitz-vector-num-elements object)))
  (append (remove 'movitz::data (call-next-method object) :key #'second)
	  (case (movitz-vector-element-type object)
	    (:any-t
	     ;; merge EQ elements..
	     (loop for (value next-value) on (movitz-vector-symbolic-data object)
		 as i upfrom 0
		 with start-index = 0
		 unless (and next-value
			     (= (movitz-intern value)
				(movitz-intern next-value)))
		 collect `(aref ,start-index ,@(unless (= i start-index) (list i)))
		 and do (setf start-index (1+ i))))
	    (t (list `(array ,(movitz-vector-num-elements object)))))))

(defmethod browser-default-open-slots ((object movitz-struct))
  (append (remove 'movitz::slot0 (call-next-method object) :key #'second)
	  (loop for x from 0 below (movitz-struct-length object)
	      collect `(struct-ref ,x))))

(defun browse-image (*image* &key (root (make-graph-tuple
					 :object (movitz-word (movitz-read-and-intern nil 'word))
					 :tree (gensym))))
  (let ((*endian* :little-endian)
	(*print-radix* t)
	(*print-base* 16))
    (run-frame-top-level
     (make-application-frame 'browser
			     :width 700
			     :height 700
			     :root-tuple root))))

(defun browse-word (word)
  (browse-image movitz::*image*
		:root (make-graph-tuple :object (movitz-word word)
					:tree (gensym))))
    
(defun browser ()
  (multiprocessing:process-run-function "browser" #'browse-image *i*))

(defun browse-pid (pid)
  (flet ((do-browse-pid (pid)
	   (with-procfs-image (pid)
	     (browse-image *image*))))
    (multiprocessing:process-run-function
     `(:name "browser")
     #'do-browse-pid
     pid)))

(defun browse-file (&key (threadp t) (path *default-image-file*)
			 (offset (- 512 #x100000)) (direction :input))
  (flet ((do-browse-path (path offset direction)
	   (with-binary-file (stream path :direction direction)
	     (browse-image (make-instance 'stream-image
			     :stream stream
			     :offset offset)))))
    (if threadp
	(multiprocessing:process-run-function "browser" #'do-browse-path
					      path offset direction)
      (do-browse-path path offset direction))))


(define-presentation-type movitz-object ())

(define-presentation-method present (object (type movitz-object)
					    *standard-output*
					    (view textual-view) &key)
  (formatting-table ()
    (formatting-column ()
      (formatting-cell (t :align-x :center)
	(with-drawing-options (t :size :small)
	  (browser-print-safely object)))
      (formatting-cell (t :align-x :center)
	(format t "#x~8,'0X" (movitz-intern object))))))

(define-presentation-method present
    (object (type movitz-object) *standard-output* (view textual-menu-view) &key)
  (format t "#x~8,'0X" (movitz-intern object)))

(define-presentation-method present
    (object (type graph-tuple) *standard-output* (view textual-menu-view) &key)
  (format t "#x~8,'0X" (movitz-intern (graph-tuple-object object))))

(define-presentation-method present (object (type movitz-character)
					    *standard-output*
					    (view textual-view) &key)
  (write (movitz-char object)))

(define-presentation-method present
    (object (type movitz-symbol) *standard-output* (view textual-view) &key)
  (format t "#x~8,'0X: |~A|" (movitz-intern object) (browser-print-safely object)))

(define-presentation-method present
    (object (type movitz-vector) *standard-output* (view textual-view) &key)
  (if (not (eq :character (movitz-vector-element-type object)))
      (call-next-method)
    (format t "#x~8,'0X: \"~A\"" (movitz-intern object) (browser-print-safely object))))

(defun browser-print-safely (object)
  (handler-case
      (movitz::movitz-print object)
    (error ()
      (write-string (string-downcase (symbol-name (type-of object)))))))

(define-presentation-method present (object (type browser-array)
					    *standard-output*
					    (view textual-view) &key)
  (let ((rows-per-col (typecase (length (browser-array-elements object))
			((integer 0 15) 1)
			((integer 16 47) 2)
			((integer 48 127) 4)
			(t 8))))
    (formatting-table ()
      (loop for row on (browser-array-elements object) by #'(lambda (x) (nthcdr rows-per-col x))
	  as i upfrom 0 by rows-per-col
	  do (formatting-row ()
	       (formatting-cell (t :align-x :right)
		 (format t "~D:" i))
	       (loop for r from 1 to rows-per-col
		   as element in row
		   do (formatting-cell ()
			(case (browser-array-type object)
			  (:u32 (format t "#x~8,'0X" element))
			  ((:u8 :code)  (format t "#x~2,'0X" element))
			  (t #+ignore(warn "unk: ~S" (browser-array-type object))
			     (write element))))))))))

(define-browser-command read-and-set-root ((object 't))
  (set-root (movitz-word (movitz-read-and-intern object 'word))))

(define-browser-command toggle ((tuple 'graph-tuple))
  (with-slots (tree object parent slot-name) tuple
    (cond
     ((null (browser-open-slots tree object parent slot-name))
      (setf (browser-open-slots tree object parent slot-name)
	(browser-default-open-slots object)))
      ;; (warn "now open: ~S" (browser-open-slots tree object parent slot-name)))
     (t
      (setf (browser-open-slots tree object parent slot-name)
	nil)))))

(define-presentation-to-command-translator toggle
    (graph-tuple
     toggle
     browser
     :gesture :select
     :tester ((object)
	      (typep (graph-tuple-object object) 'movitz-heap-object)))
  (object)
  (list object))

(define-browser-command set-root ((object 'movitz-object))
  (setf (browser-root-tuple *application-frame*)
    (make-graph-tuple :tree (gensym) :object object)))

(define-presentation-to-command-translator set-root-tuple
    (graph-tuple set-root browser)
  (object)
  (list (graph-tuple-object object)))

(define-browser-command new-browser ((object 'movitz-object))
  (browse-image *image* :root (make-graph-tuple :tree (gensym)
						:object object)))

(define-presentation-to-command-translator new-browser-tuple
    (graph-tuple new-browser browser)
  (object)
  (list (graph-tuple-object object)))

(defun (setf browser-open-slots) (value tree object parent slot-name)
  (let ((old-slot (assoc-if #'(lambda (x) (and (eq (car x) parent) (eq (cdr x) slot-name)))
			    (getf (movitz-object-browser-properties object) tree))))
    (if old-slot
	(setf (cdr old-slot) value)
      (setf (getf (movitz-object-browser-properties object) tree)
	(acons (cons parent slot-name)
	       value
	       (getf (movitz-object-browser-properties object) tree)))))
  value)

(defun browser-open-slots (tree object parent slot-name)
  (cdr (assoc-if #'(lambda (x) (and (eq (car x) parent) (eq (cdr x) slot-name)))
		 (getf (movitz-object-browser-properties object) tree))))


(define-browser-command set-root-word ()
  (let ((word (accepting-values (t :own-window t)
		(accept '((integer 0 #xffffffff) :base 16)))))
    (when word
      (set-root (movitz-word word)))))
