;;;;------------------------------------------------------------------
;;;; 
;;;;    Copyright (C) 2001, 2003-2005, 
;;;;    Department of Computer Science, University of Tromso, Norway.
;;;; 
;;;;    For distribution policy, see the accompanying file COPYING.
;;;; 
;;;; Filename:      simple-streams.lisp
;;;; Description:   
;;;; Author:        Frode Vatvedt Fjeld <frodef@acm.org>
;;;; Created at:    Fri Aug 29 13:39:43 2003
;;;;                
;;;; $Id: simple-streams.lisp,v 1.9 2008-03-15 20:58:20 ffjeld Exp $
;;;;                
;;;;------------------------------------------------------------------

(require :muerte/basic-macros)
(require :muerte/los-closette)
(provide :muerte/simple-streams)

(in-package muerte)

(defvar *default-external-format* :ascii)


(defconstant +flag-bits+ '(:simple	; instance is valid
			   :input :output ; direction
			   :dual :string ; type of stream
			   :eof		; latched EOF
			   :dirty	; output buffer needs write
			   :interactive)) ; interactive stream


(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun %flags (flags)
    (loop for flag in flags
	  as pos = (position flag +flag-bits+)
	when (eq flag :gray) do
	  (error "Gray streams not supported.")
	if pos
	  sum (ash 1 pos) into bits
	else
	  collect flag into unused
      finally (when unused
		(warn "Invalid stream instance flag~P: ~{~S~^, ~}"
		      (length unused) unused))
	      (return bits))))

(defmacro simple-stream-dispatch (stream single-clause dual-clause string-clause)
  (assert (eq 'single-channel-simple-stream (car single-clause)))
  (assert (eq 'dual-channel-simple-stream (car dual-clause)))
  (assert (eq 'string-simple-stream (car string-clause)))
  (let ((s (gensym "stream-")))
    `(let ((,s ,stream))
       (with-stream-class (simple-stream ,s)
	 (let ((%flags (sm %flags ,s)))
	   (cond ((zerop (logand %flags ,(%flags '(:string :dual))))
		  ,@(cdr single-clause))
		 ((zerop (logand %flags ,(%flags '(:string))))
		  ,@(cdr dual-clause))
		 (t ,@(cdr string-clause))))))))

(defmacro/cross-compilation with-stream-class ((class-name &optional stream) &body body)
  (if stream
      (let ((stream-var (gensym "stream-"))
	    (slots-var (gensym "stream-slots-")))
	`(let* ((,stream-var ,stream)
		(,slots-var (std-instance-slots ,stream-var)))
	   (declare (type ,class-name ,stream-var)
		    (type simple-vector ,slots-var)
		    (ignorable ,slots-var))
	   (macrolet ((sm (slot-name stream)
			(declare (ignore stream))
			`(slot-value ,',stream-var ',slot-name)
			#+ignore `(svref%unsafe ,',slots-var
						,(slot-location ,(movitz-find-class class-name)
								slot-name)))
		      (add-stream-instance-flags (stream &rest flags)
			(declare (ignore stream))
			`(setf (sm %flags ,',stream-var)
			   (logior (sm %flags ,',stream-var)
				   ,(%flags flags))))
		      (remove-stream-instance-flags (stream &rest flags)
			(declare (ignore stream))
			`(setf (sm %flags ,',stream-var)
			   (logandc2 (sm %flags ,',stream-var)
				     ,(%flags flags))))
		      (any-stream-instance-flags (stream &rest flags)
			(declare (ignore stream))
			`(not (zerop (logand (sm %flags ,',stream-var)
					     ,(%flags flags))))))
	     ,@body)))
    `(macrolet ((sm (slot-name stream)
		  `(svref%unsafe (std-instance-slots stream)
				 ,(slot-location ,(movitz-find-class class-name)
						 slot-name))))
       ,@body)))

(defmacro sm (slot-name stream)
  "Access the named slot in Stream."
  ;; (warn "Using ~S macro outside ~S." 'sm 'with-stream-class)
  `(slot-value ,stream ',slot-name))

(defmacro funcall-stm-handler (slot-name stream &rest args)
  "Call the strategy function named by Slot-Name on Stream."
  (let ((s (gensym)))
    `(let ((,s ,stream))
       (funcall (sm ,slot-name ,s) ,s ,@args))))

(defmacro funcall-stm-handler-2 (slot-name arg1 stream &rest args)
  "Call the strategy function named by Slot-Name on Stream."
  (let ((s (gensym)))
    `(let ((,s ,stream))
       (funcall (sm ,slot-name ,s) ,arg1 ,s ,@args))))

(defmacro add-stream-instance-flags (stream &rest flags)
  "Set the given Flags in Stream."
  (let ((s (gensym "STREAM")))
    `(let ((,s ,stream))
       (with-stream-class (simple-stream ,s)
	 (add-stream-instance-flags ,s ,@flags)))))

(defmacro remove-stream-instance-flags (stream &rest flags)
  "Clear the given Flags in Stream."
  (let ((s (gensym "STREAM")))
    `(let ((,s ,stream))
       (with-stream-class (simple-stream ,s)
	 (remove-stream-instance-flags ,s ,@flags)))))

(defmacro any-stream-instance-flags (stream &rest flags)
  "Determine whether any one of the Flags is set in Stream."
  (let ((s (gensym "STREAM")))
    `(let ((,s ,stream))
       (with-stream-class (simple-stream ,s)
	 (any-stream-instance-flags ,s ,@flags)))))


(defun ill-in-any (stream &rest ignore)
  (declare (ignore ignore))
  (error 'simple-type-error
         :datum stream
         :expected-type '(satisfies input-stream-p)
         :format-control "~S is not an input stream."
         :format-arguments (list stream)))

(defun ill-out-any (stream &rest ignore)
  (declare (ignore ignore))
  (error 'simple-type-error
         :datum stream
         :expected-type '(satisfies output-stream-p)
         :format-control "~S is not an output stream."
         :format-arguments (list stream)))

(defclass simple-stream (stream)
  ((%flags
    :initform 0
    :type fixnum)
   (plist
    :initform nil
    :type list
    :accessor stream-plist)

   (j-listen
    :initform 'ill-in-any 
    :type j-listen-fn)
   (j-read-char 
    :initform 'ill-in-any 
    :type j-read-char-fn)
   (j-read-chars 
    :initform 'ill-in-any 
    :type j-read-chars-fn)
   (j-unread-char 
    :initform 'ill-in-any 
    :type j-unread-char-fn)
   (j-write-char 
    :initform 'ill-out-any 
    :type j-write-char-fn)		;@@
   (j-write-chars 
    :initform 'ill-out-any 
    :type j-write-chars-fn)		;@@

   (oc-state 
    :initform nil)
   (co-state 
    :initform nil)
   (external-format 
    :initform *default-external-format*)

   (input-handle 
    :initform nil 
    :initarg :input-handle
    :type (or null fixnum stream)
		 
    :accessor stream-input-handle)
   (output-handle 
    :initform nil 
    :initarg :output-handle
    :type (or null fixnum stream)
    :accessor stream-output-handle)
   (control-in 
    :initform nil 
    :type (or null simple-vector))
   (control-out 
    :initform nil 
    :type (or null simple-vector))

   (melded-stream 
    :type (or null simple-stream))
   (melding-base 
    :type (or null simple-stream))

   (encapsulated-char-read-size 
    :initform 0 
    :type fixnum)
   (last-char-read-size 
    :initform 0 
    :type fixnum)
   (charpos 
    :initform 0 
    :type (or null integer)
    :accessor stream-line-column)
   (record-end 
    :initform nil 
    :type (or null fixnum))

   (buffer 
    :initform nil 
    :type (or simple-stream-buffer null))
   (buffpos 
    :initform 0 
    :type fixnum)
   (buffer-ptr 
    :initform 0 
    :type fixnum)
   (buf-len 
    :initform 0 
    :type fixnum)

   (pending 
    :initform nil 
    :type list)
   (handler 
    :initform nil 
    :type (or null handler))))

(defclass single-channel-simple-stream (simple-stream)
  ((mode
    :initform 0
    :type fixnum)))

(defclass dual-channel-simple-stream (simple-stream)
  ((out-buffer
    :initform nil
    :type (or simple-stream-buffer null))
   (outpos
    :initform 0
    :type fixnum)
   (max-out-pos
    :initform 0
    :type fixnum)))

(defclass string-simple-stream (simple-stream) ())


;;;;

;;;; Generic function definitions

(defgeneric device-open (stream options)
  (:documentation "Write me"))

(defgeneric device-close (stream abort)
  (:documentation "Write me"))

(defgeneric device-buffer-length (stream)
  (:documentation "Write me"))

(defgeneric device-file-position (stream)
  (:documentation "Write me"))

(defgeneric (setf device-file-position) (value stream)
  ;; (:argument-precedence-order stream value)
  (:documentation "Write me"))

(defgeneric device-file-length (stream)
  (:documentation "Write me"))

(defgeneric device-read (stream buffer start end blocking)
  (:documentation "Write me"))

(defgeneric device-clear-input (stream buffer-only)
  (:documentation "Write me"))

(defgeneric device-write (stream buffer start end blocking)
  (:documentation "Write me"))

(defgeneric device-clear-output (stream)
  (:documentation "Write me"))

(defgeneric device-finish-record (stream blocking action)
  (:documentation "Write me"))

(defmethod shared-initialize :after ((instance simple-stream) slot-names
				     &rest initargs &key &allow-other-keys)
  (declare (ignore slot-names)
	   (dynamic-extent initargs))
  (unless (slot-boundp instance 'melded-stream)
    (setf (slot-value instance 'melded-stream) instance)
    (setf (slot-value instance 'melding-base) instance))
  (unless (device-open instance initargs)
    (device-close instance t)))

(defmethod print-object ((object simple-stream) stream)
  (print-unreadable-object (object stream :type nil :identity nil)
    (cond ((not (any-stream-instance-flags object :simple))
	   (princ "Invalid " stream))
	  ((not (any-stream-instance-flags object :input :output))
	   (princ "Closed " stream)))
    (format stream "~:(~A~)" (type-of object))))

#+ignore
(defmethod device-close :around ((stream simple-stream) abort)
  (with-stream-class (simple-stream stream)
    (when (any-stream-instance-flags stream :input :output)
      (when (any-stream-instance-flags stream :output)
	(ignore-errors (if abort
			   (clear-output stream)
			 (%finish-output stream))))
      (call-next-method)
      (setf (sm input-handle stream) nil
	    (sm output-handle stream) nil)
      (remove-stream-instance-flags stream :input :output)
      ;; (ext:cancel-finalization stream)
      (setf (stream-external-format stream) :void))))

(defmethod device-close ((stream simple-stream) abort)
  (declare (ignore abort))
  t)

(defmethod device-buffer-length ((stream simple-stream))
  4096)

(defmethod device-file-position ((stream simple-stream))
  (with-stream-class (simple-stream stream)
    (sm buffpos stream)))

(defmethod (setf device-file-position) (value (stream simple-stream))
  (with-stream-class (simple-stream stream)
    (setf (sm buffpos stream) value)))

(defmethod device-file-length ((stream simple-stream))
  nil)

(defmethod (setf stream-external-format) (ef (stream simple-stream))
  (with-stream-class (simple-stream stream)
    (setf (sm external-format stream) (find-external-format ef)))
  ef)

(defmethod (setf stream-external-format) :after (ef (stream single-channel-simple-stream))
  (with-stream-class (single-channel-simple-stream stream)
    (compose-encapsulating-streams stream ef)
    (install-single-channel-character-strategy (melding-stream stream)
					       ef nil)))

(defmethod (setf stream-external-format) :after (ef (stream dual-channel-simple-stream))
  (with-stream-class (dual-channel-simple-stream stream)
    (compose-encapsulating-streams stream ef)
    (install-dual-channel-character-strategy (melding-stream stream) ef)))

;;;(defmethod device-read ((stream single-channel-simple-stream) buffer start end blocking)
;;;  (read-octets stream buffer start end blocking))
;;;
;;;(defmethod device-read ((stream dual-channel-simple-stream) buffer start end blocking)
;;;  (read-octets stream buffer start end blocking))

(defmethod device-clear-input ((stream simple-stream) buffer-only)
  (declare (ignore buffer-only))
  nil)

(defmethod device-write ((stream single-channel-simple-stream) buffer
                         start end blocking)
  ;; buffer may be :flush to force/finish-output
  (when (or (and (null buffer) (not (eql start end)))
	    (eq buffer :flush))
    (with-stream-class (single-channel-simple-stream stream)
      (setf buffer (sm buffer stream))
      (setf end (sm buffpos stream))))
  (write-octets stream buffer start end blocking))

(defmethod device-write ((stream dual-channel-simple-stream) buffer
                         start end blocking)
  ;; buffer may be :flush to force/finish-output
  (when (or (and (null buffer) (not (eql start end)))
	    (eq buffer :flush))
    (with-stream-class (dual-channel-simple-stream stream)
      (setf buffer (sm out-buffer stream))
      (setf end (sm outpos stream))))
  (write-octets stream buffer start end blocking))

(defmethod device-clear-output ((stream simple-stream))
  nil)

;;;; CL layer interface

(defun %check (stream kind)
  (declare (type simple-stream stream)
	   (optimize (speed 3) (space 1) (debug 0) (safety 0)))
  (with-stream-class (simple-stream stream)
    (cond ((not (any-stream-instance-flags stream :simple))
	   (error "~S is uninitialized." stream))
	  ((and (eq kind :open)
		(not (any-stream-instance-flags stream :input :output)))
	   (closed-flame stream))
	  ((and (or (eq kind :input) (eq kind :io))
		(not (any-stream-instance-flags stream :input)))
	   (ill-in-any stream))
	  ((and (or (eq kind :output) (eq kind :io))
		(not (any-stream-instance-flags stream :output)))
	   (ill-out-any stream)))))

(defun %write-char (character stream)
  (etypecase stream
    (function
     (funcall stream 'stream-write-char character))
    (simple-stream
     (with-stream-class (simple-stream stream)
       (%check stream :output)
       (funcall-stm-handler-2 j-write-char character (sm melded-stream stream))))
    (string
     (vector-push-extend character stream))))

(defun %read-line (stream eof-error-p eof-value recursive-p)
  (declare (ignore recursive-p))
  (etypecase stream
    (function
     (funcall stream 'read-line eof-error-p eof-value))
    (simple-stream
     (with-stream-class (simple-stream stream)
       (%check stream :input)
       (when (any-stream-instance-flags stream :eof)
	 (return-from %read-line
	   (eof-or-lose stream eof-error-p eof-value)))
       ;; for interactive streams, finish output first to force prompt
       (when (and (any-stream-instance-flags stream :output)
		  (any-stream-instance-flags stream :interactive))
	 (%finish-output stream))
       (let* ((encap (sm melded-stream stream)) ; encapsulating stream
	      (cbuf (make-string 80))	; current buffer
	      (bufs (list cbuf))	; list of buffers
	      (tail bufs)		; last cons of bufs list
	      (index 0)			; current index in current buffer
	      (total 0))		; total characters
	 (loop
	   (multiple-value-bind (chars done)
	       (funcall-stm-handler j-read-chars encap cbuf
				    #\Newline index (length cbuf) t)
	     (incf index chars)
	     (incf total chars)
	     (when (and (eq done :eof) (zerop total))
	       (if eof-error-p
		   (error 'end-of-file :stream stream)
		 (return (values eof-value t))))
	     (when done
	       ;; If there's only one buffer in use, return it directly
	       (when (null (cdr bufs))
		 (return (values (shrink-vector cbuf total)
				 (eq done :eof))))
	       ;; If total fits in final buffer, use it
	       (when (<= total (length cbuf))
		 (replace cbuf cbuf :start1 (- total index) :end2 index)
		 (let ((idx 0))
		   (declare (type index idx))
		   (do ((list bufs (cdr list)))
		       ((eq list tail))
		     (let ((buf (car list)))
		       (declare (type simple-base-string buf))
		       (replace cbuf buf :start1 idx)
		       (incf idx (length buf)))))
		 (return (values (shrink-vector cbuf total)
				 (eq done :eof))))
	       ;; Allocate new string of appropriate length
	       (let ((string (make-string total))
		     (index 0))
		 (declare (type index index))
		 (dolist (buf bufs)
		   (declare (type simple-base-string buf))
		   (replace string buf :start1 index)
		   (incf index (length buf)))
		 (return  (values string (eq done :eof)))))
	     (when (>= index (length cbuf))
	       (setf cbuf (make-string (the index (* 2 index))))
	       (setf index 0)
	       (setf (cdr tail) (cons cbuf nil))
	       (setf tail (cdr tail))))))))))

(defun %read-char (stream eof-error-p eof-value recursive-p blocking-p)
  (declare (ignore recursive-p))
  (etypecase stream
    (function
     (funcall stream 'stream-read-char))
    (simple-stream
     (with-stream-class (simple-stream stream)
       (%check stream :input)
       (when (any-stream-instance-flags stream :eof)
	 (return-from %read-char
	   (eof-or-lose stream eof-error-p eof-value)))
       ;; for interactive streams, finish output first to force prompt
       (when (and (any-stream-instance-flags stream :output)
		  (any-stream-instance-flags stream :interactive))
	 (%finish-output stream))
       (funcall-stm-handler j-read-char (sm melded-stream stream)
			    eof-error-p eof-value blocking-p)))))

(defun %read-key (stream eof-error-p eof-value recursive-p blocking-p)
  (etypecase stream
    (function
     (funcall stream 'stream-read-key))
    (simple-stream			; XXX
     (%read-char stream eof-error-p eof-value recursive-p blocking-p))))

(defun %unread-char (stream character)
  (declare (type simple-stream stream) (ignore character))
  (with-stream-class (simple-stream stream)
    (%check stream :input)
    (if (zerop (sm last-char-read-size stream))
	(error "Nothing to unread.")
	(progn
	  (funcall-stm-handler j-unread-char (sm melded-stream stream) nil)
	  (remove-stream-instance-flags stream :eof)
	  (setf (sm last-char-read-size stream) 0)))))

(defun %peek-char (stream peek-type eof-error-p eof-value recursive-p)
  (declare (type simple-stream stream)
	   (ignore recursive-p))
  (with-stream-class (simple-stream stream)
    (%check stream :input)
    (when (any-stream-instance-flags stream :eof)
      (return-from %peek-char
	(eof-or-lose stream eof-error-p eof-value)))
    (let* ((encap (sm melded-stream stream))
	   (char (funcall-stm-handler j-read-char encap
				     eof-error-p stream t)))
      (cond ((eq char stream) eof-value)
	    ((characterp peek-type)
	     (do ((char char (funcall-stm-handler j-read-char encap
						  eof-error-p
						  stream t)))
		 ((or (eq char stream) (char= char peek-type))
		  (unless (eq char stream)
		    (funcall-stm-handler j-unread-char encap t))
		  (if (eq char stream) eof-value char))))
	    ((eq peek-type t)
	     (do ((char char (funcall-stm-handler j-read-char encap
						  eof-error-p
						  stream t)))
		 ((or (eq char stream)
		      (not (char-whitespace-p char)))
		  (unless (eq char stream)
		    (funcall-stm-handler j-unread-char encap t))
		  (if (eq char stream) eof-value char))))
	    (t
	     (funcall-stm-handler j-unread-char encap t)
	     char)))))


(defun %finish-output (stream)
  (declare (type simple-stream stream))
  (with-stream-class (simple-stream stream)
    (%check stream :output)
    (when (sm handler stream)
      (do ()
	  ((null (sm pending stream)))
	#+ignore (sys:serve-all-events)))
    (device-write stream :flush 0 nil t)
    (simple-stream-dispatch stream
      (single-channel-simple-stream
       (setf (sm buffpos stream) 0))
      (dual-channel-simple-stream
       (with-stream-class (dual-channel-simple-stream stream)
	 (setf (sm outpos stream) 0)))
      (string-simple-stream
       nil)))
  nil)

(defun %force-output (stream)
  (declare (type simple-stream stream))
  (with-stream-class (simple-stream stream)
    (%check stream :output)
    (device-write stream :flush 0 nil nil)
    (simple-stream-dispatch stream
      (single-channel-simple-stream
       (setf (sm buffpos stream) 0))
      (dual-channel-simple-stream
       (with-stream-class (dual-channel-simple-stream stream)
	 (setf (sm outpos stream) 0)))
      (string-simple-stream)))
  nil)

(defun %clear-output (stream)
  (declare (type simple-stream stream))
  (with-stream-class (simple-stream stream)
    (%check stream :output)
    (when (sm handler stream)
      (setf (sm handler stream) nil
	    (sm pending stream) nil))
    (simple-stream-dispatch stream
      (single-channel-simple-stream
       (with-stream-class (single-channel-simple-stream stream)
	 (case (sm mode stream)
	   (1 (setf (sm buffpos stream) 0))
	   (3 (setf (sm mode stream) 0)))))
      (dual-channel-simple-stream
       (with-stream-class (dual-channel-simple-stream stream)
	 (setf (sm outpos stream) 0)))
      (string-simple-stream))
    (device-clear-output stream)))




;;;; Null stream

(defun null-read-char (stream eof-error-p eof-value blocking)
  (declare (ignore blocking))
  (eof-or-lose stream eof-error-p eof-value))

(defun null-read-chars (stream string search start end blocking)
  (declare (ignore stream string search start end blocking))
  (values 0 :eof))

(defun null-unread-char (stream relaxed)
  (declare (ignore stream relaxed)))

(defun null-write-char (character stream)
  (declare (ignore stream))
  character)

(defun null-write-chars (string stream start end)
  (declare (ignore string stream))
  (- end start))

(defun null-listen (stream)
  (declare (ignore stream))
  nil)

(defclass null-simple-stream (single-channel-simple-stream) ())

(defmethod device-open ((stream null-simple-stream) options)
  (with-stream-class (null-simple-stream stream)
    (add-stream-instance-flags stream :simple :input :output)
    (setf (sm j-read-char stream) 'null-read-char
	  (sm j-read-chars stream) 'null-read-chars
	  (sm j-unread-char stream) 'null-unread-char
	  (sm j-write-char stream) 'null-write-char
	  (sm j-write-chars stream) 'null-write-chars
	  (sm j-listen stream) 'null-listen))
  stream)

(defmethod device-buffer-length ((stream null-simple-stream))
  256)

(defmethod device-write ((stream null-simple-stream) buffer start end blocking)
  (declare (ignore buffer blocking))
  (- end start))

(defmethod device-read ((stream null-simple-stream) buffer start end blocking)
  (declare (ignore buffer start end blocking))
  -1)

;;;;; String stream

(defclass string-input-simple-stream (string-simple-stream) ())

(defclass string-output-simple-stream (string-simple-stream)
  ((out-buffer
    :initform nil
    :type (or simple-stream-buffer null))
   (outpos
    :initform 0
    :type fixnum)
   (max-out-pos
    :initform 0
    :type fixnum)))

(defclass composing-stream (string-simple-stream) ())

(defun install-string-input-character-strategy (stream)
  #| implement me |#
  (with-stream-class (simple-stream stream)
    (setf (sm j-read-char stream) #'string-read-char-e-crlf))
  stream)

(defun install-string-output-character-strategy (stream)
  (declare (ignore stream))
  #| implement me |#)

(defun string-read-char-e-crlf (stream eof-error-p eof-value blocking)
  (with-stream-class (composing-stream stream)
    (let* ((encap (sm melded-stream stream))
	   (ctrl (sm control-in stream))
           (char (funcall-stm-handler j-read-char encap nil stream blocking)))
      ;; if CHAR is STREAM, we hit EOF; if NIL, blocking is NIL and no
      ;; character was available...
      (when (eql char #\Return)
        (let ((next (funcall-stm-handler j-read-char encap nil stream blocking)))
          ;; if NEXT is STREAM, we hit EOF, so we should just return the
          ;; #\Return (and mark the stream :EOF?  At least unread if we
          ;; got a soft EOF, from a terminal, etc.
          ;; if NEXT is NIL, blocking is NIL and there's a CR but no
          ;; LF available on the stream: have to unread the CR and
          ;; return NIL, letting the CR be reread later.
          ;;
          ;; If we did get a linefeed, adjust the last-char-read-size
          ;; so that an unread of the resulting newline will unread both
          ;; the linefeed _and_ the carriage return.
          (if (eql next #\Linefeed)
              (setq char #\Newline)
              (funcall-stm-handler j-unread-char encap nil))))
      (when (characterp char)
	(let ((code (char-code char)))
	  (when (and (< code 32) ctrl (svref ctrl code))
	    (setq char (funcall (the (or symbol function) (svref ctrl code))
				stream char)))))
      (if (eq char stream)
	  (eof-or-lose stream eof-error-p eof-value)
	char))))

(defmethod device-open :before ((stream string-input-simple-stream) options)
  ;; Taken with permission from ftp://ftp.franz.com/pub/duane/Simp-stms.ppt
  (with-stream-class (string-input-simple-stream stream)
    (let ((string (getf options :string)))
      (when (and string (null (sm buffer stream)))
	(let ((start (getf options :start))
	      (end (or (getf options :end) (length string))))
	  (setf (sm buffer stream) string
		(sm buffpos stream) start
		(sm buffer-ptr stream) end))))
    (install-string-input-character-strategy stream)
    (add-stream-instance-flags stream :string :input :simple)))

#+ignore
(defmethod device-open :before ((stream string-output-simple-stream) options)
  ;; Taken with permission from ftp://ftp.franz.com/pub/duane/Simp-stms.ppt
  (with-stream-class (string-output-simple-stream stream)
    (unless (sm out-buffer stream)
      (let ((string (getf options :string)))
	(if string
	    (setf (sm out-buffer stream) string
		  (sm max-out-pos stream) (length string))
	    (let ((buflen (max (device-buffer-length stream) 16)))
	      (setf (sm out-buffer stream) (make-string buflen)
		    (sm max-out-pos stream) buflen)))))
    (unless (sm control-out stream)
      (setf (sm control-out stream) *std-control-out-table*))
    (install-string-output-character-strategy stream)
    (add-stream-instance-flags stream :string :output :simple)))

(defmethod device-open ((stream string-simple-stream) options)
  (declare (ignore options))
  (with-stream-class (string-simple-stream stream)
    (if (and (any-stream-instance-flags stream :simple)
	     (any-stream-instance-flags stream :input :output))
	t
	nil)))

(defmethod device-file-position ((stream string-simple-stream))
  (with-stream-class (simple-stream stream)
    (sm buffpos stream)))

(defmethod (setf device-file-position) (value (stream string-simple-stream))
  (with-stream-class (simple-stream stream)
    (cond ((or (> value (sm buffer-ptr stream))
	       (< value (- -1 (sm buffer-ptr stream))))
	   nil)
	  ((>= value 0)
	   (setf (sm buffpos stream) value)
	   t)
	  (t
	   (setf (sm buffpos stream) (+ (sm buffer-ptr stream) value 1))
	   t))))

(defmethod device-file-length ((stream string-simple-stream))
  (with-stream-class (simple-stream stream)
    (sm buffer-ptr stream)))

