;;;Filesystem package -- Copyright (C) 2004 Alessio Stalla
;;;Provides the classes and functions to implement different file systems

(require :tmp/harddisk)
(require :tmp/partitions)

(provide :tmp/fs)

(defpackage fs
  (:use muerte.cl
	muerte
	muerte.lib))

(in-package fs)

(defvar *fs-table* (make-hash-table)
  "The hash table that associates partition types with file systems")

;;Every file system implementation should provide a "mount" function which
;;returns an instance of (a subclass of) fs
(defclass fs ()
  ((open-file-fn :reader get-open-file-fn :initarg :open-file-fn)
   (read-file-fn :reader get-read-file-fn :initarg :read-file-fn)
   (write-file-fn :reader get-write-file-fn :initarg :write-file-fn)
   (close-file-fn :reader get-close-file-fn :initarg :close-file-fn)
   (delete-file-fn :reader get-delete-file-fn :initarg :delete-file-fn)
   (list-open-files-fn :reader get-list-open-files-fn :initarg :list-open-files-fn)
   (list-dir-fn :reader get-list-dir-fn :initarg :list-dir-fn)
   (create-dir-fn :reader get-create-dir-fn :initarg :create-dir-fn)
   (delete-dir-fn :reader get-delete-dir-fn :initarg :delete-dir-fn)))

(defun open-file (fs path)
  (funcall (get-open-file-fn fs) path))

(defun read-file (fs handle &optional (count 1))
  (funcall (get-read-file-fn fs) handle count))

(defun write-file (fs handle data)
  (funcall (get-write-file-fn fs) handle data))

(defun close-file (fs handle)
  (funcall (get-close-file-fn fs) handle))

(defun delete-file (fs path)
  (funcall (get-delete-file-fn fs) path))

(defun list-open-files (fs)
      (funcall (get-list-open-files-fn fs)))

(defun list-dir (fs path)
  (funcall (get-list-dir-fn fs) path))

(defun create-dir (fs path)
  (funcall (get-create-dir-fn fs) path))

(defun delete-dir (fs path)
  (funcall (get-delete-dir-fn fs) path))

(defun add-fs (num mount-fn)
  (setf (gethash num *fs-table*) mount-fn))

;;"Mounts" a filesystem from the desired partition
(defun mount (hdn partn &rest other-args)
  (declare (dynamic-extent other-args))
  (let* ((part (aref (muerte.x86-pc.harddisk::read-partition-table hdn 0) partn))
	 (fn (gethash (muerte.x86-pc.harddisk::partition-type part) *fs-table*)))
    (if fn
	(apply fn hdn part other-args)
	(error "Unsupported filesystem! (Partition type ~A)~%"
	       (muerte.x86-pc.harddisk::partition-type part)))))