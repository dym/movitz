;;;Ext2 fs package -- Copyright (C) 2004 Alessio Stalla

(require :muerte/integers)

(require :tmp/harddisk)
(require :tmp/partitions)
(require :tmp/fs)

(provide :tmp/ext2fs)

(defpackage fs.ext2
  (:use muerte.cl
	muerte
	muerte.lib)
  (:import-from muerte.x86-pc.harddisk hd-read-sectors))

(in-package fs.ext2)

(defvar *known-magic-numbers* '(#xEF53))

;Possible values of an inode's "type" attribute
(defconstant +it-format-mask+  #xf0)
(defconstant +it-socket+       #xc0)
(defconstant +it-symlink+      #xa0)
(defconstant +it-file+         #x80)
(defconstant +it-block-device+ #x60)
(defconstant +it-directory+    #x40)
(defconstant +it-char-device+  #x20)
(defconstant +it-fifo+         #x10)

;;;
;;;Classes and structures 
;;;

;;The ext2-fs class is simply a container for the closures created by mount;
;;it is intended to only be passed as an argument to the generic functions in
;;the fs package
(defclass ext2-fs (fs::fs) ())

;;An ext2 superblock -- contains important information relative to the entire
;;filesystem
(defstruct superblock
  (inodes_count 0 :type (unsigned-byte 32))
  (blocks_count 0 :type (unsigned-byte 32))
  (r_blocks_count 0 :type (unsigned-byte 32))
  (free_blocks_count 0 :type (unsigned-byte 32))
  (free_inodes_count 0 :type (unsigned-byte 32))
  (first_data_block 0 :type (unsigned-byte 32))
  (log_block_size 0 :type (unsigned-byte 32))
  (log_frag_size 0 :type (unsigned-byte 32))
  (blocks_per_group 0 :type (unsigned-byte 32))
  (s_frags_per_group 0 :type (unsigned-byte 32))
  (inodes_per_group 0 :type (unsigned-byte 32))
  (s_mtime 0 :type (unsigned-byte 32))
  (s_wtime 0 :type (unsigned-byte 32))
  (s_mnt_count 0 :type (unsigned-byte 16))
  (s_max_mnt_count 0 :type (unsigned-byte 16))
  (s_magic 0 :type (unsigned-byte 16))
  (s_state 0 :type (unsigned-byte 16))
  (s_errors 0 :type (unsigned-byte 16))
  (s_minor_rev_level 0 :type (unsigned-byte 16))
  (s_lastcheck 0 :type (unsigned-byte 32))
  (s_checkinterval 0 :type (unsigned-byte 32))
  (s_creator_os 0 :type (unsigned-byte 32))
  (s_rev_level 0 :type (unsigned-byte 32))
  (s_def_resuid 0 :type (unsigned-byte 16))
  (s_def_resgid 0 :type (unsigned-byte 16))
  (s_first_ino 0 :type (unsigned-byte 32))
  (s_inode_size 0 :type (unsigned-byte 16))
  (s_block_group_nr 0 :type (unsigned-byte 16)))
;     92       4 s_feature_compat
;     96       4 s_feature_incompat
;    100       4 s_feature_ro_compat
;    104      16 s_uuid
;    120      16 s_volume_name
;    136      64 s_last_mounted
;    200       4 s_algo_bitmap


;;A group descriptor -- contains important info relative to a block group
(defstruct group-descriptor
  (bg_block_bitmap 0 :type (unsigned-byte 32))
  (bg_inode_bitmap 0 :type (unsigned-byte 32))
  (inode-table 0 :type (unsigned-byte 32))
  (bg_free_blocks_count 0 :type (unsigned-byte 16))
  (bg_free_inodes_count 0 :type (unsigned-byte 16))
  (bg_used_dirs_count 0 :type (unsigned-byte 16))
  bg_reserved)


;;An inode -- represents an object in the fs (e.g. file, directory, symlink...)
(defstruct inode
  type
  access_rights
  (uid 0 :type (unsigned-byte 16))
  (size 0 :type (unsigned-byte 32))
  (atime 0 :type (unsigned-byte 32))
  (ctime 0 :type (unsigned-byte 32))
  (mtime 0 :type (unsigned-byte 32))
  (dtime 0 :type (unsigned-byte 32))
  (gid 0 :type (unsigned-byte 16))
  (links_count 0 :type (unsigned-byte 16))
  (blocks 0 :type (unsigned-byte 32))
  (flags 0 :type (unsigned-byte 32))
  (osd1 0 :type (unsigned-byte 32))
  block
  (generation 0 :type (unsigned-byte 32))
  (file_acl 0 :type (unsigned-byte 32))
  (dir_acl 0 :type (unsigned-byte 32))
  (faddr 0 :type (unsigned-byte 32))
  (osd2 0 :type (unsigned-byte 96)))


;;;
;;;Miscellaneous functions and macros -- should be moved elsewhere
;;;

(defun exp256 (exp)
  (case exp
    (0 #x1)
    (1 #x100)
    (2 #x10000)
    (3 #x1000000)
    (4 #x100000000)
    (t (expt 256 exp))))

(defun exp2 (exp)
  (case exp
    (0 1)
    (1 2)
    (2 4)
    (3 8)
    (4 16)
    (t (expt 2 exp))))

(defun little-endian-to-integer (byte-array start length)
  (let ((res 0))
    (dotimes (i length)
      (incf res (* (exp256 i) (aref byte-array (+ i start)))))
    res))

(defun vconc (&rest args)
  (declare (dynamic-extent args))
  (apply #'concatenate 'vector args))

(define-modify-macro vconcf (&rest args) vconc)

(defun make-string-from-bytes (byte-array)
  (let* ((len (length byte-array))
	 (str (make-string len)))
    (dotimes (i len)
      (setf (aref str i) (code-char (aref byte-array i))))
    str))

(defun split-string (str delim)
  (delete "" (loop with start = 0
		   with len = (length str)
		   for i = (position delim str :start start)
		   while (<= start len)
		   if i collect (subseq str start i) into lst
		        and do (setq start (1+ i))
		   else collect (subseq str start) into lst and return lst)
	  :test #'string=))

(defmacro aif (test then &optional else)
  `(let ((it ,test))
    (if it ,then ,else)))

(defun test-aif (x)
  (aif x (print it) (print 'else)))


;;;
;;;ext2-related functions
;;;

(defun read-superblock (hdn sect)
  "Initializes a superblock structure reading data from the specified hard disk and sector"
  (let ((sbdata (hd-read-sectors hdn sect 1)))
    (if (member (little-endian-to-integer sbdata 56 2) *known-magic-numbers*)
	(make-superblock
	 :inodes_count (little-endian-to-integer sbdata 0 4)
	 :blocks_count (little-endian-to-integer sbdata 4 4)
	 :r_blocks_count (little-endian-to-integer sbdata 8 4)
	 :free_blocks_count (little-endian-to-integer sbdata 12 4)
	 :free_inodes_count (little-endian-to-integer sbdata 16 4)
	 :first_data_block (little-endian-to-integer sbdata 20 4)
	 :log_block_size (little-endian-to-integer sbdata 24 4)
	 :log_frag_size (little-endian-to-integer sbdata 28 4)
	 :blocks_per_group (little-endian-to-integer sbdata 32 4)
	 :s_frags_per_group (little-endian-to-integer sbdata 36 4)
	 :inodes_per_group (little-endian-to-integer sbdata 40 4)
	 :s_mtime (little-endian-to-integer sbdata 44 4)
	 :s_wtime (little-endian-to-integer sbdata 48 4)
	 :s_mnt_count (little-endian-to-integer sbdata 52 2)
	 :s_max_mnt_count (little-endian-to-integer sbdata 54 2)
	 :s_magic (little-endian-to-integer sbdata 56 2)
	 :s_state (little-endian-to-integer sbdata 58 2)
	 :s_errors (little-endian-to-integer sbdata 60 2)
	 :s_minor_rev_level (little-endian-to-integer sbdata 62 2)
	 :s_lastcheck (little-endian-to-integer sbdata 64 4)
	 :s_checkinterval (little-endian-to-integer sbdata 68 4)
	 :s_creator_os (little-endian-to-integer sbdata 72 4)
	 :s_rev_level (little-endian-to-integer sbdata 76 4)
	 :s_def_resuid (little-endian-to-integer sbdata 80 2)
	 :s_def_resgid (little-endian-to-integer sbdata 82 2))
	(error "Can't read ext2 superblock -- invalid magic number. Either this is not an ext2 fs, or it is corrupted; in this case, try reading a superblock backup copy"))))

(defun read-group-descriptors (hdn sect howmany)
  "Initializes an array of <howmany> group-descriptor structures reading data from the sector sect of the specified hard disk"
  (let ((data (hd-read-sectors hdn sect howmany))
	(arr (make-array howmany)))
    (loop for i from 0 to (1- howmany)
	  for j = (* 32 i)
	  do (setf (aref arr i)
		   (make-group-descriptor
		    :bg_block_bitmap (little-endian-to-integer data j 4)
		    :bg_inode_bitmap (little-endian-to-integer data (+ j 4) 4)
		    :inode-table (little-endian-to-integer data (+ j 8) 4)
		    :bg_free_blocks_count (little-endian-to-integer data (+ j 12) 2)
		    :bg_free_inodes_count (little-endian-to-integer data (+ j 14) 2)
		    :bg_used_dirs_count (little-endian-to-integer data (+ j 16) 2))))
    arr))

(defun read-inodes (hdn sect howmany)
  "Reads some inodes"
  (let* ((data (hd-read-sectors hdn sect (1+ (truncate (/ (1- howmany) 4)))))
	 (arr (make-array howmany :element-type 'inode))
	 (blockdata (make-array 15)))
;    (format t "reading ~A inodes from sector ~A~%" howmany sect)
    (dotimes (i howmany)
      (dotimes (j 15)
        (setf (aref blockdata j) (little-endian-to-integer data (+ 40 (* 4 j) (* 128 i)) 4)))
      (setf (aref arr i)
	    (make-inode
	     :type (logand #xf0 (aref data (1+ (* 128 i))))
	     :access_rights (logand #x0fff (little-endian-to-integer data (* 128 i) 2))
	     :uid (little-endian-to-integer data (+ 2 (* 128 i)) 2)
	     :size (little-endian-to-integer data (+ 4 (* 128 i)) 4)
	     :links_count (little-endian-to-integer data (+ 26 (* 128 i)) 2)
	     :blocks (little-endian-to-integer data (+ 28 (* 128 i)) 4)
	     :flags (little-endian-to-integer data (+ 32 (* 128 i)) 4)
	     :block (copy-seq blockdata))))
    arr))


;;;
;;;The "main" function, mount
;;;

(defun mount (hdn part &key (sb-sect 2) (inode-cache-size 15))
  "Returns an ext2-fs instance reading data from the specified hard disk and partition"
  (let* ((pstart (muerte.x86-pc.harddisk::partition-start part))
	 (sb (read-superblock hdn (+ pstart sb-sect)))
	 (blocksize (exp2 (1+ (superblock-log_block_size sb))))
	 (blocksize-bytes (* 512 blocksize))
	 (group-descriptors (read-group-descriptors
			     hdn
			     (+ pstart
				(* blocksize (superblock-first_data_block sb))
				blocksize)
			     (1+ (truncate (/ (superblock-blocks_count sb)
					      (superblock-blocks_per_group sb))))))
	 (root (aref
		(read-inodes
		 0
		 (+ pstart
		    (* blocksize
		       (group-descriptor-inode-table (aref group-descriptors 0))))
		 2)
		1))
	 (inode-cache (make-array inode-cache-size
				  :initial-element (vector nil nil)))
	 (inode-cache-ptr 0)
	 (open-files ()))
    (macrolet ((dir-loop (return-value &rest loop-clauses)
		 `(let* ((file (%open-file inode))
			 (val (loop with size = (inode-size inode)
				    with count = 0
				    for num    = (little-endian-to-integer
						  (%read-data file 4) 0 4)
				    for reclen = (little-endian-to-integer
						  (%read-data file 2) 0 2)
				    for strlen = (aref (%read-data file) 0)
				    for type   = (%read-data file)
				    for name   = (make-string-from-bytes (%read-data file strlen))
				    do (%read-data file (- reclen strlen 8)) ;Padding
				    ,@loop-clauses
				    do (incf count reclen)
				    if (>= count size) return ,return-value)))
		   (%close-file file)
		   val)))
      (labels ((%read-inode (num)
		 "Reads the inode number num from the inode table"
		 (let ((num0 (1- num)))
		   (aif (find num inode-cache :test #'equal :key #'(lambda (x) (aref x 0)))
			(aref it 1)
			(let* ((block-group (truncate (/ num0 (superblock-inodes_per_group sb))))
			       (inode (aref (read-inodes
					     hdn
					     (+ pstart
						(* blocksize
						   (group-descriptor-inode-table
						    (aref group-descriptors block-group)))
						(truncate (/ (- num0 (* block-group (superblock-inodes_per_group sb))) 4)))
					     4)
					    (mod (- num0 (* block-group (superblock-inodes_per_group sb))) 4))))
			  (setf (aref inode-cache inode-cache-ptr) (vector num inode))
			  (setq inode-cache-ptr (mod (1+ inode-cache-ptr) inode-cache-size))
			  inode)))) 	     
	       (%inode-block-to-address (inode blocknum)
		 "Converts one of the block fields of the inode structure into a physical address"
		 (+ pstart
		    (* blocksize
		       (cond
			 ((< blocknum 12) (aref (inode-block inode) blocknum))
			 ((and (>= blocknum 12)
			       (< blocknum (+ 12 (* 128 blocksize))))
			  (aref (hd-read-sectors
				 hdn
				 (+ pstart (* blocksize (aref (inode-block inode) 12)))
				 blocksize)
				(- blocknum 12)))
	;;Bi-indirect and tri-indirect blocks not implemented yet
			  ))))
	       
	       (%open-file (inode &optional (name "Unknown") (mode :read))
		 (let ((file-handle (gensym)))
		   (case mode
		     (:read (push (list file-handle inode 0 name :read nil)
				  open-files))
		     (t (error "Unknown mode: ~A" mode)))
		   file-handle))
	     
	       (%close-file (handle)
		 (setq open-files (delete handle open-files :key #'car)))
	       
	       (%read-data (handle &optional (bytes 1))
		 "Reads at most <bytes> bytes from the specified file. Returns as much data as could be read from the file (if bytes > 1), or :eof if the end of the file has been reached. Note that file actually means inode, i.e. this function can also read directories."
		 (let* ((filedata (assoc handle open-files))
			(inode (second filedata))
			(size (inode-size inode))
			(fileptr (third filedata))
			(name (fourth filedata))
			(mode (fifth filedata))
			(blocknum (truncate (/ fileptr blocksize-bytes))))
		   (when (> (+ fileptr bytes) size)
		     (if (and (> bytes 1) (< fileptr size))
			 (return-from %read-data (%read-data handle (- size fileptr)))
			 (return-from %read-data :eof)))
		   (when (< bytes 1) (return-from %read-data #()))
		   (if (and filedata (member mode '(:read)))
		       (apply #'vconc
			      (loop with ptr = (- fileptr (* blocknum blocksize-bytes))
				    with left = bytes
				    while (> left 0)
				    if (eq (sixth filedata) nil)
				       do (setf (sixth filedata) (hd-read-sectors hdn (%inode-block-to-address inode blocknum) blocksize))
				    if (<= (+ ptr left) blocksize-bytes)
				       collect (subseq (sixth filedata) ptr (+ ptr left)) into lst
				       and do (incf (third filedata) left)
				       and return lst
				    else collect (subseq (sixth filedata) ptr) into lst
				         do (incf blocknum)
					 do (setf (sixth filedata) (hd-read-sectors hdn (%inode-block-to-address inode blocknum) blocksize))
					 do (decf left (- blocksize-bytes ptr))
					 do (incf (third filedata) (- blocksize-bytes ptr))
					 do (setq ptr 0)))
		       (error "File not open for reading: ~A" name))))
	     
	       (%list-dir (inode)
		 "Returns an array of the directory entries of inode, in the form (name <inode>)"
		 (dir-loop result
			   collect (list name (%read-inode num)) into result))
	     
	       (%find-dir-entry (inode entry-name)
		 "Searches for a given directory entry"
		 (dir-loop nil
                           if (string= name entry-name)
                              return (%read-inode num)))
	     
	       (%path-to-inode (path)
		 "Converts an (absolute) path into an inode"
		 (let ((path2 (split-string path #\/))
		       (inode root))
;		   (format t "path2 = ~A~% " path2)
;		   (read)
		   (if (null path2)
		       root
		       (progn
			 (dolist (x (butlast path2))
			   (setq inode (%find-dir-entry inode x))
			   (when (null inode)
			     (return)))
			 (if (null inode)
			     nil
			     (%find-dir-entry inode (car (last path2)))))))))
;	(print (%path-to-inode "/"))
;	(print (%path-to-inode "/."))
;	(print (%path-to-inode "/etc/"))

;	(format t "Inodes per group: ~A~%" (superblock-inodes_per_group sb))
;	(print (%path-to-inode "/etc/fstab"))
	(make-instance 'ext2-fs
		       :open-file-fn #'(lambda (path &optional (mode :read))
				      (let ((inode (%path-to-inode path)))
					(cond
					  ((null inode)
					   (error "File doesn't exist: ~A" path))
					  ((= (inode-type inode) +it-directory+)
					   (error "File ~A is a directory!" path))
					  (t (%open-file inode path mode)))))
		       :read-file-fn #'%read-data
		       :write-file-fn #'(lambda (file-handle data)
				       (declare (ignore file-handle data))
				       (warn "Not implemented!"))
		       :close-file-fn #'%close-file
		       :delete-file-fn #'(lambda (path)
					(declare (ignore path))
					(warn "Not implemented!"))
		       :list-open-files-fn #'(lambda () open-files) ;TODO!!
		       :list-dir-fn #'(lambda (path)
				     (let ((inode (%path-to-inode path)))
				       (if (= (inode-type inode) +it-directory+)
					   (%list-dir inode)
					   (error "~A is not a directory!" path))))
		       :create-dir-fn #'(lambda (path)
				       (declare (ignore path))
				       (warn "Not implemented!"))
		       :delete-dir-fn #'(lambda (path &optional (recursive-p nil))
				       (declare (ignore path recursive-p))
				       (warn "Not implemented!")))))))

