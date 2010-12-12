;;;Ext2 fs package -- Copyright (C) 2004 Alessio Stalla
;;;                                 2010 Dmitriy Budashny
;
; Block Group structure:
; |Superblock | Group Descriptors |Block Bitmap|INode Bitmap|INode Table|Data blocks|
; |-------------------------------|-------------------------------------------------|
; |This is the same for all groups| this is specific to each group                  |

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

;;; Special inodes numbers
(defconstant +ext2-bad-ino+ 1) ; Bad blocks inode
(defconstant +ext2-root-ino+ 2)	; Root inode
(defconstant +ext2-acl-idx-ino+ 3) ; ACL inode
(defconstant +ext2-acl-data-ino+ 4) ; ACL inode
(defconstant +ext2-boot-loader-ino+ 5) ; Boot loader inode
(defconstant +ext2-undel-dir-ino+ 6) ; Undelete directory inode
; First non-reserved inode for old ext2 filesystems
(defconstant +ext2-good-old-first-ino+ 11)

; The second extended file system magic number
(defconstant +ext2-super-magic+ '(#xEF53))

; Maximal count of links to a file
(defconstant +ext2-link-max+ 32000)

;;; Block sizes
(defconstant +ext2-min-block-size+ 1024)
(defconstant +ext2-max-block-size+ 4096)
(defconstant +ext2-min-block-log-size+ 10)
; TODO: put here all that calculations from ext2_fs.h

;;; Fragments
(defconstant +ext2-min-frag-size+ 1024)
(defconstant +ext2-max-frag-size+ 4096)
(defconstant +ext2-min-frag-log-size+ 10)
; TODO: put here all that calculations from ext2_fs.h

;;; Constants relative to the data blocks
(defconstant +ext2-ndir-blocks+ 12)
(defconstant +ext2-ind-block+ +ext2-ndir-blocks+)
(defconstant +ext2-dind-block+ (+ +ext2-ind-block+ 1))
(defconstant +ext2-tind-block+ (+ +ext2-dind-block+ 1))
(defconstant +ext2-n-blocks+ (+ +ext2-tind-block+ 1))

;;; Inode flags
(defconstant +ext2-secrm-fl+ #x00000001) ; Secure deletion
(defconstant +ext2-unrm-fl+ #x00000002) ; Undelete
(defconstant +ext2-compr-fl+ #x00000004) ; Compress file
(defconstant +ext2-sync-fl+ #x00000008) ; Synchronous updates
(defconstant +ext2-immutable-fl+ #x00000010) ; Immutable file
(defconstant +ext2-append-fl+ #x00000020) ; writes to file may only append
(defconstant +ext2-nodump-fl+ #x00000040) ; do not dump file
(defconstant +ext2-noatime-fl+ #x00000080) ; do not update atime
;; Reserved for compression usage...
(defconstant +ext2-dirty-fl+ #x00000100)
(defconstant +ext2-comprblk-fl+ #x00000200) ; One or more compressed clusters
(defconstant +ext2-nocomp-fl+ #x00000400) ; Don't compress
(defconstant +ext2-ecompr-fl+ #x00000800) ; Compression error
;; End compression flags --- maybe not all used
(defconstant +ext2-btree-fl+ #x00001000) ; btree format dir
(defconstant +ext2-reserved-fl+ #x80000000) ; reserved for ext2 lib
(defconstant +ext2-fl-user-visible+ #x00001FFF) ; User visible flags
(defconstant +ext2-fl-user-modifiable+ #x000000FF) ; User modifiable flags

;; File system states
(defconstant +ext2-valid-fs+ #x0001) ; Unmounted cleanly
(defconstant +ext2-error-fs+ #x0002) ; Errors detected

;; Mount flags
(defconstant +ext2-mount-check-normal+ #x0001) ; Do some more checks
(defconstant +ext2-mount-check-strict+ #x0002) ; Do again more checks
(defconstant +ext2-mount-check+ #x0003)
(defconstant +ext2-mount-grpid+	#x0004)	; Create files with directory's group
(defconstant +ext2-mount-debug+ #x0008)	; Some debugging messages
(defconstant +ext2-mount-errors-cont+ #x0010) ; Continue on errors
(defconstant +ext2-mount-errors-ro+ #x0020) ; Remount fs ro on errors
(defconstant +ext2-mount-errors-panic+ #x0040) ; Panic on errors
(defconstant +ext2-mount-minix-df+ #x0080) ; Mimics the Minix statfs

;; Maximal mount counts between two filesystem checks
(defconstant +ext2-dfl-max-mnt-count+ 20) ; Allow 20 mounts
(defconstant +ext2-dfl-checkinterval+ 0) ; Don't use interval check

;; Behaviour when detecting errors
(defconstant +ext2-errors-continue+ 1) ; Continue execution
(defconstant +ext2-errors-ro+ 2) ; Remount fs read-only
(defconstant +ext2-errors-panic+ 3) ; Panic
(defconstant +ext2-errors-default+ +ext2-errors-continue+)

;; Codes for operating systems
(defconstant +ext2-os-linux+ 0)
(defconstant +ext2-os-hurd+ 1)
(defconstant +ext2-os-masix+ 2)
(defconstant +ext2-os-freebsd+ 3)
(defconstant +ext2-os-lites+ 4)

;; Revision levels
(defconstant +ext2-good-old-rev+ 0) ; The good old (original) format
(defconstant +ext2-dynamic-rev+ 1) ; V2 format w/ dynamic inode sizes
(defconstant +ext2-current-rev+	+ext2-good-old-rev+)
(defconstant +ext2-max-supp-rev+ +ext2-dynamic-rev+)
(defconstant +ext2-good-old-inode-size+ 128)

;;; Feature set definitions
;; s-feature-compat
(defconstant +ext2-feature-compat-dir-prealloc+ #x0001)

;; s-feature-incompat
(defconstant +ext2-feature-incompat-compression+ #x0001)
(defconstant +ext2-feature-incompat-filetype+ #x0002)

;; s-feature-ro-compat
; Doesn't store superblock in every block group but just in some
(defconstant +ext2-feature-ro-compat-sparse-super+ #x0001)
(defconstant +ext2-feature-ro-compat-large-file+ #x0002)
(defconstant +ext2-feature-ro-compat-btree-dir+	#x0004)

(defconstant +ext2-feature-compat-supp+ 0)
(defconstant +ext2-feature-incompat-supp+ +ext2-feature-incompat-filetype+)
(defconstant +ext2-feature-ro-compat-supp+ +ext2-feature-ro-compat-sparse-super+)

;; Default values for user and/or group using reserved blocks
(defconstant +ext2-def-resuid+ 0)
(defconstant +ext2-def-resgid+ 0)

;; Directory entry
(defconstant +ext2-name-len+ 255)

;; Ext2 directory file types.  Only the low 3 bits are used.  The
;; other bits are reserved for now.
(defconstant +ext2-ft-unknown+ 0)
(defconstant +ext2-ft-reg-file+	1)
(defconstant +ext2-ft-dir+ 2)
(defconstant +ext2-ft-chrdev+ 3)
(defconstant +ext2-ft-blkdev+ 4)
(defconstant +ext2-ft-fifo+ 5)
(defconstant +ext2-ft-sock+ 6)
(defconstant +ext2-ft-symlink+ 7)
(defconstant +ext2-ft-max+ 8)


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

;; ACL structures
; Header of Access Control Lists
(defstruct ext2-acl-header
  (aclh-size 0 :type (unsigned-byte 32))
  (aclh-file-count 0 :type (unsigned-byte 32))
  (aclh-acle-count 0 :type (unsigned-byte 32))
  (aclh-first-acle 0 :type (unsigned-byte 32)))

; Access Control List Entry */
(defstruct ext2-acl-entry
  (acle-size 0 :type (unsigned-byte 32))
  (acle-perms 0 :type (unsigned-byte 16)) ; Access permissions
  (acle-type 0 :type (unsigned-byte 16)) ; Type of entry
  (acle-tag 0 :type (unsigned-byte 16))	; User or group identity
  (acle-pad1 0 :type (unsigned-byte 16))
  (acle-next 0 :type (unsigned-byte 32))) ; Pointer on next entry for the same inode or on next free entry

;; Structure of a blocks group descriptor
(defstruct ext2-group-desc
  (bg-block-bitmap 0 :type (unsigned-byte 32)) ; Blocks bitmap block
  (bg-inode-bitmap 0 :type (unsigned-byte 32)) ; Inodes bitmap block
  (bg-inode-table 0 :type (unsigned-byte 32)) ; Inodes table block
  (bg-free-blocks-count 0 :type (unsigned-byte 16)) ; Free blocks count
  (bg-free-inodes-count 0 :type (unsigned-byte 16)) ; Free inodes count
  (bg-used-dirs-count 0 :type (unsigned-byte 16)) ; Directories count
  (bg-pad 0 :type (unsigned-byte 16))
  (bg-reserved 0 :type (unsigned-byte 96)))

;; Structure of an inode on the disk
(defstruct ext2-inode
  (i-mode 0 :type (unsigned-byte 16)) ; File mode
  (i-uid 0 :type (unsigned-byte 16)) ; Owner Uid
  (i-size 0 :type (unsigned-byte 32)) ; Size in bytes
  (i-atime 0 :type (unsigned-byte 32)) ; Access time
  (i-ctime 0 :type (unsigned-byte 32)) ; Creation time
  (i-mtime 0 :type (unsigned-byte 32)) ; Modification time
  (i-dtime 0 :type (unsigned-byte 32)) ; Deletion Time
  (i-gid 0 :type (unsigned-byte 16)) ; Group Id
  (i-links-count 0 :type (unsigned-byte 16)) ; Links count
  (i-blocks 0 :type (unsigned-byte 32)) ; Blocks count
  (i-flags 0 :type (unsigned-byte 32)) ; File flags
  (osd1 0 :type (unsigned-byte 32)) ; OS dependent 1
  (i-block 0 :type (unsigned-byte (* 32 +ext2-n-blocks+))) ; Pointers to blocks
  (i-generation 0 :type (unsigned-byte 32)) ; File version (for NFS)
  (i-file-acl 0 :type (unsigned-byte 32)) ; File ACL
  (i-dir-acl 0 :type (unsigned-byte 32)) ; Directory ACL
  (i-faddr 0 :type (unsigned-byte 32)) ; Fragment address
  (osd2 0 :type (unsigned-byte 96))) ; OS dependent 2



;; Structure of the super block
(defstruct ext2-super-block
  (s-inodes-count 0 :type (unsigned-byte 32)) ; Inodes count
  (s-blocks-count 0 :type (unsigned-byte 32)) ; Blocks count
  (s-r-blocks-count 0 :type (unsigned-byte 32)) ; Reserved blocks count
  (s-free-blocks-count 0 :type (unsigned-byte 32)) ; Free blocks count
  (s-free-inodes-count 0 :type (unsigned-byte 32)) ; Free inodes count
  (s-first-data-block 0 :type (unsigned-byte 32)) ; First Data Block
  (s-log-block-size 0 :type (unsigned-byte 32)) ; Block size (0=1k, 1=2k, 2=4k)
  (s-log-frag-size 0 :type (unsigned-byte 32)) ; Fragment size
  (s-blocks-per-group 0 :type (unsigned-byte 32)) ; # Blocks per group
  (s-frags-per-group 0 :type (unsigned-byte 32)) ; # Fragments per group
  (s-inodes-per-group 0 :type (unsigned-byte 32)) ; # Inodes per group
  (s-mtime 0 :type (unsigned-byte 32)) ; Mount time
  (s-wtime 0 :type (unsigned-byte 32)) ; Write time
  (s-mnt-count 0 :type (unsigned-byte 16)) ; Mount count
  (s-max-mnt-count 0 :type (unsigned-byte 16)) ; Maximal mount count
  (s-magic 0 :type (unsigned-byte 16)) ; Magic signature
  (s-state 0 :type (unsigned-byte 16)) ; File system state
  (s-errors 0 :type (unsigned-byte 16)) ; Behaviour when detecting errors
  (s-minor-rev-level 0 :type (unsigned-byte 16)) ; minor revision level
  (s-lastcheck 0 :type (unsigned-byte 32)) ; time of last check
  (s-checkinterval 0 :type (unsigned-byte 32)) ; max. time between checks
  (s-creator-os 0 :type (unsigned-byte 32)) ; OS
  (s-rev-level 0 :type (unsigned-byte 32)) ; Revision level
  (s-def-resuid 0 :type (unsigned-byte 16)) ; Default uid for reserved blocks
  (s-def-resgid 0 :type (unsigned-byte 16)) ; Default gid for reserved blocks
  ; These fields are for +ext2-dynamic-rev+ superblocks only.
  (s-first-ino 0 :type (unsigned-byte 32)) ; First non-reserved inode
  (s-inode-size 0 :type (unsigned-byte 16)) ; size of inode structure
  (s-block-group-nr 0 :type (unsigned-byte 16)) ; block group # of this superblock
  (s-feature-compat 0 :type (unsigned-byte 32)) ; compatible feature set
  (s-feature-incompat 0 :type (unsigned-byte 32)) ; incompatible feature set
  (s-feature-ro-compat 0 :type (unsigned-byte 32)) ; readonly-compatible feature set
  (s-uuid 0 :type (unsigned-byte 128)) ; 128-bit uuid for volume
  (s-volume-name "" :type (unsigned-byte 128)) ; volume name
  (s-last-mounted "" :type (unsigned-byte 512)) ; directory where last mounted
  (s-algorithm-usage-bitmap 0 :type (unsigned-byte 32)) ; For compression
  ; Performance hints.  Directory preallocation should only
  ; happen if the ext2-compat-prealloc flag is on.
  (s-prealloc-blocks 0 :type (unsigned-byte 8))	; # of blocks to try to preallocate
  (s-prealloc-dir-blocks 0 :type (unsigned-byte 8)) ; # to preallocate for dirs
  (s-padding1 0 :type (unsigned-byte 16))
  (s-reserved 0 :type (ussigned-byte 6528))) ; Padding to the end of the block

;; Structure of a directory entry
(defstruct ext2-dir-entry
  (inode 0 :type (unsigned-byte 32)) ; Inode number
  (rec-len 0 :type (unsigned-byte 16)) ; Directory entry length
  (name-len 0 :type (unsigned-byte 16)) ; Name length
  (name 0 :type (unsigned-byte (* 8 +ext2-name-len+)))) ; File name


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

(defun read-ext2-super-block (hdn sect)
  "Initializes a superblock structure reading data from the specified hard disk and sector"
  (let ((sbdata (hd-read-sectors hdn sect 1)))
    (if (member (little-endian-to-integer sbdata 56 2) +ext2-super-magic+)
	(make-ext2-super-block
	 :s-inodes-count (little-endian-to-integer sbdata 0 4)
	 :s-blocks-count (little-endian-to-integer sbdata 4 4)
	 :s-r-blocks-count (little-endian-to-integer sbdata 8 4)
	 :s-free-blocks-count (little-endian-to-integer sbdata 12 4)
	 :s-free-inodes-count (little-endian-to-integer sbdata 16 4)
	 :s-first-data-block (little-endian-to-integer sbdata 20 4)
	 :s-log-block-size (little-endian-to-integer sbdata 24 4)
	 :s-log-frag-size (little-endian-to-integer sbdata 28 4)
	 :s-blocks-per-group (little-endian-to-integer sbdata 32 4)
	 :s-frags-per-group (little-endian-to-integer sbdata 36 4)
	 :s-inodes-per-group (little-endian-to-integer sbdata 40 4)
	 :s-mtime (little-endian-to-integer sbdata 44 4)
	 :s-wtime (little-endian-to-integer sbdata 48 4)
	 :s-mnt-count (little-endian-to-integer sbdata 52 2)
	 :s-max-mnt-count (little-endian-to-integer sbdata 54 2)
	 :s-magic (little-endian-to-integer sbdata 56 2)
	 :s-state (little-endian-to-integer sbdata 58 2)
	 :s-errors (little-endian-to-integer sbdata 60 2)
	 :s-minor-rev-level (little-endian-to-integer sbdata 62 2)
	 :s-lastcheck (little-endian-to-integer sbdata 64 4)
	 :s-checkinterval (little-endian-to-integer sbdata 68 4)
	 :s-creator-os (little-endian-to-integer sbdata 72 4)
	 :s-rev-level (little-endian-to-integer sbdata 76 4)
	 :s-def-resuid (little-endian-to-integer sbdata 80 2)
	 :s-def-resgid (little-endian-to-integer sbdata 82 2))
	(error "Can't read ext2 superblock -- invalid magic number. Either this is not an ext2 fs, or it is corrupted; in this case, try reading a superblock backup copy"))))

(defun read-group-descriptors (hdn sect howmany)
  "Initializes an array of <howmany> group-descriptor structures reading data from the sector sect of the specified hard disk"
  (let ((data (hd-read-sectors hdn sect howmany))
	(arr (make-array howmany)))
    (loop for i from 0 to (1- howmany)
	  for j = (* 32 i)
	  do (setf (aref arr i)
		   (make-group-descriptor
		    :bg-block-bitmap (little-endian-to-integer data j 4)
		    :bg-inode-bitmap (little-endian-to-integer data (+ j 4) 4)
		    :bg-inode-table (little-endian-to-integer data (+ j 8) 4)
		    :bg-free-blocks-count (little-endian-to-integer data (+ j 12) 2)
		    :bg-free-inodes-count (little-endian-to-integer data (+ j 14) 2)
		    :bg-used-dirs-count (little-endian-to-integer data (+ j 16) 2))))
    arr))

(defun read-inodes (hdn sect howmany)
  "Reads some inodes"
  (let* ((data (hd-read-sectors hdn sect (1+ (truncate (/ (1- howmany) 4)))))
	 (arr (make-array howmany :element-type 'ext2-inode))
	 (blockdata (make-array 15)))
;    (format t "reading ~A inodes from sector ~A~%" howmany sect)
    (dotimes (i howmany)
      (dotimes (j 15)
        (setf (aref blockdata j) (little-endian-to-integer data (+ 40 (* 4 j) (* 128 i)) 4)))
      (setf (aref arr i)
	    (make-inode
	     :type (logand #xf0 (aref data (1+ (* 128 i))))
	     :access_rights (logand #x0fff (little-endian-to-integer data (* 128 i) 2))
	     :i-uid (little-endian-to-integer data (+ 2 (* 128 i)) 2)
	     :i-size (little-endian-to-integer data (+ 4 (* 128 i)) 4)
	     :i-links-count (little-endian-to-integer data (+ 26 (* 128 i)) 2)
	     :i-blocks (little-endian-to-integer data (+ 28 (* 128 i)) 4)
	     :i-flags (little-endian-to-integer data (+ 32 (* 128 i)) 4)
	     :i-block (copy-seq blockdata))))
    arr))


;;;
;;;The "main" function, mount
;;;

(defun mount (hdn part &key (sb-sect 2) (inode-cache-size 15))
  "Returns an ext2-fs instance reading data from the specified hard disk and partition"
  (let* ((pstart (muerte.x86-pc.harddisk::partition-start part))
	 (sb (read-ext2-super-block-hdn (+ pstart sb-sect)))
	 (blocksize (exp2 (1+ (ext2-super-block-log-block-size sb))))
	 (blocksize-bytes (* 512 blocksize))
	 (group-descriptors (read-group-descriptors
			     hdn
			     (+ pstart
				(* blocksize (ext2-super-block-s-first-data-block sb))
				blocksize)
			     (1+ (truncate (/ (ext2-super-block-s-blocks-count sb)
					      (ext2-super-block-s-blocks-per-group sb))))))
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
			(let* ((block-group (truncate (/ num0 (ext2-super-block-s-inodes-per-group sb))))
			       (inode (aref (read-inodes
					     hdn
					     (+ pstart
						(* blocksize
						   (group-descriptor-inode-table
						    (aref group-descriptors block-group)))
						(truncate (/ (- num0 (* block-group (ext2-super-block-s-inodes-per-group sb))) 4)))
					     4)
					    (mod (- num0 (* block-group (ext2-super-block-s-inodes-per-group sb))) 4))))
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
	(print (%path-to-inode "/"))
	(print (%path-to-inode "/."))
	(print (%path-to-inode "/etc/"))

	(format t "Inodes per group: ~A~%" (ext2-super-block-s-inodes-per-group sb))
	(print (%path-to-inode "/etc/fstab"))
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

