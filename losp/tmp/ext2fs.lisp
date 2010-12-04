;;;Ext2 fs package -- Copyright (C) 2004 Alessio Stalla
;;;                                 2010 Dmitriy Budashny
;
; Block structure:
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
(defconstant +EXT2_BAD_INO+ 1) ; Bad blocks inode
(defconstant +EXT2_ROOT_INO+ 2)	; Root inode
(defconstant +EXT2_ACL_IDX_INO+ 3) ; ACL inode
(defconstant +EXT2_ACL_DATA_INO+ 4) ; ACL inode
(defconstant +EXT2_BOOT_LOADER_INO+ 5) ; Boot loader inode
(defconstant +EXT2_UNDEL_DIR_INO+ 6) ; Undelete directory inode
; First non-reserved inode for old ext2 filesystems
(defconstant +EXT2_GOOD_OLD_FIRST_INO+ 11)

; The second extended file system magic number
(defconstant +EXT2_SUPER_MAGIC+ '(#xEF53))

; Maximal count of links to a file
(defconstant +EXT2_LINK_MAX+ 32000)

;;; Block sizes
(defconstant +EXT2_MIN_BLOCK_SIZE+ 1024)
(defconstant +EXT2_MAX_BLOCK_SIZE+ 4096)
(defconstant +EXT2_MIN_BLOCK_LOG_SIZE+ 10)
; TODO: put here all that calculations from ext2_fs.h

;;; Fragments
(defconstant +EXT2_MIN_FRAG_SIZE+ 1024)
(defconstant +EXT2_MAX_FRAG_SIZE+ 4096)
(defconstant +EXT2_MIN_FRAG_LOG_SIZE+ 10)
; TODO: put here all that calculations from ext2_fs.h

;;; Constants relative to the data blocks
(defconstant +EXT2_NDIR_BLOCKS+ 12)
(defconstant +EXT2_IND_BLOCK+ +EXT2_NDIR_BLOCKS+)
(defconstant +EXT2_DIND_BLOCK+ (+ +EXT2_IND_BLOCK+ 1))
(defconstant +EXT2_TIND_BLOCK+ (+ +EXT2_DIND_BLOCK+ 1))
(defconstant +EXT2_N_BLOCKS+ (+ +EXT2_TIND_BLOCK+ 1))

;;; Inode flags
(defconstant +EXT2_SECRM_FL+ #x00000001) ; Secure deletion
(defconstant +EXT2_UNRM_FL+ #x00000002) ; Undelete
(defconstant +EXT2_COMPR_FL+ #x00000004) ; Compress file
(defconstant +EXT2_SYNC_FL+ #x00000008) ; Synchronous updates
(defconstant +EXT2_IMMUTABLE_FL+ #x00000010) ; Immutable file
(defconstant +EXT2_APPEND_FL+ #x00000020) ; writes to file may only append
(defconstant +EXT2_NODUMP_FL+ #x00000040) ; do not dump file
(defconstant +EXT2_NOATIME_FL+ #x00000080) ; do not update atime
;; Reserved for compression usage...
(defconstant +EXT2_DIRTY_FL+ #x00000100)
(defconstant +EXT2_COMPRBLK_FL+ #x00000200) ; One or more compressed clusters
(defconstant +EXT2_NOCOMP_FL+ #x00000400) ; Don't compress
(defconstant +EXT2_ECOMPR_FL+ #x00000800) ; Compression error
;; End compression flags --- maybe not all used
(defconstant +EXT2_BTREE_FL+ #x00001000) ; btree format dir
(defconstant +EXT2_RESERVED_FL+ #x80000000) ; reserved for ext2 lib
(defconstant +EXT2_FL_USER_VISIBLE+ #x00001FFF) ; User visible flags
(defconstant +EXT2_FL_USER_MODIFIABLE+ #x000000FF) ; User modifiable flags

;; File system states
(defconstant +EXT2_VALID_FS+ #x0001) ; Unmounted cleanly
(defconstant +EXT2_ERROR_FS+ #x0002) ; Errors detected

;; Mount flags
(defconstant +EXT2_MOUNT_CHECK_NORMAL+ #x0001) ; Do some more checks
(defconstant +EXT2_MOUNT_CHECK_STRICT+ #x0002) ; Do again more checks
(defconstant +EXT2_MOUNT_CHECK+
  (boole boole-ior +EXT2_MOUNT_CHECK_NORMAL+ +EXT2_MOUNT_CHECK_STRICT+))
(defconstant +EXT2_MOUNT_GRPID+	#x0004)	; Create files with directory's group
(defconstant +EXT2_MOUNT_DEBUG+ #x0008)	; Some debugging messages
(defconstant +EXT2_MOUNT_ERRORS_CONT+ #x0010) ; Continue on errors
(defconstant +EXT2_MOUNT_ERRORS_RO+ #x0020) ; Remount fs ro on errors
(defconstant +EXT2_MOUNT_ERRORS_PANIC+ #x0040) ; Panic on errors
(defconstant +EXT2_MOUNT_MINIX_DF+ #x0080) ; Mimics the Minix statfs

;; Maximal mount counts between two filesystem checks
(defconstant +EXT2_DFL_MAX_MNT_COUNT+ 20) ; Allow 20 mounts
(defconstant +EXT2_DFL_CHECKINTERVAL+ 0) ; Don't use interval check

;; Behaviour when detecting errors
(defconstant +EXT2_ERRORS_CONTINUE+ 1) ; Continue execution
(defconstant +EXT2_ERRORS_RO+ 2) ; Remount fs read-only
(defconstant +EXT2_ERRORS_PANIC+ 3) ; Panic
(defconstant +EXT2_ERRORS_DEFAULT+ +EXT2_ERRORS_CONTINUE+)

;; Codes for operating systems
(defconstant +EXT2_OS_LINUX+ 0)
(defconstant +EXT2_OS_HURD+ 1)
(defconstant +EXT2_OS_MASIX+ 2)
(defconstant +EXT2_OS_FREEBSD+ 3)
(defconstant +EXT2_OS_LITES+ 4)

;; Revision levels
(defconstant +EXT2_GOOD_OLD_REV+ 0) ; The good old (original) format
(defconstant +EXT2_DYNAMIC_REV+ 1) ; V2 format w/ dynamic inode sizes
(defconstant +EXT2_CURRENT_REV+	+EXT2_GOOD_OLD_REV+)
(defconstant +EXT2_MAX_SUPP_REV+ +EXT2_DYNAMIC_REV+)
(defconstant +EXT2_GOOD_OLD_INODE_SIZE+ 128)

;;; Feature set definitions
;; s_feature_compat
(defconstant +EXT2_FEATURE_COMPAT_DIR_PREALLOC+ #x0001)

;; s_feature_incompat
(defconstant +EXT2_FEATURE_INCOMPAT_COMPRESSION+ #x0001)
(defconstant +EXT2_FEATURE_INCOMPAT_FILETYPE+ #x0002)

;; s_feature_ro_compat
; Doesn't store superblock in every block group but just in some
(defconstant +EXT2_FEATURE_RO_COMPAT_SPARSE_SUPER+ #x0001)
(defconstant +EXT2_FEATURE_RO_COMPAT_LARGE_FILE+ #x0002)
(defconstant +EXT2_FEATURE_RO_COMPAT_BTREE_DIR+	#x0004)

(defconstant +EXT2_FEATURE_COMPAT_SUPP+ 0)
(defconstant +EXT2_FEATURE_INCOMPAT_SUPP+ +EXT2_FEATURE_INCOMPAT_FILETYPE+)
(defconstant +EXT2_FEATURE_RO_COMPAT_SUPP+ +EXT2_FEATURE_RO_COMPAT_SPARSE_SUPER+)

;; Default values for user and/or group using reserved blocks
(defconstant +EXT2_DEF_RESUID+ 0)
(defconstant +EXT2_DEF_RESGID+ 0)

;; Directory entry
(defconstant +EXT2_NAME_LEN+ 255)

;; Ext2 directory file types.  Only the low 3 bits are used.  The
;; other bits are reserved for now.
(defconstant +EXT2_FT_UNKNOWN+ 0)
(defconstant +EXT2_FT_REG_FILE+	1)
(defconstant +EXT2_FT_DIR+ 2)
(defconstant +EXT2_FT_CHRDEV+ 3)
(defconstant +EXT2_FT_BLKDEV+ 4)
(defconstant +EXT2_FT_FIFO+ 5)
(defconstant +EXT2_FT_SOCK+ 6)
(defconstant +EXT2_FT_SYMLINK+ 7)
(defconstant +EXT2_FT_MAX+ 8)


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
(defstruct ext2_acl_header
  (aclh_size 0 :type (unsigned-byte 32))
  (aclh_file_count 0 :type (unsigned-byte 32))
  (aclh_acle_count 0 :type (unsigned-byte 32))
  (aclh_first_acle 0 :type (unsigned-byte 32)))

; Access Control List Entry */
(defstruct ext2_acl_entry
  (acle_size 0 :type (unsigned-byte 32))
  (acle_perms 0 :type (unsigned-byte 16)) ; Access permissions
  (acle_type 0 :type (unsigned-byte 16)) ; Type of entry
  (acle_tag 0 :type (unsigned-byte 16))	; User or group identity
  (acle_pad1 0 :type (unsigned-byte 16))
  (acle_next 0 :type (unsigned-byte 32))) ; Pointer on next entry for the same inode or on next free entry

;; Structure of a blocks group descriptor
(defstruct ext2_group_desc
  (bg_block_bitmap 0 :type (unsigned-byte 32)) ; Blocks bitmap block
  (bg_inode_bitmap 0 :type (unsigned-byte 32)) ; Inodes bitmap block
  (bg_inode_table 0 :type (unsigned-byte 32)) ; Inodes table block
  (bg_free_blocks_count 0 :type (unsigned-byte 16)) ; Free blocks count
  (bg_free_inodes_count 0 :type (unsigned-byte 16)) ; Free inodes count
  (bg_used_dirs_count 0 :type (unsigned-byte 16)) ; Directories count
  (bg_pad 0 :type (unsigned-byte 16))
  (bg_reserved 0 :type (unsigned-byte 96))

;; Structure of an inode on the disk
(defstruct ext2_inode
  (i_mode 0 :type (unsigned-byte 16)) ; File mode
  (i_uid 0 :type (unsigned-byte 16)) ; Owner Uid
  (i_size 0 :type (unsigned-byte 32)) ; Size in bytes
  (i_atime 0 :type (unsigned-byte 32)) ; Access time
  (i_ctime 0 :type (unsigned-byte 32)) ; Creation time
  (i_mtime 0 :type (unsigned-byte 32)) ; Modification time
  (i_dtime 0 :type (unsigned-byte 32)) ; Deletion Time
  (i_gid 0 :type (unsigned-byte 16)) ; Group Id
  (i_links_count 0 :type (unsigned-byte 16)) ; Links count
  (i_blocks 0 :type (unsigned-byte 32)) ; Blocks count
  (i_flags 0 :type (unsigned-byte 32)) ; File flags
  (osd1 0 :type (unsigned-byte 32)) ; OS dependent 1
  (i_block :type (unsigned-byte (* 32 +EXT2_N_BLOCKS+))) ; Pointers to blocks
  (i_generation 0 :type (unsigned-byte 32)) ; File version (for NFS)
  (i_file_acl 0 :type (unsigned-byte 32)) ; File ACL
  (i_dir_acl 0 :type (unsigned-byte 32)) ; Directory ACL
  (i_faddr 0 :type (unsigned-byte 32)) ; Fragment address
  (osd2 0 :type (unsigned-byte 96))) ; OS dependent 2



;; Structure of the super block
(defstruct ext2_super_block
  (s_inodes_count 0 :type (unsigned-byte 32)) ; Inodes count
  (s_blocks_count 0 :type (unsigned-byte 32)) ; Blocks count
  (s_r_blocks_count 0 :type (unsigned-byte 32)) ; Reserved blocks count
  (s_free_blocks_count 0 :type (unsigned-byte 32)) ; Free blocks count
  (s_free_inodes_count 0 :type (unsigned-byte 32)) ; Free inodes count
  (s_first_data_block 0 :type (unsigned-byte 32)) ; First Data Block
  (s_log_block_size 0 :type (unsigned-byte 32)) ; Block size
  (s_log_frag_size 0 :type (unsigned-byte 32)) ; Fragment size
  (s_blocks_per_group 0 :type (unsigned-byte 32)) ; # Blocks per group
  (s_frags_per_group 0 :type (unsigned-byte 32)) ; # Fragments per group
  (s_inodes_per_group 0 :type (unsigned-byte 32)) ; # Inodes per group
  (s_mtime 0 :type (unsigned-byte 32)) ; Mount time
  (s_wtime 0 :type (unsigned-byte 32)) ; Write time
  (s_mnt_count 0 :type (unsigned-byte 16)) ; Mount count
  (s_max_mnt_count 0 :type (unsigned-byte 16)) ; Maximal mount count
  (s_magic 0 :type (unsigned-byte 16)) ; Magic signature
  (s_state 0 :type (unsigned-byte 16)) ; File system state
  (s_errors 0 :type (unsigned-byte 16)) ; Behaviour when detecting errors
  (s_minor_rev_level 0 :type (unsigned-byte 16)) ; minor revision level
  (s_lastcheck 0 :type (unsigned-byte 32)) ; time of last check
  (s_checkinterval 0 :type (unsigned-byte 32)) ; max. time between checks
  (s_creator_os 0 :type (unsigned-byte 32)) ; OS
  (s_rev_level 0 :type (unsigned-byte 32)) ; Revision level
  (s_def_resuid 0 :type (unsigned-byte 16)) ; Default uid for reserved blocks
  (s_def_resgid 0 :type (unsigned-byte 16)) ; Default gid for reserved blocks
  ; These fields are for EXT2_DYNAMIC_REV superblocks only.
  (s_first_ino 0 :type (unsigned-byte 32)) ; First non-reserved inode
  (s_inode_size 0 :type (unsigned-byte 16)) ; size of inode structure
  (s_block_group_nr 0 :type (unsigned-byte 16)) ; block group # of this superblock
  (s_feature_compat 0 :type (unsigned-byte 32)) ; compatible feature set
  (s_feature_incompat 0 :type (unsigned-byte 32)) ; incompatible feature set
  (s_feature_ro_compat 0 :type (unsigned-byte 32)) ; readonly-compatible feature set
  (s_uuid 0 :type (unsigned-byte 128)) ; 128-bit uuid for volume
  (s_volume_name "" :type (unsigned-byte 128)) ; volume name
  (s_last_mounted "" :type (unsigned-byte 512)) ; directory where last mounted
  (s_algorithm_usage_bitmap 0 :type (unsigned-byte 32)) ; For compression
  ; Performance hints.  Directory preallocation should only
  ; happen if the EXT2_COMPAT_PREALLOC flag is on.
  (s_prealloc_blocks 0 :type (unsigned-byte 8))	; # of blocks to try to preallocate
  (s_prealloc_dir_blocks 0 :type (unsigned-byte 8)) ; # to preallocate for dirs
  (s_padding1 0 :type (unsigned-byte 16))
  (s_reserved 0 :type (ussigned-byte 6528))) ; Padding to the end of the block

;; Structure of a directory entry
(defstruct ext2_dir_entry
  (inode 0 :type (unsigned-byte 32)) ; Inode number
  (rec_len 0 :type (unsigned-byte 16)) ; Directory entry length
  (name_len 0 :type (unsigned-byte 16)) ; Name length
  (name 0 :type (unsigned-byte (* 8 +EXT2_NAME_LEN+)))) ; File name


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

(defun read-ext2_super_block (hdn sect)
  "Initializes a superblock structure reading data from the specified hard disk and sector"
  (let ((sbdata (hd-read-sectors hdn sect 1)))
    (if (member (little-endian-to-integer sbdata 56 2) +EXT2_SUPER_MAGIC+)
	(make-ext2_super_block
	 :s_inodes_count (little-endian-to-integer sbdata 0 4)
	 :s_blocks_count (little-endian-to-integer sbdata 4 4)
	 :s_r_blocks_count (little-endian-to-integer sbdata 8 4)
	 :s_free_blocks_count (little-endian-to-integer sbdata 12 4)
	 :s_free_inodes_count (little-endian-to-integer sbdata 16 4)
	 :s_first_data_block (little-endian-to-integer sbdata 20 4)
	 :s_log_block_size (little-endian-to-integer sbdata 24 4)
	 :s_log_frag_size (little-endian-to-integer sbdata 28 4)
	 :s_blocks_per_group (little-endian-to-integer sbdata 32 4)
	 :s_frags_per_group (little-endian-to-integer sbdata 36 4)
	 :s_inodes_per_group (little-endian-to-integer sbdata 40 4)
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
	 (arr (make-array howmany :element-type 'ext2_inode))
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
	 (sb (read-ext2_super_block hdn (+ pstart sb-sect)))
	 (blocksize (exp2 (1+ (ext2_super_block-log_block_size sb))))
	 (blocksize-bytes (* 512 blocksize))
	 (group-descriptors (read-group-descriptors
			     hdn
			     (+ pstart
				(* blocksize (ext2_super_block-first_data_block sb))
				blocksize)
			     (1+ (truncate (/ (ext2_super_block-blocks_count sb)
					      (ext2_super_block-blocks_per_group sb))))))
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
			(let* ((block-group (truncate (/ num0 (ext_super_block-inodes_per_group sb))))
			       (inode (aref (read-inodes
					     hdn
					     (+ pstart
						(* blocksize
						   (group-descriptor-inode-table
						    (aref group-descriptors block-group)))
						(truncate (/ (- num0 (* block-group (ext2_super_block-inodes_per_group sb))) 4)))
					     4)
					    (mod (- num0 (* block-group (ext2_super_block-inodes_per_group sb))) 4))))
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

