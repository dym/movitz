;;;; $Id: partitions.lisp,v 1.1 2004/08/19 00:28:56 ffjeld Exp $

(require :tmp/harddisk)

(provide :tmp/partitions)

(in-package muerte.x86-pc.harddisk)

(defstruct partition
  bootable
  start-cylinder
  start-head
  start-sector
  type
  end-cylinder
  end-head
  end-sector
  start
  size)

(defun read-partition-table (hdn &optional (sect 0))
  "Reads the partition table of hard disk hdn, assuming it is located at sector sect; returns an array of the partitions found (doesn't support extended partitions yet)"
  (let ((data (hd-read-sectors hdn sect 1))
	(arr (make-array 4 :initial-element nil)))
    (if (and (= (aref data 510) #x55) (= (aref data 511) #xAA))
	(dotimes (i 4)
	  (let* ((addr (+ 446 (* i 16)))
		 (start (+ (aref data (+ addr 8))
			   (* #x100 (aref data (+ addr 9)))
			   (* #x10000 (aref data (+ addr 10)))
			   (* #x1000000 (aref data (+ addr 11)))))
		 (size (+ (aref data (+ addr 12))
			  (* #x100 (aref data (+ addr 13)))
			  (* #x10000 (aref data (+ addr 14)))
			  (* #x1000000 (aref data (+ addr 15))))))
	    (when (> size 0)
	      (setf (aref arr i)
		    (make-partition
		     :bootable (aref data addr)
		     :type     (aref data (+ addr 4))
		     :start    start
		     :size     size)))))
	(error "Invalid partition table in hd ~D, sector ~D!" hdn sect))
    arr))
