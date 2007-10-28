(provide :lib/scheduler)

(in-package muerte.lib)

(defclass process ()
  ((name :initform "Anonymous" :initarg :name :accessor process-name)
   (whostate :initform "Running" :initarg :whostate :accessor process-whostate)
   (rtc :initarg :rtc :reader process-rtc)
   (run-reasons :initform (list :run) :initarg :run-reasons :accessor process-run-reasons)
   (arrest-reasons :initform nil :initarg :arrest-reasons :accessor process-arrest-reasons)
   (blocked-p :initform nil :accessor process-blocked-p)
   (wait-function :initform nil :initarg :wait-function :accessor process-wait-function)
   (wait-argument-list :initform nil :initarg :wait-function-args :accessor process-wait-argument-list)
   (creation-time :initform 0 :reader process-creation-time)
   (last-run-time :initform 0 :accessor process-last-run-time)
   (total-run-time :initform 0 :accessor process-total-run-time)
   (timer :initform nil :accessor process-timer)
   (quantum-remaining :initform 100 :initarg :quantum-remaining :accessor process-quantum-remaining)
   (quantum :initform 100 :initarg :quantum :accessor process-quantum)))

(defvar *all-processes* nil)
(defvar *idle-process* nil)
(defvar *ticks* 0)
(defvar *ticks-per-second* 0)

(defvar *next-timer-event* 0
  "The tick count that the next time event is scheduled to go off.")

;; FIXME: can we call some powersaving no-op instead?
(defun idle-process ()
  (loop))

(defun current-process ()
  (let ((rtc (current-run-time-context)))
    (or (find rtc *all-processes* :key 'process-rtc)
        ;; don't forget the idle process..yuk.
        (and (eq rtc (process-rtc *idle-process*)) *idle-process*))))

(defun %process-wait-p (process &optional
                        (wf (process-wait-function process))
                        (args (process-wait-argument-list process)))
  (or (not (process-wait-function process))
      (apply wf args)))

(defun process-runnable-p (process)
  ;; no arrest reasons, 1 run reason and its wait function must return
  ;; T, if it exists.
  (and 
   (null (process-arrest-reasons process))
   (not (null (process-run-reasons process)))
   (not (process-blocked-p process))
   (%process-wait-p process)))

(defun setup-scheduling ()
  (setf (exception-handler 32) #'timer-interrupt
        *all-processes* nil)
  ;; Set timer 0 frequency to 100Hz (ie. 10ms intervals).
  (setf (muerte.x86-pc:pit8253-timer-count 0) #xffff ; 11932
        *ticks-per-second* 100
        (symbol-function 'sleep)
        (lambda (seconds)
          (check-type seconds (real 0 *))
          (process-block-with-timeout (current-process)
                                      (truncate (* *ticks-per-second* seconds))
                                      "Sleep")))
  (let ((idle (make-instance 'process
                             :name "Idle"
                             :rtc (make-instance 'threading:thread :function #'idle-process :args nil)))
        (repl (make-instance 'process
                             :name "REPL"
                             :rtc (current-run-time-context))))
    ;; the current rtc needs to be added too. it's the repl.
    (push repl *all-processes*)
    (setf *idle-process* idle)
    (write-line "Scheduling Initialized.")))

;; (defun boink (n)
;;   (let ((map (muerte.x86-pc:vga-memory-map)))
;;     (loop 
;;        (loop for i from 0 to 255 do
;;             (setf (memref-int map
;;                               :index (+ (* 80 3) 10)
;;                               :type :unsigned-byte16)
;;                   (logior (ash i 8) i))
;;             (sleep n)))))

(defvar *in-scheduler* nil
  "Set to T when the scheduler is running.")

(defvar *scheduler-function* 'round-robin-scheduler
  "What scheduler function should we use?")

(defun %switch-to-process (process)
  (let ((old (current-process)))
    (if (eq process old)
        (without-interrupts
            (setf *in-scheduler* nil))
        (progn
          ;; FIXME: The cli may not actually be needed
          (muerte::cli)
          (setf (process-quantum-remaining process) (process-quantum process)
                (process-wait-function process) nil
                (process-wait-argument-list process) nil
                (process-whostate process) "Running"
                *in-scheduler* nil)
          (threading:yield (process-rtc process))))))

(defun %wakeup-timer-events ()
  (dolist (i *all-processes*)
    (when (and (process-timer i)
               (<= (process-timer i) *ticks*))
      (setf (process-timer i) nil
            (process-blocked-p i) nil))))

(defun %setup-next-timer-event ()
  (setf *next-timer-event*
        (loop for i in *all-processes*
           when (process-timer i)
           minimize (process-timer i))))

;; TODO: spinning through the lists would be faster if there were
;; lists of active, blocked, etc processes.
(defun round-robin-scheduler ()
  ;; timer events
  (%wakeup-timer-events)
  (%setup-next-timer-event)
  ;; select a new process. The one with the most quantum
  ;; remaining is picked.
  (multiple-value-bind (newproc quantum)
      (loop 
         for i in *all-processes*
         with proc = nil
         with max = -1 do
         (when (and (process-runnable-p i)
                    (> (process-quantum-remaining i) max))
           (setf proc i
                 max (process-quantum-remaining i)))
         finally (return (values proc max)))
    ;; is it time for a fresh a fresh quantum? The idea here is
    ;; to give priority to io bound processes by giving them a
    ;; bigger quantum they'll respond better when io comes in.
    (when (= quantum 0)
      (dolist (i *all-processes*)
        (setf (process-quantum-remaining i)
              (+ (/ (process-quantum-remaining i) 2)
                 (process-quantum i)))))
    ;; Use the idle process if no other process is runnable
    (%switch-to-process (or newproc *idle-process*))))

(defun scheduler ()
  (muerte::cli)
  (unless *in-scheduler*
    (setf *in-scheduler* t)
    (muerte::sti)
    (funcall (or *scheduler-function*
                 'round-robin-scheduler))))

(defun timer-interrupt (vector exception-frame)
  "Some really simple scheduling."
  (declare (ignore vector exception-frame))
  (incf *ticks*)
  (incf (process-total-run-time (current-process)))
  (decf (process-quantum-remaining (current-process)))
  (cond ((or (eq (current-process) *idle-process*)
             (<= (process-quantum-remaining (current-process)) 0))
         (setf (process-quantum-remaining (current-process)) 0)
         (muerte.x86-pc:pic8259-end-of-interrupt 0)
         (scheduler))
        ((<= *next-timer-event* *ticks*)
         (muerte.x86-pc:pic8259-end-of-interrupt 0)
         (scheduler))
        (t
         (muerte.x86-pc:pic8259-end-of-interrupt 0))))

(defun process-run-function (name-or-kwds fn &rest args)
  (let ((newproc (if (listp name-or-kwds)
                     (apply 'make-instance 'process
                            :rtc (make-instance 'threading:thread :function fn :args args)
                            name-or-kwds)
                     (make-instance 'process
                                    :rtc (make-instance 'threading:thread :function fn :args args)
                                    :name name-or-kwds
                                    :run-reasons (list :run)))))
    (without-interrupts
        (push newproc *all-processes*))
    newproc))

(defun process-wait (whostate wf &rest args)
  (unless (apply wf args)
    (without-interrupts
        (setf (process-whostate (current-process)) whostate
              (process-wait-function (current-process)) wf
              (process-wait-argument-list (current-process)) args))
    (scheduler)))

(defun process-wait-with-timeout (whostate time function &rest args)
  "TIME is in 10ms ticks."
  (if (null time)
      (apply 'process-wait whostate function args)
      (let* ((f #'(lambda ()
                    (let ((val (apply function args)))
                      (when val
                        (process-unblock
                        val))))))
        (process-wait whostate f))))

(defun process-enable (p)
  (check-type p process)
  (without-interrupts
      (setf (process-run-reasons p) (list :enable)
            (process-arrest-reasons p) nil
            (process-whostate p) "Enabled")))

(defun process-disable (p)
  (check-type p process)
  (without-interrupts
      (setf (process-run-reasons p) nil
            (process-arrest-reasons p) nil
            (process-whostate p) "Disabled")))

(defun process-enable-run-reason (p &optional (reason :user))
  (check-type p process)
  (without-interrupts
      (pushnew reason (process-run-reasons p)))
  (when (eq p (current-process))
    (scheduler)))

(defun process-disable-run-reason (p &optional (reason :user))
  (check-type p process)
  (without-interrupts
      (setf (process-run-reasons p) (remove reason (process-run-reasons p))))
  (when (eq p (current-process))
    (scheduler)))

(defun process-enable-arrest-reason (p &optional (reason :user))
  (check-type p process)
  (without-interrupts
      (pushnew reason (process-arrest-reasons p)))
  (when (eq p (current-process))
    (scheduler)))

(defun process-disable-arrest-reason (p &optional (reason :user))
  (check-type p process)
  (without-interrupts
      (setf (process-arrest-reasons p) (remove reason (process-arrest-reasons p))))
  (when (eq p (current-process))
    (scheduler)))

(defun clear-process-run-time (p)
  (check-type p process)
  (setf (process-total-run-time p) 0))

(defun process-kill (p)
  (check-type p process)
  (when (eq p *idle-process*)
    (error "Can't kill idle process"))
  (without-interrupts
      (setf *all-processes* (remove p *all-processes*)))
  (when (eq (current-process) p)
    (scheduler)))

(defun process-block-with-timeout (p time whostate)
  (check-type p process)
  (check-type time (real 0 *))
  (without-interrupts
      (let ((timer (and time (+ time *ticks*))))
        (setf (process-blocked-p p) t
              (process-timer p) timer
              (process-whostate p) whostate)
        ;; update the next timer event.
        (when (and timer
                   (< timer *next-timer-event*))
          (setf *next-timer-event* timer))
        (%setup-next-timer-event)))
  (when (eq (current-process) p)
    (scheduler)))

(defun process-block (p whostate)
  (process-block-with-timeout p nil whostate))

(defun process-unblock (p)
  (check-type p process)
  (without-interrupts
      (setf (process-blocked-p p) nil
            (process-timer p) nil
            (process-whostate p) "Unblocked"))
  (when (eq (current-process) p)
    (scheduler)))
