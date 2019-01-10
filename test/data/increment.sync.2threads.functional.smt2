(set-logic QF_AUFBV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; initial state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_0_1 () (_ BitVec 16))
(declare-fun accu_0_2 () (_ BitVec 16))

(assert (= accu_0_1 #x0000))
(assert (= accu_0_2 #x0000))

; mem states - mem_<step>_<thread>
(declare-fun mem_0_1 () (_ BitVec 16))
(declare-fun mem_0_2 () (_ BitVec 16))

(assert (= mem_0_1 #x0000))
(assert (= mem_0_2 #x0000))

; heap states - heap_<step>
(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_1_0 () Bool)
(declare-fun stmt_1_1_1 () Bool)
(declare-fun stmt_1_1_2 () Bool)
(declare-fun stmt_1_1_3 () Bool)
(declare-fun stmt_1_1_4 () Bool)
(declare-fun stmt_1_1_5 () Bool)
(declare-fun stmt_1_1_6 () Bool)
(declare-fun stmt_1_1_7 () Bool)

(declare-fun stmt_1_2_0 () Bool)
(declare-fun stmt_1_2_1 () Bool)
(declare-fun stmt_1_2_2 () Bool)
(declare-fun stmt_1_2_3 () Bool)
(declare-fun stmt_1_2_4 () Bool)
(declare-fun stmt_1_2_5 () Bool)
(declare-fun stmt_1_2_6 () Bool)

; initial statement activation
(assert stmt_1_1_0)
(assert (not stmt_1_1_1))
(assert (not stmt_1_1_2))
(assert (not stmt_1_1_3))
(assert (not stmt_1_1_4))
(assert (not stmt_1_1_5))
(assert (not stmt_1_1_6))
(assert (not stmt_1_1_7))

(assert stmt_1_2_0)
(assert (not stmt_1_2_1))
(assert (not stmt_1_2_2))
(assert (not stmt_1_2_3))
(assert (not stmt_1_2_4))
(assert (not stmt_1_2_5))
(assert (not stmt_1_2_6))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_1 () Bool)
(declare-fun thread_1_2 () Bool)

(assert (or thread_1_1 thread_1_2))
(assert (or (not thread_1_1) (not thread_1_2)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_1_0 () Bool)
(declare-fun sync_1_1 () Bool)

; all threads synchronized?
(assert (= sync_1_0 (and stmt_1_1_1 stmt_1_2_0 (or thread_1_1 thread_1_2))))
(assert (= sync_1_1 (and stmt_1_1_5 stmt_1_2_1 (or thread_1_1 thread_1_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_1_1_1 (not sync_1_0)) (not thread_1_1))) ; barrier 0: thread 1
(assert (=> (and stmt_1_2_0 (not sync_1_0)) (not thread_1_2))) ; barrier 0: thread 2
(assert (=> (and stmt_1_1_5 (not sync_1_1)) (not thread_1_1))) ; barrier 1: thread 1
(assert (=> (and stmt_1_2_1 (not sync_1_1)) (not thread_1_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_1_0 () Bool)
(declare-fun exec_1_1_1 () Bool)
(declare-fun exec_1_1_2 () Bool)
(declare-fun exec_1_1_3 () Bool)
(declare-fun exec_1_1_4 () Bool)
(declare-fun exec_1_1_5 () Bool)
(declare-fun exec_1_1_6 () Bool)
(declare-fun exec_1_1_7 () Bool)

(declare-fun exec_1_2_0 () Bool)
(declare-fun exec_1_2_1 () Bool)
(declare-fun exec_1_2_2 () Bool)
(declare-fun exec_1_2_3 () Bool)
(declare-fun exec_1_2_4 () Bool)
(declare-fun exec_1_2_5 () Bool)
(declare-fun exec_1_2_6 () Bool)

(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))
(assert (= exec_1_1_1 (and stmt_1_1_1 sync_1_0)))
(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))
(assert (= exec_1_1_3 (and stmt_1_1_3 thread_1_1)))
(assert (= exec_1_1_4 (and stmt_1_1_4 thread_1_1)))
(assert (= exec_1_1_5 (and stmt_1_1_5 sync_1_1)))
(assert (= exec_1_1_6 (and stmt_1_1_6 thread_1_1)))
(assert (= exec_1_1_7 (and stmt_1_1_7 thread_1_1)))

(assert (= exec_1_2_0 (and stmt_1_2_0 sync_1_0)))
(assert (= exec_1_2_1 (and stmt_1_2_1 sync_1_1)))
(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))
(assert (= exec_1_2_3 (and stmt_1_2_3 thread_1_2)))
(assert (= exec_1_2_4 (and stmt_1_2_4 thread_1_2)))
(assert (= exec_1_2_5 (and stmt_1_2_5 thread_1_2)))
(assert (= exec_1_2_6 (and stmt_1_2_6 thread_1_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_1_1 () (_ BitVec 16))
(declare-fun accu_1_2 () (_ BitVec 16))

(assert (= accu_1_1 (ite exec_1_1_2 (select heap_0 #x0000) (ite exec_1_1_3 (bvadd accu_0_1 #x0001) accu_0_1))))
(assert (= accu_1_2 (ite exec_1_2_2 (select heap_0 #x0000) (ite exec_1_2_3 (bvadd accu_0_2 #x0001) accu_0_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_1_1 () (_ BitVec 16))
(declare-fun mem_1_2 () (_ BitVec 16))

(assert (= mem_1_1 mem_0_1))
(assert (= mem_1_2 mem_0_2))

; heap states - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_1 (ite exec_1_1_0 (store heap_0 #x0000 accu_0_1) (ite exec_1_1_4 (store heap_0 #x0000 accu_0_1) (ite exec_1_2_4 (store heap_0 #x0000 accu_0_2) heap_0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_2 () Bool)

(assert (= exit_2 (or exec_1_1_7 exec_1_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_1_0 () Bool)
(declare-fun stmt_2_1_1 () Bool)
(declare-fun stmt_2_1_2 () Bool)
(declare-fun stmt_2_1_3 () Bool)
(declare-fun stmt_2_1_4 () Bool)
(declare-fun stmt_2_1_5 () Bool)
(declare-fun stmt_2_1_6 () Bool)
(declare-fun stmt_2_1_7 () Bool)

(declare-fun stmt_2_2_0 () Bool)
(declare-fun stmt_2_2_1 () Bool)
(declare-fun stmt_2_2_2 () Bool)
(declare-fun stmt_2_2_3 () Bool)
(declare-fun stmt_2_2_4 () Bool)
(declare-fun stmt_2_2_5 () Bool)
(declare-fun stmt_2_2_6 () Bool)

(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))
(assert (= stmt_2_1_1 (ite stmt_1_1_6 (and exec_1_1_6 (not (= accu_1_1 #x0000))) (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1))))))
(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))
(assert (= stmt_2_1_3 (ite stmt_1_1_2 exec_1_1_2 (and stmt_1_1_3 (not exec_1_1_3)))))
(assert (= stmt_2_1_4 (ite stmt_1_1_3 exec_1_1_3 (and stmt_1_1_4 (not exec_1_1_4)))))
(assert (= stmt_2_1_5 (ite stmt_1_1_4 exec_1_1_4 (and stmt_1_1_5 (not exec_1_1_5)))))
(assert (= stmt_2_1_6 (ite stmt_1_1_5 exec_1_1_5 (and stmt_1_1_6 (not exec_1_1_6)))))
(assert (= stmt_2_1_7 (ite stmt_1_1_6 (and exec_1_1_6 (not (not (= accu_1_1 #x0000)))) (and stmt_1_1_7 (not exec_1_1_7)))))

(assert (= stmt_2_2_0 (ite stmt_1_2_5 (and exec_1_2_5 (not (= accu_1_2 #x0000))) (and stmt_1_2_0 (not exec_1_2_0)))))
(assert (= stmt_2_2_1 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))
(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))
(assert (= stmt_2_2_3 (ite stmt_1_2_2 exec_1_2_2 (and stmt_1_2_3 (not exec_1_2_3)))))
(assert (= stmt_2_2_4 (ite stmt_1_2_3 exec_1_2_3 (and stmt_1_2_4 (not exec_1_2_4)))))
(assert (= stmt_2_2_5 (ite stmt_1_2_4 exec_1_2_4 (and stmt_1_2_5 (not exec_1_2_5)))))
(assert (= stmt_2_2_6 (ite stmt_1_2_5 (and exec_1_2_5 (not (not (= accu_1_2 #x0000)))) (and stmt_1_2_6 (not exec_1_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_1 () Bool)
(declare-fun thread_2_2 () Bool)

(assert (or thread_2_1 thread_2_2 exit_2))
(assert (or (not thread_2_1) (not thread_2_2)))
(assert (or (not thread_2_1) (not exit_2)))
(assert (or (not thread_2_2) (not exit_2)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_2_0 () Bool)
(declare-fun sync_2_1 () Bool)

; all threads synchronized?
(assert (= sync_2_0 (and stmt_2_1_1 stmt_2_2_0 (or thread_2_1 thread_2_2))))
(assert (= sync_2_1 (and stmt_2_1_5 stmt_2_2_1 (or thread_2_1 thread_2_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_2_1_1 (not sync_2_0)) (not thread_2_1))) ; barrier 0: thread 1
(assert (=> (and stmt_2_2_0 (not sync_2_0)) (not thread_2_2))) ; barrier 0: thread 2
(assert (=> (and stmt_2_1_5 (not sync_2_1)) (not thread_2_1))) ; barrier 1: thread 1
(assert (=> (and stmt_2_2_1 (not sync_2_1)) (not thread_2_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_1_0 () Bool)
(declare-fun exec_2_1_1 () Bool)
(declare-fun exec_2_1_2 () Bool)
(declare-fun exec_2_1_3 () Bool)
(declare-fun exec_2_1_4 () Bool)
(declare-fun exec_2_1_5 () Bool)
(declare-fun exec_2_1_6 () Bool)
(declare-fun exec_2_1_7 () Bool)

(declare-fun exec_2_2_0 () Bool)
(declare-fun exec_2_2_1 () Bool)
(declare-fun exec_2_2_2 () Bool)
(declare-fun exec_2_2_3 () Bool)
(declare-fun exec_2_2_4 () Bool)
(declare-fun exec_2_2_5 () Bool)
(declare-fun exec_2_2_6 () Bool)

(assert (= exec_2_1_0 (and stmt_2_1_0 thread_2_1)))
(assert (= exec_2_1_1 (and stmt_2_1_1 sync_2_0)))
(assert (= exec_2_1_2 (and stmt_2_1_2 thread_2_1)))
(assert (= exec_2_1_3 (and stmt_2_1_3 thread_2_1)))
(assert (= exec_2_1_4 (and stmt_2_1_4 thread_2_1)))
(assert (= exec_2_1_5 (and stmt_2_1_5 sync_2_1)))
(assert (= exec_2_1_6 (and stmt_2_1_6 thread_2_1)))
(assert (= exec_2_1_7 (and stmt_2_1_7 thread_2_1)))

(assert (= exec_2_2_0 (and stmt_2_2_0 sync_2_0)))
(assert (= exec_2_2_1 (and stmt_2_2_1 sync_2_1)))
(assert (= exec_2_2_2 (and stmt_2_2_2 thread_2_2)))
(assert (= exec_2_2_3 (and stmt_2_2_3 thread_2_2)))
(assert (= exec_2_2_4 (and stmt_2_2_4 thread_2_2)))
(assert (= exec_2_2_5 (and stmt_2_2_5 thread_2_2)))
(assert (= exec_2_2_6 (and stmt_2_2_6 thread_2_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_2_1 () (_ BitVec 16))
(declare-fun accu_2_2 () (_ BitVec 16))

(assert (= accu_2_1 (ite exec_2_1_2 (select heap_1 #x0000) (ite exec_2_1_3 (bvadd accu_1_1 #x0001) accu_1_1))))
(assert (= accu_2_2 (ite exec_2_2_2 (select heap_1 #x0000) (ite exec_2_2_3 (bvadd accu_1_2 #x0001) accu_1_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_2_1 () (_ BitVec 16))
(declare-fun mem_2_2 () (_ BitVec 16))

(assert (= mem_2_1 mem_1_1))
(assert (= mem_2_2 mem_1_2))

; heap states - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_2 (ite exec_2_1_0 (store heap_1 #x0000 accu_1_1) (ite exec_2_1_4 (store heap_1 #x0000 accu_1_1) (ite exec_2_2_4 (store heap_1 #x0000 accu_1_2) heap_1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_3 () Bool)

(assert (= exit_3 (or exit_2 exec_2_1_7 exec_2_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_1_0 () Bool)
(declare-fun stmt_3_1_1 () Bool)
(declare-fun stmt_3_1_2 () Bool)
(declare-fun stmt_3_1_3 () Bool)
(declare-fun stmt_3_1_4 () Bool)
(declare-fun stmt_3_1_5 () Bool)
(declare-fun stmt_3_1_6 () Bool)
(declare-fun stmt_3_1_7 () Bool)

(declare-fun stmt_3_2_0 () Bool)
(declare-fun stmt_3_2_1 () Bool)
(declare-fun stmt_3_2_2 () Bool)
(declare-fun stmt_3_2_3 () Bool)
(declare-fun stmt_3_2_4 () Bool)
(declare-fun stmt_3_2_5 () Bool)
(declare-fun stmt_3_2_6 () Bool)

(assert (= stmt_3_1_0 (and stmt_2_1_0 (not exec_2_1_0))))
(assert (= stmt_3_1_1 (ite stmt_2_1_6 (and exec_2_1_6 (not (= accu_2_1 #x0000))) (ite stmt_2_1_0 exec_2_1_0 (and stmt_2_1_1 (not exec_2_1_1))))))
(assert (= stmt_3_1_2 (ite stmt_2_1_1 exec_2_1_1 (and stmt_2_1_2 (not exec_2_1_2)))))
(assert (= stmt_3_1_3 (ite stmt_2_1_2 exec_2_1_2 (and stmt_2_1_3 (not exec_2_1_3)))))
(assert (= stmt_3_1_4 (ite stmt_2_1_3 exec_2_1_3 (and stmt_2_1_4 (not exec_2_1_4)))))
(assert (= stmt_3_1_5 (ite stmt_2_1_4 exec_2_1_4 (and stmt_2_1_5 (not exec_2_1_5)))))
(assert (= stmt_3_1_6 (ite stmt_2_1_5 exec_2_1_5 (and stmt_2_1_6 (not exec_2_1_6)))))
(assert (= stmt_3_1_7 (ite stmt_2_1_6 (and exec_2_1_6 (not (not (= accu_2_1 #x0000)))) (and stmt_2_1_7 (not exec_2_1_7)))))

(assert (= stmt_3_2_0 (ite stmt_2_2_5 (and exec_2_2_5 (not (= accu_2_2 #x0000))) (and stmt_2_2_0 (not exec_2_2_0)))))
(assert (= stmt_3_2_1 (ite stmt_2_2_0 exec_2_2_0 (and stmt_2_2_1 (not exec_2_2_1)))))
(assert (= stmt_3_2_2 (ite stmt_2_2_1 exec_2_2_1 (and stmt_2_2_2 (not exec_2_2_2)))))
(assert (= stmt_3_2_3 (ite stmt_2_2_2 exec_2_2_2 (and stmt_2_2_3 (not exec_2_2_3)))))
(assert (= stmt_3_2_4 (ite stmt_2_2_3 exec_2_2_3 (and stmt_2_2_4 (not exec_2_2_4)))))
(assert (= stmt_3_2_5 (ite stmt_2_2_4 exec_2_2_4 (and stmt_2_2_5 (not exec_2_2_5)))))
(assert (= stmt_3_2_6 (ite stmt_2_2_5 (and exec_2_2_5 (not (not (= accu_2_2 #x0000)))) (and stmt_2_2_6 (not exec_2_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_1 () Bool)
(declare-fun thread_3_2 () Bool)

(assert (or thread_3_1 thread_3_2 exit_3))
(assert (or (not thread_3_1) (not thread_3_2)))
(assert (or (not thread_3_1) (not exit_3)))
(assert (or (not thread_3_2) (not exit_3)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_3_0 () Bool)
(declare-fun sync_3_1 () Bool)

; all threads synchronized?
(assert (= sync_3_0 (and stmt_3_1_1 stmt_3_2_0 (or thread_3_1 thread_3_2))))
(assert (= sync_3_1 (and stmt_3_1_5 stmt_3_2_1 (or thread_3_1 thread_3_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_3_1_1 (not sync_3_0)) (not thread_3_1))) ; barrier 0: thread 1
(assert (=> (and stmt_3_2_0 (not sync_3_0)) (not thread_3_2))) ; barrier 0: thread 2
(assert (=> (and stmt_3_1_5 (not sync_3_1)) (not thread_3_1))) ; barrier 1: thread 1
(assert (=> (and stmt_3_2_1 (not sync_3_1)) (not thread_3_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_1_0 () Bool)
(declare-fun exec_3_1_1 () Bool)
(declare-fun exec_3_1_2 () Bool)
(declare-fun exec_3_1_3 () Bool)
(declare-fun exec_3_1_4 () Bool)
(declare-fun exec_3_1_5 () Bool)
(declare-fun exec_3_1_6 () Bool)
(declare-fun exec_3_1_7 () Bool)

(declare-fun exec_3_2_0 () Bool)
(declare-fun exec_3_2_1 () Bool)
(declare-fun exec_3_2_2 () Bool)
(declare-fun exec_3_2_3 () Bool)
(declare-fun exec_3_2_4 () Bool)
(declare-fun exec_3_2_5 () Bool)
(declare-fun exec_3_2_6 () Bool)

(assert (= exec_3_1_0 (and stmt_3_1_0 thread_3_1)))
(assert (= exec_3_1_1 (and stmt_3_1_1 sync_3_0)))
(assert (= exec_3_1_2 (and stmt_3_1_2 thread_3_1)))
(assert (= exec_3_1_3 (and stmt_3_1_3 thread_3_1)))
(assert (= exec_3_1_4 (and stmt_3_1_4 thread_3_1)))
(assert (= exec_3_1_5 (and stmt_3_1_5 sync_3_1)))
(assert (= exec_3_1_6 (and stmt_3_1_6 thread_3_1)))
(assert (= exec_3_1_7 (and stmt_3_1_7 thread_3_1)))

(assert (= exec_3_2_0 (and stmt_3_2_0 sync_3_0)))
(assert (= exec_3_2_1 (and stmt_3_2_1 sync_3_1)))
(assert (= exec_3_2_2 (and stmt_3_2_2 thread_3_2)))
(assert (= exec_3_2_3 (and stmt_3_2_3 thread_3_2)))
(assert (= exec_3_2_4 (and stmt_3_2_4 thread_3_2)))
(assert (= exec_3_2_5 (and stmt_3_2_5 thread_3_2)))
(assert (= exec_3_2_6 (and stmt_3_2_6 thread_3_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_3_1 () (_ BitVec 16))
(declare-fun accu_3_2 () (_ BitVec 16))

(assert (= accu_3_1 (ite exec_3_1_2 (select heap_2 #x0000) (ite exec_3_1_3 (bvadd accu_2_1 #x0001) accu_2_1))))
(assert (= accu_3_2 (ite exec_3_2_2 (select heap_2 #x0000) (ite exec_3_2_3 (bvadd accu_2_2 #x0001) accu_2_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_3_1 () (_ BitVec 16))
(declare-fun mem_3_2 () (_ BitVec 16))

(assert (= mem_3_1 mem_2_1))
(assert (= mem_3_2 mem_2_2))

; heap states - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_3 (ite exec_3_1_0 (store heap_2 #x0000 accu_2_1) (ite exec_3_1_4 (store heap_2 #x0000 accu_2_1) (ite exec_3_2_4 (store heap_2 #x0000 accu_2_2) heap_2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_4 () Bool)

(assert (= exit_4 (or exit_3 exec_3_1_7 exec_3_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_1_0 () Bool)
(declare-fun stmt_4_1_1 () Bool)
(declare-fun stmt_4_1_2 () Bool)
(declare-fun stmt_4_1_3 () Bool)
(declare-fun stmt_4_1_4 () Bool)
(declare-fun stmt_4_1_5 () Bool)
(declare-fun stmt_4_1_6 () Bool)
(declare-fun stmt_4_1_7 () Bool)

(declare-fun stmt_4_2_0 () Bool)
(declare-fun stmt_4_2_1 () Bool)
(declare-fun stmt_4_2_2 () Bool)
(declare-fun stmt_4_2_3 () Bool)
(declare-fun stmt_4_2_4 () Bool)
(declare-fun stmt_4_2_5 () Bool)
(declare-fun stmt_4_2_6 () Bool)

(assert (= stmt_4_1_0 (and stmt_3_1_0 (not exec_3_1_0))))
(assert (= stmt_4_1_1 (ite stmt_3_1_6 (and exec_3_1_6 (not (= accu_3_1 #x0000))) (ite stmt_3_1_0 exec_3_1_0 (and stmt_3_1_1 (not exec_3_1_1))))))
(assert (= stmt_4_1_2 (ite stmt_3_1_1 exec_3_1_1 (and stmt_3_1_2 (not exec_3_1_2)))))
(assert (= stmt_4_1_3 (ite stmt_3_1_2 exec_3_1_2 (and stmt_3_1_3 (not exec_3_1_3)))))
(assert (= stmt_4_1_4 (ite stmt_3_1_3 exec_3_1_3 (and stmt_3_1_4 (not exec_3_1_4)))))
(assert (= stmt_4_1_5 (ite stmt_3_1_4 exec_3_1_4 (and stmt_3_1_5 (not exec_3_1_5)))))
(assert (= stmt_4_1_6 (ite stmt_3_1_5 exec_3_1_5 (and stmt_3_1_6 (not exec_3_1_6)))))
(assert (= stmt_4_1_7 (ite stmt_3_1_6 (and exec_3_1_6 (not (not (= accu_3_1 #x0000)))) (and stmt_3_1_7 (not exec_3_1_7)))))

(assert (= stmt_4_2_0 (ite stmt_3_2_5 (and exec_3_2_5 (not (= accu_3_2 #x0000))) (and stmt_3_2_0 (not exec_3_2_0)))))
(assert (= stmt_4_2_1 (ite stmt_3_2_0 exec_3_2_0 (and stmt_3_2_1 (not exec_3_2_1)))))
(assert (= stmt_4_2_2 (ite stmt_3_2_1 exec_3_2_1 (and stmt_3_2_2 (not exec_3_2_2)))))
(assert (= stmt_4_2_3 (ite stmt_3_2_2 exec_3_2_2 (and stmt_3_2_3 (not exec_3_2_3)))))
(assert (= stmt_4_2_4 (ite stmt_3_2_3 exec_3_2_3 (and stmt_3_2_4 (not exec_3_2_4)))))
(assert (= stmt_4_2_5 (ite stmt_3_2_4 exec_3_2_4 (and stmt_3_2_5 (not exec_3_2_5)))))
(assert (= stmt_4_2_6 (ite stmt_3_2_5 (and exec_3_2_5 (not (not (= accu_3_2 #x0000)))) (and stmt_3_2_6 (not exec_3_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_1 () Bool)
(declare-fun thread_4_2 () Bool)

(assert (or thread_4_1 thread_4_2 exit_4))
(assert (or (not thread_4_1) (not thread_4_2)))
(assert (or (not thread_4_1) (not exit_4)))
(assert (or (not thread_4_2) (not exit_4)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_4_0 () Bool)
(declare-fun sync_4_1 () Bool)

; all threads synchronized?
(assert (= sync_4_0 (and stmt_4_1_1 stmt_4_2_0 (or thread_4_1 thread_4_2))))
(assert (= sync_4_1 (and stmt_4_1_5 stmt_4_2_1 (or thread_4_1 thread_4_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_4_1_1 (not sync_4_0)) (not thread_4_1))) ; barrier 0: thread 1
(assert (=> (and stmt_4_2_0 (not sync_4_0)) (not thread_4_2))) ; barrier 0: thread 2
(assert (=> (and stmt_4_1_5 (not sync_4_1)) (not thread_4_1))) ; barrier 1: thread 1
(assert (=> (and stmt_4_2_1 (not sync_4_1)) (not thread_4_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_1_0 () Bool)
(declare-fun exec_4_1_1 () Bool)
(declare-fun exec_4_1_2 () Bool)
(declare-fun exec_4_1_3 () Bool)
(declare-fun exec_4_1_4 () Bool)
(declare-fun exec_4_1_5 () Bool)
(declare-fun exec_4_1_6 () Bool)
(declare-fun exec_4_1_7 () Bool)

(declare-fun exec_4_2_0 () Bool)
(declare-fun exec_4_2_1 () Bool)
(declare-fun exec_4_2_2 () Bool)
(declare-fun exec_4_2_3 () Bool)
(declare-fun exec_4_2_4 () Bool)
(declare-fun exec_4_2_5 () Bool)
(declare-fun exec_4_2_6 () Bool)

(assert (= exec_4_1_0 (and stmt_4_1_0 thread_4_1)))
(assert (= exec_4_1_1 (and stmt_4_1_1 sync_4_0)))
(assert (= exec_4_1_2 (and stmt_4_1_2 thread_4_1)))
(assert (= exec_4_1_3 (and stmt_4_1_3 thread_4_1)))
(assert (= exec_4_1_4 (and stmt_4_1_4 thread_4_1)))
(assert (= exec_4_1_5 (and stmt_4_1_5 sync_4_1)))
(assert (= exec_4_1_6 (and stmt_4_1_6 thread_4_1)))
(assert (= exec_4_1_7 (and stmt_4_1_7 thread_4_1)))

(assert (= exec_4_2_0 (and stmt_4_2_0 sync_4_0)))
(assert (= exec_4_2_1 (and stmt_4_2_1 sync_4_1)))
(assert (= exec_4_2_2 (and stmt_4_2_2 thread_4_2)))
(assert (= exec_4_2_3 (and stmt_4_2_3 thread_4_2)))
(assert (= exec_4_2_4 (and stmt_4_2_4 thread_4_2)))
(assert (= exec_4_2_5 (and stmt_4_2_5 thread_4_2)))
(assert (= exec_4_2_6 (and stmt_4_2_6 thread_4_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_4_1 () (_ BitVec 16))
(declare-fun accu_4_2 () (_ BitVec 16))

(assert (= accu_4_1 (ite exec_4_1_2 (select heap_3 #x0000) (ite exec_4_1_3 (bvadd accu_3_1 #x0001) accu_3_1))))
(assert (= accu_4_2 (ite exec_4_2_2 (select heap_3 #x0000) (ite exec_4_2_3 (bvadd accu_3_2 #x0001) accu_3_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_4_1 () (_ BitVec 16))
(declare-fun mem_4_2 () (_ BitVec 16))

(assert (= mem_4_1 mem_3_1))
(assert (= mem_4_2 mem_3_2))

; heap states - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_4 (ite exec_4_1_0 (store heap_3 #x0000 accu_3_1) (ite exec_4_1_4 (store heap_3 #x0000 accu_3_1) (ite exec_4_2_4 (store heap_3 #x0000 accu_3_2) heap_3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_5 () Bool)

(assert (= exit_5 (or exit_4 exec_4_1_7 exec_4_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_1_0 () Bool)
(declare-fun stmt_5_1_1 () Bool)
(declare-fun stmt_5_1_2 () Bool)
(declare-fun stmt_5_1_3 () Bool)
(declare-fun stmt_5_1_4 () Bool)
(declare-fun stmt_5_1_5 () Bool)
(declare-fun stmt_5_1_6 () Bool)
(declare-fun stmt_5_1_7 () Bool)

(declare-fun stmt_5_2_0 () Bool)
(declare-fun stmt_5_2_1 () Bool)
(declare-fun stmt_5_2_2 () Bool)
(declare-fun stmt_5_2_3 () Bool)
(declare-fun stmt_5_2_4 () Bool)
(declare-fun stmt_5_2_5 () Bool)
(declare-fun stmt_5_2_6 () Bool)

(assert (= stmt_5_1_0 (and stmt_4_1_0 (not exec_4_1_0))))
(assert (= stmt_5_1_1 (ite stmt_4_1_6 (and exec_4_1_6 (not (= accu_4_1 #x0000))) (ite stmt_4_1_0 exec_4_1_0 (and stmt_4_1_1 (not exec_4_1_1))))))
(assert (= stmt_5_1_2 (ite stmt_4_1_1 exec_4_1_1 (and stmt_4_1_2 (not exec_4_1_2)))))
(assert (= stmt_5_1_3 (ite stmt_4_1_2 exec_4_1_2 (and stmt_4_1_3 (not exec_4_1_3)))))
(assert (= stmt_5_1_4 (ite stmt_4_1_3 exec_4_1_3 (and stmt_4_1_4 (not exec_4_1_4)))))
(assert (= stmt_5_1_5 (ite stmt_4_1_4 exec_4_1_4 (and stmt_4_1_5 (not exec_4_1_5)))))
(assert (= stmt_5_1_6 (ite stmt_4_1_5 exec_4_1_5 (and stmt_4_1_6 (not exec_4_1_6)))))
(assert (= stmt_5_1_7 (ite stmt_4_1_6 (and exec_4_1_6 (not (not (= accu_4_1 #x0000)))) (and stmt_4_1_7 (not exec_4_1_7)))))

(assert (= stmt_5_2_0 (ite stmt_4_2_5 (and exec_4_2_5 (not (= accu_4_2 #x0000))) (and stmt_4_2_0 (not exec_4_2_0)))))
(assert (= stmt_5_2_1 (ite stmt_4_2_0 exec_4_2_0 (and stmt_4_2_1 (not exec_4_2_1)))))
(assert (= stmt_5_2_2 (ite stmt_4_2_1 exec_4_2_1 (and stmt_4_2_2 (not exec_4_2_2)))))
(assert (= stmt_5_2_3 (ite stmt_4_2_2 exec_4_2_2 (and stmt_4_2_3 (not exec_4_2_3)))))
(assert (= stmt_5_2_4 (ite stmt_4_2_3 exec_4_2_3 (and stmt_4_2_4 (not exec_4_2_4)))))
(assert (= stmt_5_2_5 (ite stmt_4_2_4 exec_4_2_4 (and stmt_4_2_5 (not exec_4_2_5)))))
(assert (= stmt_5_2_6 (ite stmt_4_2_5 (and exec_4_2_5 (not (not (= accu_4_2 #x0000)))) (and stmt_4_2_6 (not exec_4_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_1 () Bool)
(declare-fun thread_5_2 () Bool)

(assert (or thread_5_1 thread_5_2 exit_5))
(assert (or (not thread_5_1) (not thread_5_2)))
(assert (or (not thread_5_1) (not exit_5)))
(assert (or (not thread_5_2) (not exit_5)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_5_0 () Bool)
(declare-fun sync_5_1 () Bool)

; all threads synchronized?
(assert (= sync_5_0 (and stmt_5_1_1 stmt_5_2_0 (or thread_5_1 thread_5_2))))
(assert (= sync_5_1 (and stmt_5_1_5 stmt_5_2_1 (or thread_5_1 thread_5_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_5_1_1 (not sync_5_0)) (not thread_5_1))) ; barrier 0: thread 1
(assert (=> (and stmt_5_2_0 (not sync_5_0)) (not thread_5_2))) ; barrier 0: thread 2
(assert (=> (and stmt_5_1_5 (not sync_5_1)) (not thread_5_1))) ; barrier 1: thread 1
(assert (=> (and stmt_5_2_1 (not sync_5_1)) (not thread_5_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_1_0 () Bool)
(declare-fun exec_5_1_1 () Bool)
(declare-fun exec_5_1_2 () Bool)
(declare-fun exec_5_1_3 () Bool)
(declare-fun exec_5_1_4 () Bool)
(declare-fun exec_5_1_5 () Bool)
(declare-fun exec_5_1_6 () Bool)
(declare-fun exec_5_1_7 () Bool)

(declare-fun exec_5_2_0 () Bool)
(declare-fun exec_5_2_1 () Bool)
(declare-fun exec_5_2_2 () Bool)
(declare-fun exec_5_2_3 () Bool)
(declare-fun exec_5_2_4 () Bool)
(declare-fun exec_5_2_5 () Bool)
(declare-fun exec_5_2_6 () Bool)

(assert (= exec_5_1_0 (and stmt_5_1_0 thread_5_1)))
(assert (= exec_5_1_1 (and stmt_5_1_1 sync_5_0)))
(assert (= exec_5_1_2 (and stmt_5_1_2 thread_5_1)))
(assert (= exec_5_1_3 (and stmt_5_1_3 thread_5_1)))
(assert (= exec_5_1_4 (and stmt_5_1_4 thread_5_1)))
(assert (= exec_5_1_5 (and stmt_5_1_5 sync_5_1)))
(assert (= exec_5_1_6 (and stmt_5_1_6 thread_5_1)))
(assert (= exec_5_1_7 (and stmt_5_1_7 thread_5_1)))

(assert (= exec_5_2_0 (and stmt_5_2_0 sync_5_0)))
(assert (= exec_5_2_1 (and stmt_5_2_1 sync_5_1)))
(assert (= exec_5_2_2 (and stmt_5_2_2 thread_5_2)))
(assert (= exec_5_2_3 (and stmt_5_2_3 thread_5_2)))
(assert (= exec_5_2_4 (and stmt_5_2_4 thread_5_2)))
(assert (= exec_5_2_5 (and stmt_5_2_5 thread_5_2)))
(assert (= exec_5_2_6 (and stmt_5_2_6 thread_5_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_5_1 () (_ BitVec 16))
(declare-fun accu_5_2 () (_ BitVec 16))

(assert (= accu_5_1 (ite exec_5_1_2 (select heap_4 #x0000) (ite exec_5_1_3 (bvadd accu_4_1 #x0001) accu_4_1))))
(assert (= accu_5_2 (ite exec_5_2_2 (select heap_4 #x0000) (ite exec_5_2_3 (bvadd accu_4_2 #x0001) accu_4_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_5_1 () (_ BitVec 16))
(declare-fun mem_5_2 () (_ BitVec 16))

(assert (= mem_5_1 mem_4_1))
(assert (= mem_5_2 mem_4_2))

; heap states - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_5 (ite exec_5_1_0 (store heap_4 #x0000 accu_4_1) (ite exec_5_1_4 (store heap_4 #x0000 accu_4_1) (ite exec_5_2_4 (store heap_4 #x0000 accu_4_2) heap_4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_6 () Bool)

(assert (= exit_6 (or exit_5 exec_5_1_7 exec_5_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_1_0 () Bool)
(declare-fun stmt_6_1_1 () Bool)
(declare-fun stmt_6_1_2 () Bool)
(declare-fun stmt_6_1_3 () Bool)
(declare-fun stmt_6_1_4 () Bool)
(declare-fun stmt_6_1_5 () Bool)
(declare-fun stmt_6_1_6 () Bool)
(declare-fun stmt_6_1_7 () Bool)

(declare-fun stmt_6_2_0 () Bool)
(declare-fun stmt_6_2_1 () Bool)
(declare-fun stmt_6_2_2 () Bool)
(declare-fun stmt_6_2_3 () Bool)
(declare-fun stmt_6_2_4 () Bool)
(declare-fun stmt_6_2_5 () Bool)
(declare-fun stmt_6_2_6 () Bool)

(assert (= stmt_6_1_0 (and stmt_5_1_0 (not exec_5_1_0))))
(assert (= stmt_6_1_1 (ite stmt_5_1_6 (and exec_5_1_6 (not (= accu_5_1 #x0000))) (ite stmt_5_1_0 exec_5_1_0 (and stmt_5_1_1 (not exec_5_1_1))))))
(assert (= stmt_6_1_2 (ite stmt_5_1_1 exec_5_1_1 (and stmt_5_1_2 (not exec_5_1_2)))))
(assert (= stmt_6_1_3 (ite stmt_5_1_2 exec_5_1_2 (and stmt_5_1_3 (not exec_5_1_3)))))
(assert (= stmt_6_1_4 (ite stmt_5_1_3 exec_5_1_3 (and stmt_5_1_4 (not exec_5_1_4)))))
(assert (= stmt_6_1_5 (ite stmt_5_1_4 exec_5_1_4 (and stmt_5_1_5 (not exec_5_1_5)))))
(assert (= stmt_6_1_6 (ite stmt_5_1_5 exec_5_1_5 (and stmt_5_1_6 (not exec_5_1_6)))))
(assert (= stmt_6_1_7 (ite stmt_5_1_6 (and exec_5_1_6 (not (not (= accu_5_1 #x0000)))) (and stmt_5_1_7 (not exec_5_1_7)))))

(assert (= stmt_6_2_0 (ite stmt_5_2_5 (and exec_5_2_5 (not (= accu_5_2 #x0000))) (and stmt_5_2_0 (not exec_5_2_0)))))
(assert (= stmt_6_2_1 (ite stmt_5_2_0 exec_5_2_0 (and stmt_5_2_1 (not exec_5_2_1)))))
(assert (= stmt_6_2_2 (ite stmt_5_2_1 exec_5_2_1 (and stmt_5_2_2 (not exec_5_2_2)))))
(assert (= stmt_6_2_3 (ite stmt_5_2_2 exec_5_2_2 (and stmt_5_2_3 (not exec_5_2_3)))))
(assert (= stmt_6_2_4 (ite stmt_5_2_3 exec_5_2_3 (and stmt_5_2_4 (not exec_5_2_4)))))
(assert (= stmt_6_2_5 (ite stmt_5_2_4 exec_5_2_4 (and stmt_5_2_5 (not exec_5_2_5)))))
(assert (= stmt_6_2_6 (ite stmt_5_2_5 (and exec_5_2_5 (not (not (= accu_5_2 #x0000)))) (and stmt_5_2_6 (not exec_5_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_1 () Bool)
(declare-fun thread_6_2 () Bool)

(assert (or thread_6_1 thread_6_2 exit_6))
(assert (or (not thread_6_1) (not thread_6_2)))
(assert (or (not thread_6_1) (not exit_6)))
(assert (or (not thread_6_2) (not exit_6)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_6_0 () Bool)
(declare-fun sync_6_1 () Bool)

; all threads synchronized?
(assert (= sync_6_0 (and stmt_6_1_1 stmt_6_2_0 (or thread_6_1 thread_6_2))))
(assert (= sync_6_1 (and stmt_6_1_5 stmt_6_2_1 (or thread_6_1 thread_6_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_6_1_1 (not sync_6_0)) (not thread_6_1))) ; barrier 0: thread 1
(assert (=> (and stmt_6_2_0 (not sync_6_0)) (not thread_6_2))) ; barrier 0: thread 2
(assert (=> (and stmt_6_1_5 (not sync_6_1)) (not thread_6_1))) ; barrier 1: thread 1
(assert (=> (and stmt_6_2_1 (not sync_6_1)) (not thread_6_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_1_0 () Bool)
(declare-fun exec_6_1_1 () Bool)
(declare-fun exec_6_1_2 () Bool)
(declare-fun exec_6_1_3 () Bool)
(declare-fun exec_6_1_4 () Bool)
(declare-fun exec_6_1_5 () Bool)
(declare-fun exec_6_1_6 () Bool)
(declare-fun exec_6_1_7 () Bool)

(declare-fun exec_6_2_0 () Bool)
(declare-fun exec_6_2_1 () Bool)
(declare-fun exec_6_2_2 () Bool)
(declare-fun exec_6_2_3 () Bool)
(declare-fun exec_6_2_4 () Bool)
(declare-fun exec_6_2_5 () Bool)
(declare-fun exec_6_2_6 () Bool)

(assert (= exec_6_1_0 (and stmt_6_1_0 thread_6_1)))
(assert (= exec_6_1_1 (and stmt_6_1_1 sync_6_0)))
(assert (= exec_6_1_2 (and stmt_6_1_2 thread_6_1)))
(assert (= exec_6_1_3 (and stmt_6_1_3 thread_6_1)))
(assert (= exec_6_1_4 (and stmt_6_1_4 thread_6_1)))
(assert (= exec_6_1_5 (and stmt_6_1_5 sync_6_1)))
(assert (= exec_6_1_6 (and stmt_6_1_6 thread_6_1)))
(assert (= exec_6_1_7 (and stmt_6_1_7 thread_6_1)))

(assert (= exec_6_2_0 (and stmt_6_2_0 sync_6_0)))
(assert (= exec_6_2_1 (and stmt_6_2_1 sync_6_1)))
(assert (= exec_6_2_2 (and stmt_6_2_2 thread_6_2)))
(assert (= exec_6_2_3 (and stmt_6_2_3 thread_6_2)))
(assert (= exec_6_2_4 (and stmt_6_2_4 thread_6_2)))
(assert (= exec_6_2_5 (and stmt_6_2_5 thread_6_2)))
(assert (= exec_6_2_6 (and stmt_6_2_6 thread_6_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_6_1 () (_ BitVec 16))
(declare-fun accu_6_2 () (_ BitVec 16))

(assert (= accu_6_1 (ite exec_6_1_2 (select heap_5 #x0000) (ite exec_6_1_3 (bvadd accu_5_1 #x0001) accu_5_1))))
(assert (= accu_6_2 (ite exec_6_2_2 (select heap_5 #x0000) (ite exec_6_2_3 (bvadd accu_5_2 #x0001) accu_5_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_6_1 () (_ BitVec 16))
(declare-fun mem_6_2 () (_ BitVec 16))

(assert (= mem_6_1 mem_5_1))
(assert (= mem_6_2 mem_5_2))

; heap states - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_6 (ite exec_6_1_0 (store heap_5 #x0000 accu_5_1) (ite exec_6_1_4 (store heap_5 #x0000 accu_5_1) (ite exec_6_2_4 (store heap_5 #x0000 accu_5_2) heap_5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_7 () Bool)

(assert (= exit_7 (or exit_6 exec_6_1_7 exec_6_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_1_0 () Bool)
(declare-fun stmt_7_1_1 () Bool)
(declare-fun stmt_7_1_2 () Bool)
(declare-fun stmt_7_1_3 () Bool)
(declare-fun stmt_7_1_4 () Bool)
(declare-fun stmt_7_1_5 () Bool)
(declare-fun stmt_7_1_6 () Bool)
(declare-fun stmt_7_1_7 () Bool)

(declare-fun stmt_7_2_0 () Bool)
(declare-fun stmt_7_2_1 () Bool)
(declare-fun stmt_7_2_2 () Bool)
(declare-fun stmt_7_2_3 () Bool)
(declare-fun stmt_7_2_4 () Bool)
(declare-fun stmt_7_2_5 () Bool)
(declare-fun stmt_7_2_6 () Bool)

(assert (= stmt_7_1_0 (and stmt_6_1_0 (not exec_6_1_0))))
(assert (= stmt_7_1_1 (ite stmt_6_1_6 (and exec_6_1_6 (not (= accu_6_1 #x0000))) (ite stmt_6_1_0 exec_6_1_0 (and stmt_6_1_1 (not exec_6_1_1))))))
(assert (= stmt_7_1_2 (ite stmt_6_1_1 exec_6_1_1 (and stmt_6_1_2 (not exec_6_1_2)))))
(assert (= stmt_7_1_3 (ite stmt_6_1_2 exec_6_1_2 (and stmt_6_1_3 (not exec_6_1_3)))))
(assert (= stmt_7_1_4 (ite stmt_6_1_3 exec_6_1_3 (and stmt_6_1_4 (not exec_6_1_4)))))
(assert (= stmt_7_1_5 (ite stmt_6_1_4 exec_6_1_4 (and stmt_6_1_5 (not exec_6_1_5)))))
(assert (= stmt_7_1_6 (ite stmt_6_1_5 exec_6_1_5 (and stmt_6_1_6 (not exec_6_1_6)))))
(assert (= stmt_7_1_7 (ite stmt_6_1_6 (and exec_6_1_6 (not (not (= accu_6_1 #x0000)))) (and stmt_6_1_7 (not exec_6_1_7)))))

(assert (= stmt_7_2_0 (ite stmt_6_2_5 (and exec_6_2_5 (not (= accu_6_2 #x0000))) (and stmt_6_2_0 (not exec_6_2_0)))))
(assert (= stmt_7_2_1 (ite stmt_6_2_0 exec_6_2_0 (and stmt_6_2_1 (not exec_6_2_1)))))
(assert (= stmt_7_2_2 (ite stmt_6_2_1 exec_6_2_1 (and stmt_6_2_2 (not exec_6_2_2)))))
(assert (= stmt_7_2_3 (ite stmt_6_2_2 exec_6_2_2 (and stmt_6_2_3 (not exec_6_2_3)))))
(assert (= stmt_7_2_4 (ite stmt_6_2_3 exec_6_2_3 (and stmt_6_2_4 (not exec_6_2_4)))))
(assert (= stmt_7_2_5 (ite stmt_6_2_4 exec_6_2_4 (and stmt_6_2_5 (not exec_6_2_5)))))
(assert (= stmt_7_2_6 (ite stmt_6_2_5 (and exec_6_2_5 (not (not (= accu_6_2 #x0000)))) (and stmt_6_2_6 (not exec_6_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_1 () Bool)
(declare-fun thread_7_2 () Bool)

(assert (or thread_7_1 thread_7_2 exit_7))
(assert (or (not thread_7_1) (not thread_7_2)))
(assert (or (not thread_7_1) (not exit_7)))
(assert (or (not thread_7_2) (not exit_7)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_7_0 () Bool)
(declare-fun sync_7_1 () Bool)

; all threads synchronized?
(assert (= sync_7_0 (and stmt_7_1_1 stmt_7_2_0 (or thread_7_1 thread_7_2))))
(assert (= sync_7_1 (and stmt_7_1_5 stmt_7_2_1 (or thread_7_1 thread_7_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_7_1_1 (not sync_7_0)) (not thread_7_1))) ; barrier 0: thread 1
(assert (=> (and stmt_7_2_0 (not sync_7_0)) (not thread_7_2))) ; barrier 0: thread 2
(assert (=> (and stmt_7_1_5 (not sync_7_1)) (not thread_7_1))) ; barrier 1: thread 1
(assert (=> (and stmt_7_2_1 (not sync_7_1)) (not thread_7_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_1_0 () Bool)
(declare-fun exec_7_1_1 () Bool)
(declare-fun exec_7_1_2 () Bool)
(declare-fun exec_7_1_3 () Bool)
(declare-fun exec_7_1_4 () Bool)
(declare-fun exec_7_1_5 () Bool)
(declare-fun exec_7_1_6 () Bool)
(declare-fun exec_7_1_7 () Bool)

(declare-fun exec_7_2_0 () Bool)
(declare-fun exec_7_2_1 () Bool)
(declare-fun exec_7_2_2 () Bool)
(declare-fun exec_7_2_3 () Bool)
(declare-fun exec_7_2_4 () Bool)
(declare-fun exec_7_2_5 () Bool)
(declare-fun exec_7_2_6 () Bool)

(assert (= exec_7_1_0 (and stmt_7_1_0 thread_7_1)))
(assert (= exec_7_1_1 (and stmt_7_1_1 sync_7_0)))
(assert (= exec_7_1_2 (and stmt_7_1_2 thread_7_1)))
(assert (= exec_7_1_3 (and stmt_7_1_3 thread_7_1)))
(assert (= exec_7_1_4 (and stmt_7_1_4 thread_7_1)))
(assert (= exec_7_1_5 (and stmt_7_1_5 sync_7_1)))
(assert (= exec_7_1_6 (and stmt_7_1_6 thread_7_1)))
(assert (= exec_7_1_7 (and stmt_7_1_7 thread_7_1)))

(assert (= exec_7_2_0 (and stmt_7_2_0 sync_7_0)))
(assert (= exec_7_2_1 (and stmt_7_2_1 sync_7_1)))
(assert (= exec_7_2_2 (and stmt_7_2_2 thread_7_2)))
(assert (= exec_7_2_3 (and stmt_7_2_3 thread_7_2)))
(assert (= exec_7_2_4 (and stmt_7_2_4 thread_7_2)))
(assert (= exec_7_2_5 (and stmt_7_2_5 thread_7_2)))
(assert (= exec_7_2_6 (and stmt_7_2_6 thread_7_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_7_1 () (_ BitVec 16))
(declare-fun accu_7_2 () (_ BitVec 16))

(assert (= accu_7_1 (ite exec_7_1_2 (select heap_6 #x0000) (ite exec_7_1_3 (bvadd accu_6_1 #x0001) accu_6_1))))
(assert (= accu_7_2 (ite exec_7_2_2 (select heap_6 #x0000) (ite exec_7_2_3 (bvadd accu_6_2 #x0001) accu_6_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_7_1 () (_ BitVec 16))
(declare-fun mem_7_2 () (_ BitVec 16))

(assert (= mem_7_1 mem_6_1))
(assert (= mem_7_2 mem_6_2))

; heap states - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_7 (ite exec_7_1_0 (store heap_6 #x0000 accu_6_1) (ite exec_7_1_4 (store heap_6 #x0000 accu_6_1) (ite exec_7_2_4 (store heap_6 #x0000 accu_6_2) heap_6)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit variable - exit_<step>
(declare-fun exit_8 () Bool)

(assert (= exit_8 (or exit_7 exec_7_1_7 exec_7_2_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_1_0 () Bool)
(declare-fun stmt_8_1_1 () Bool)
(declare-fun stmt_8_1_2 () Bool)
(declare-fun stmt_8_1_3 () Bool)
(declare-fun stmt_8_1_4 () Bool)
(declare-fun stmt_8_1_5 () Bool)
(declare-fun stmt_8_1_6 () Bool)
(declare-fun stmt_8_1_7 () Bool)

(declare-fun stmt_8_2_0 () Bool)
(declare-fun stmt_8_2_1 () Bool)
(declare-fun stmt_8_2_2 () Bool)
(declare-fun stmt_8_2_3 () Bool)
(declare-fun stmt_8_2_4 () Bool)
(declare-fun stmt_8_2_5 () Bool)
(declare-fun stmt_8_2_6 () Bool)

(assert (= stmt_8_1_0 (and stmt_7_1_0 (not exec_7_1_0))))
(assert (= stmt_8_1_1 (ite stmt_7_1_6 (and exec_7_1_6 (not (= accu_7_1 #x0000))) (ite stmt_7_1_0 exec_7_1_0 (and stmt_7_1_1 (not exec_7_1_1))))))
(assert (= stmt_8_1_2 (ite stmt_7_1_1 exec_7_1_1 (and stmt_7_1_2 (not exec_7_1_2)))))
(assert (= stmt_8_1_3 (ite stmt_7_1_2 exec_7_1_2 (and stmt_7_1_3 (not exec_7_1_3)))))
(assert (= stmt_8_1_4 (ite stmt_7_1_3 exec_7_1_3 (and stmt_7_1_4 (not exec_7_1_4)))))
(assert (= stmt_8_1_5 (ite stmt_7_1_4 exec_7_1_4 (and stmt_7_1_5 (not exec_7_1_5)))))
(assert (= stmt_8_1_6 (ite stmt_7_1_5 exec_7_1_5 (and stmt_7_1_6 (not exec_7_1_6)))))
(assert (= stmt_8_1_7 (ite stmt_7_1_6 (and exec_7_1_6 (not (not (= accu_7_1 #x0000)))) (and stmt_7_1_7 (not exec_7_1_7)))))

(assert (= stmt_8_2_0 (ite stmt_7_2_5 (and exec_7_2_5 (not (= accu_7_2 #x0000))) (and stmt_7_2_0 (not exec_7_2_0)))))
(assert (= stmt_8_2_1 (ite stmt_7_2_0 exec_7_2_0 (and stmt_7_2_1 (not exec_7_2_1)))))
(assert (= stmt_8_2_2 (ite stmt_7_2_1 exec_7_2_1 (and stmt_7_2_2 (not exec_7_2_2)))))
(assert (= stmt_8_2_3 (ite stmt_7_2_2 exec_7_2_2 (and stmt_7_2_3 (not exec_7_2_3)))))
(assert (= stmt_8_2_4 (ite stmt_7_2_3 exec_7_2_3 (and stmt_7_2_4 (not exec_7_2_4)))))
(assert (= stmt_8_2_5 (ite stmt_7_2_4 exec_7_2_4 (and stmt_7_2_5 (not exec_7_2_5)))))
(assert (= stmt_8_2_6 (ite stmt_7_2_5 (and exec_7_2_5 (not (not (= accu_7_2 #x0000)))) (and stmt_7_2_6 (not exec_7_2_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_1 () Bool)
(declare-fun thread_8_2 () Bool)

(assert (or thread_8_1 thread_8_2 exit_8))
(assert (or (not thread_8_1) (not thread_8_2)))
(assert (or (not thread_8_1) (not exit_8)))
(assert (or (not thread_8_2) (not exit_8)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_8_0 () Bool)
(declare-fun sync_8_1 () Bool)

; all threads synchronized?
(assert (= sync_8_0 (and stmt_8_1_1 stmt_8_2_0 (or thread_8_1 thread_8_2))))
(assert (= sync_8_1 (and stmt_8_1_5 stmt_8_2_1 (or thread_8_1 thread_8_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_8_1_1 (not sync_8_0)) (not thread_8_1))) ; barrier 0: thread 1
(assert (=> (and stmt_8_2_0 (not sync_8_0)) (not thread_8_2))) ; barrier 0: thread 2
(assert (=> (and stmt_8_1_5 (not sync_8_1)) (not thread_8_1))) ; barrier 1: thread 1
(assert (=> (and stmt_8_2_1 (not sync_8_1)) (not thread_8_2))) ; barrier 1: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_1_0 () Bool)
(declare-fun exec_8_1_1 () Bool)
(declare-fun exec_8_1_2 () Bool)
(declare-fun exec_8_1_3 () Bool)
(declare-fun exec_8_1_4 () Bool)
(declare-fun exec_8_1_5 () Bool)
(declare-fun exec_8_1_6 () Bool)
(declare-fun exec_8_1_7 () Bool)

(declare-fun exec_8_2_0 () Bool)
(declare-fun exec_8_2_1 () Bool)
(declare-fun exec_8_2_2 () Bool)
(declare-fun exec_8_2_3 () Bool)
(declare-fun exec_8_2_4 () Bool)
(declare-fun exec_8_2_5 () Bool)
(declare-fun exec_8_2_6 () Bool)

(assert (= exec_8_1_0 (and stmt_8_1_0 thread_8_1)))
(assert (= exec_8_1_1 (and stmt_8_1_1 sync_8_0)))
(assert (= exec_8_1_2 (and stmt_8_1_2 thread_8_1)))
(assert (= exec_8_1_3 (and stmt_8_1_3 thread_8_1)))
(assert (= exec_8_1_4 (and stmt_8_1_4 thread_8_1)))
(assert (= exec_8_1_5 (and stmt_8_1_5 sync_8_1)))
(assert (= exec_8_1_6 (and stmt_8_1_6 thread_8_1)))
(assert (= exec_8_1_7 (and stmt_8_1_7 thread_8_1)))

(assert (= exec_8_2_0 (and stmt_8_2_0 sync_8_0)))
(assert (= exec_8_2_1 (and stmt_8_2_1 sync_8_1)))
(assert (= exec_8_2_2 (and stmt_8_2_2 thread_8_2)))
(assert (= exec_8_2_3 (and stmt_8_2_3 thread_8_2)))
(assert (= exec_8_2_4 (and stmt_8_2_4 thread_8_2)))
(assert (= exec_8_2_5 (and stmt_8_2_5 thread_8_2)))
(assert (= exec_8_2_6 (and stmt_8_2_6 thread_8_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_8_1 () (_ BitVec 16))
(declare-fun accu_8_2 () (_ BitVec 16))

(assert (= accu_8_1 (ite exec_8_1_2 (select heap_7 #x0000) (ite exec_8_1_3 (bvadd accu_7_1 #x0001) accu_7_1))))
(assert (= accu_8_2 (ite exec_8_2_2 (select heap_7 #x0000) (ite exec_8_2_3 (bvadd accu_7_2 #x0001) accu_7_2))))

; mem states - mem_<step>_<thread>
(declare-fun mem_8_1 () (_ BitVec 16))
(declare-fun mem_8_2 () (_ BitVec 16))

(assert (= mem_8_1 mem_7_1))
(assert (= mem_8_2 mem_7_2))

; heap states - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_8 (ite exec_8_1_0 (store heap_7 #x0000 accu_7_1) (ite exec_8_1_4 (store heap_7 #x0000 accu_7_1) (ite exec_8_2_4 (store heap_7 #x0000 accu_7_2) heap_7)))))

; exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun exit_code () (_ BitVec 16))

(assert (= exit_code (ite exec_1_1_7 #x0001 (ite exec_1_2_6 #x0001 (ite exec_2_1_7 #x0001 (ite exec_2_2_6 #x0001 (ite exec_3_1_7 #x0001 (ite exec_3_2_6 #x0001 (ite exec_4_1_7 #x0001 (ite exec_4_2_6 #x0001 (ite exec_5_1_7 #x0001 (ite exec_5_2_6 #x0001 (ite exec_6_1_7 #x0001 (ite exec_6_2_6 #x0001 (ite exec_7_1_7 #x0001 (ite exec_7_2_6 #x0001 (ite exec_8_1_7 #x0001 (ite exec_8_2_6 #x0001 #x0000))))))))))))))))))

