(set-logic QF_AUFBV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; initial state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_0_0 () (_ BitVec 16))
(declare-fun accu_0_1 () (_ BitVec 16))

(assert (= accu_0_0 #x0000))
(assert (= accu_0_1 #x0000))

; mem states - mem_<step>_<thread>
(declare-fun mem_0_0 () (_ BitVec 16))
(declare-fun mem_0_1 () (_ BitVec 16))

(assert (= mem_0_0 #x0000))
(assert (= mem_0_1 #x0000))

; heap states - heap_<step>
(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_0_0 () Bool)
(declare-fun stmt_1_0_1 () Bool)
(declare-fun stmt_1_0_2 () Bool)
(declare-fun stmt_1_0_3 () Bool)
(declare-fun stmt_1_0_4 () Bool)
(declare-fun stmt_1_0_5 () Bool)
(declare-fun stmt_1_0_6 () Bool)
(declare-fun stmt_1_0_7 () Bool)

(declare-fun stmt_1_1_0 () Bool)
(declare-fun stmt_1_1_1 () Bool)
(declare-fun stmt_1_1_2 () Bool)
(declare-fun stmt_1_1_3 () Bool)
(declare-fun stmt_1_1_4 () Bool)
(declare-fun stmt_1_1_5 () Bool)
(declare-fun stmt_1_1_6 () Bool)

; initial statement activation
(assert stmt_1_0_0)
(assert (not stmt_1_0_1))
(assert (not stmt_1_0_2))
(assert (not stmt_1_0_3))
(assert (not stmt_1_0_4))
(assert (not stmt_1_0_5))
(assert (not stmt_1_0_6))
(assert (not stmt_1_0_7))

(assert stmt_1_1_0)
(assert (not stmt_1_1_1))
(assert (not stmt_1_1_2))
(assert (not stmt_1_1_3))
(assert (not stmt_1_1_4))
(assert (not stmt_1_1_5))
(assert (not stmt_1_1_6))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_0 () Bool)
(declare-fun thread_1_1 () Bool)

(assert (xor thread_1_0 thread_1_1))

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_0_0 () Bool)
(declare-fun exec_1_0_1 () Bool)
(declare-fun exec_1_0_2 () Bool)
(declare-fun exec_1_0_3 () Bool)
(declare-fun exec_1_0_4 () Bool)
(declare-fun exec_1_0_5 () Bool)
(declare-fun exec_1_0_6 () Bool)
(declare-fun exec_1_0_7 () Bool)

(declare-fun exec_1_1_0 () Bool)
(declare-fun exec_1_1_1 () Bool)
(declare-fun exec_1_1_2 () Bool)
(declare-fun exec_1_1_3 () Bool)
(declare-fun exec_1_1_4 () Bool)
(declare-fun exec_1_1_5 () Bool)
(declare-fun exec_1_1_6 () Bool)

(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))
(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))
(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))
(assert (= exec_1_0_3 (and stmt_1_0_3 thread_1_0)))
(assert (= exec_1_0_4 (and stmt_1_0_4 thread_1_0)))
(assert (= exec_1_0_5 (and stmt_1_0_5 thread_1_0)))
(assert (= exec_1_0_6 (and stmt_1_0_6 thread_1_0)))
(assert (= exec_1_0_7 (and stmt_1_0_7 thread_1_0)))

(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))
(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))
(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))
(assert (= exec_1_1_3 (and stmt_1_1_3 thread_1_1)))
(assert (= exec_1_1_4 (and stmt_1_1_4 thread_1_1)))
(assert (= exec_1_1_5 (and stmt_1_1_5 thread_1_1)))
(assert (= exec_1_1_6 (and stmt_1_1_6 thread_1_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_1_0 () (_ BitVec 16))
(declare-fun accu_1_1 () (_ BitVec 16))

(assert (= accu_1_0 (ite exec_1_0_2 (select heap_0 #x0000) (ite exec_1_0_3 (bvadd accu_0_0 #x0001) accu_0_0))))
(assert (= accu_1_1 (ite exec_1_1_2 (select heap_0 #x0000) (ite exec_1_1_3 (bvadd accu_0_1 #x0001) accu_0_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_1_0 () (_ BitVec 16))
(declare-fun mem_1_1 () (_ BitVec 16))

(assert (= mem_1_0 mem_0_0))
(assert (= mem_1_1 mem_0_1))

; heap states - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_1 (ite exec_1_0_0 (store heap_0 #x0000 accu_0_0) (ite exec_1_0_4 (store heap_0 #x0000 accu_0_0) (ite exec_1_1_4 (store heap_0 #x0000 accu_0_1) heap_0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_2 () Bool)

(assert (= exit_2 (or exec_1_0_7 exec_1_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_0_0 () Bool)
(declare-fun stmt_2_0_1 () Bool)
(declare-fun stmt_2_0_2 () Bool)
(declare-fun stmt_2_0_3 () Bool)
(declare-fun stmt_2_0_4 () Bool)
(declare-fun stmt_2_0_5 () Bool)
(declare-fun stmt_2_0_6 () Bool)
(declare-fun stmt_2_0_7 () Bool)

(declare-fun stmt_2_1_0 () Bool)
(declare-fun stmt_2_1_1 () Bool)
(declare-fun stmt_2_1_2 () Bool)
(declare-fun stmt_2_1_3 () Bool)
(declare-fun stmt_2_1_4 () Bool)
(declare-fun stmt_2_1_5 () Bool)
(declare-fun stmt_2_1_6 () Bool)

(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))
(assert (= stmt_2_0_1 (ite stmt_1_0_6 (and exec_1_0_6 (not (= accu_1_0 #x0000))) (ite stmt_1_0_0 exec_1_0_0 (and stmt_1_0_1 (not exec_1_0_1))))))
(assert (= stmt_2_0_2 (ite stmt_1_0_1 exec_1_0_1 (and stmt_1_0_2 (not exec_1_0_2)))))
(assert (= stmt_2_0_3 (ite stmt_1_0_2 exec_1_0_2 (and stmt_1_0_3 (not exec_1_0_3)))))
(assert (= stmt_2_0_4 (ite stmt_1_0_3 exec_1_0_3 (and stmt_1_0_4 (not exec_1_0_4)))))
(assert (= stmt_2_0_5 (ite stmt_1_0_4 exec_1_0_4 (and stmt_1_0_5 (not exec_1_0_5)))))
(assert (= stmt_2_0_6 (ite stmt_1_0_5 exec_1_0_5 (and stmt_1_0_6 (not exec_1_0_6)))))
(assert (= stmt_2_0_7 (ite stmt_1_0_6 (and exec_1_0_6 (not (not (= accu_1_0 #x0000)))) (and stmt_1_0_7 (not exec_1_0_7)))))

(assert (= stmt_2_1_0 (ite stmt_1_1_5 (and exec_1_1_5 (not (= accu_1_1 #x0000))) (and stmt_1_1_0 (not exec_1_1_0)))))
(assert (= stmt_2_1_1 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))
(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))
(assert (= stmt_2_1_3 (ite stmt_1_1_2 exec_1_1_2 (and stmt_1_1_3 (not exec_1_1_3)))))
(assert (= stmt_2_1_4 (ite stmt_1_1_3 exec_1_1_3 (and stmt_1_1_4 (not exec_1_1_4)))))
(assert (= stmt_2_1_5 (ite stmt_1_1_4 exec_1_1_4 (and stmt_1_1_5 (not exec_1_1_5)))))
(assert (= stmt_2_1_6 (ite stmt_1_1_5 (and exec_1_1_5 (not (not (= accu_1_1 #x0000)))) (and stmt_1_1_6 (not exec_1_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_0 () Bool)
(declare-fun thread_2_1 () Bool)

(assert (or thread_2_0 thread_2_1 exit_2))
(assert (or (not thread_2_0) (not thread_2_1)))
(assert (or (not thread_2_0) (not exit_2)))
(assert (or (not thread_2_1) (not exit_2)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_2_0_0 () Bool)
(declare-fun block_2_0_1 () Bool)
(declare-fun block_2_1_0 () Bool)
(declare-fun block_2_1_1 () Bool)

(assert (= block_2_0_0 exec_1_0_1))
(assert (= block_2_0_1 exec_1_1_0))
(assert (= block_2_1_0 exec_1_0_5))
(assert (= block_2_1_1 exec_1_1_1))

; sync variables - sync_<step>_<id>
(declare-fun sync_2_0 () Bool)
(declare-fun sync_2_1 () Bool)

(assert (= sync_2_0 (and block_2_0_0 block_2_0_1)))
(assert (= sync_2_1 (and block_2_1_0 block_2_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_2_0_0 (not sync_2_0)) (not thread_2_0))) ; barrier 0: thread 0
(assert (=> (and block_2_0_1 (not sync_2_0)) (not thread_2_1))) ; barrier 0: thread 1
(assert (=> (and block_2_1_0 (not sync_2_1)) (not thread_2_0))) ; barrier 1: thread 0
(assert (=> (and block_2_1_1 (not sync_2_1)) (not thread_2_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_0_0 () Bool)
(declare-fun exec_2_0_1 () Bool)
(declare-fun exec_2_0_2 () Bool)
(declare-fun exec_2_0_3 () Bool)
(declare-fun exec_2_0_4 () Bool)
(declare-fun exec_2_0_5 () Bool)
(declare-fun exec_2_0_6 () Bool)
(declare-fun exec_2_0_7 () Bool)

(declare-fun exec_2_1_0 () Bool)
(declare-fun exec_2_1_1 () Bool)
(declare-fun exec_2_1_2 () Bool)
(declare-fun exec_2_1_3 () Bool)
(declare-fun exec_2_1_4 () Bool)
(declare-fun exec_2_1_5 () Bool)
(declare-fun exec_2_1_6 () Bool)

(assert (= exec_2_0_0 (and stmt_2_0_0 thread_2_0)))
(assert (= exec_2_0_1 (and stmt_2_0_1 thread_2_0)))
(assert (= exec_2_0_2 (and stmt_2_0_2 thread_2_0)))
(assert (= exec_2_0_3 (and stmt_2_0_3 thread_2_0)))
(assert (= exec_2_0_4 (and stmt_2_0_4 thread_2_0)))
(assert (= exec_2_0_5 (and stmt_2_0_5 thread_2_0)))
(assert (= exec_2_0_6 (and stmt_2_0_6 thread_2_0)))
(assert (= exec_2_0_7 (and stmt_2_0_7 thread_2_0)))

(assert (= exec_2_1_0 (and stmt_2_1_0 thread_2_1)))
(assert (= exec_2_1_1 (and stmt_2_1_1 thread_2_1)))
(assert (= exec_2_1_2 (and stmt_2_1_2 thread_2_1)))
(assert (= exec_2_1_3 (and stmt_2_1_3 thread_2_1)))
(assert (= exec_2_1_4 (and stmt_2_1_4 thread_2_1)))
(assert (= exec_2_1_5 (and stmt_2_1_5 thread_2_1)))
(assert (= exec_2_1_6 (and stmt_2_1_6 thread_2_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_2_0 () (_ BitVec 16))
(declare-fun accu_2_1 () (_ BitVec 16))

(assert (= accu_2_0 (ite exec_2_0_2 (select heap_1 #x0000) (ite exec_2_0_3 (bvadd accu_1_0 #x0001) accu_1_0))))
(assert (= accu_2_1 (ite exec_2_1_2 (select heap_1 #x0000) (ite exec_2_1_3 (bvadd accu_1_1 #x0001) accu_1_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_2_0 () (_ BitVec 16))
(declare-fun mem_2_1 () (_ BitVec 16))

(assert (= mem_2_0 mem_1_0))
(assert (= mem_2_1 mem_1_1))

; heap states - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_2 (ite exec_2_0_0 (store heap_1 #x0000 accu_1_0) (ite exec_2_0_4 (store heap_1 #x0000 accu_1_0) (ite exec_2_1_4 (store heap_1 #x0000 accu_1_1) heap_1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_3 () Bool)

(assert (= exit_3 (or exit_2 exec_2_0_7 exec_2_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_0_0 () Bool)
(declare-fun stmt_3_0_1 () Bool)
(declare-fun stmt_3_0_2 () Bool)
(declare-fun stmt_3_0_3 () Bool)
(declare-fun stmt_3_0_4 () Bool)
(declare-fun stmt_3_0_5 () Bool)
(declare-fun stmt_3_0_6 () Bool)
(declare-fun stmt_3_0_7 () Bool)

(declare-fun stmt_3_1_0 () Bool)
(declare-fun stmt_3_1_1 () Bool)
(declare-fun stmt_3_1_2 () Bool)
(declare-fun stmt_3_1_3 () Bool)
(declare-fun stmt_3_1_4 () Bool)
(declare-fun stmt_3_1_5 () Bool)
(declare-fun stmt_3_1_6 () Bool)

(assert (= stmt_3_0_0 (and stmt_2_0_0 (not exec_2_0_0))))
(assert (= stmt_3_0_1 (ite stmt_2_0_6 (and exec_2_0_6 (not (= accu_2_0 #x0000))) (ite stmt_2_0_0 exec_2_0_0 (and stmt_2_0_1 (not exec_2_0_1))))))
(assert (= stmt_3_0_2 (ite stmt_2_0_1 exec_2_0_1 (and stmt_2_0_2 (not exec_2_0_2)))))
(assert (= stmt_3_0_3 (ite stmt_2_0_2 exec_2_0_2 (and stmt_2_0_3 (not exec_2_0_3)))))
(assert (= stmt_3_0_4 (ite stmt_2_0_3 exec_2_0_3 (and stmt_2_0_4 (not exec_2_0_4)))))
(assert (= stmt_3_0_5 (ite stmt_2_0_4 exec_2_0_4 (and stmt_2_0_5 (not exec_2_0_5)))))
(assert (= stmt_3_0_6 (ite stmt_2_0_5 exec_2_0_5 (and stmt_2_0_6 (not exec_2_0_6)))))
(assert (= stmt_3_0_7 (ite stmt_2_0_6 (and exec_2_0_6 (not (not (= accu_2_0 #x0000)))) (and stmt_2_0_7 (not exec_2_0_7)))))

(assert (= stmt_3_1_0 (ite stmt_2_1_5 (and exec_2_1_5 (not (= accu_2_1 #x0000))) (and stmt_2_1_0 (not exec_2_1_0)))))
(assert (= stmt_3_1_1 (ite stmt_2_1_0 exec_2_1_0 (and stmt_2_1_1 (not exec_2_1_1)))))
(assert (= stmt_3_1_2 (ite stmt_2_1_1 exec_2_1_1 (and stmt_2_1_2 (not exec_2_1_2)))))
(assert (= stmt_3_1_3 (ite stmt_2_1_2 exec_2_1_2 (and stmt_2_1_3 (not exec_2_1_3)))))
(assert (= stmt_3_1_4 (ite stmt_2_1_3 exec_2_1_3 (and stmt_2_1_4 (not exec_2_1_4)))))
(assert (= stmt_3_1_5 (ite stmt_2_1_4 exec_2_1_4 (and stmt_2_1_5 (not exec_2_1_5)))))
(assert (= stmt_3_1_6 (ite stmt_2_1_5 (and exec_2_1_5 (not (not (= accu_2_1 #x0000)))) (and stmt_2_1_6 (not exec_2_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_0 () Bool)
(declare-fun thread_3_1 () Bool)

(assert (or thread_3_0 thread_3_1 exit_3))
(assert (or (not thread_3_0) (not thread_3_1)))
(assert (or (not thread_3_0) (not exit_3)))
(assert (or (not thread_3_1) (not exit_3)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_3_0_0 () Bool)
(declare-fun block_3_0_1 () Bool)
(declare-fun block_3_1_0 () Bool)
(declare-fun block_3_1_1 () Bool)

(assert (= block_3_0_0 (ite sync_2_0 false (or exec_2_0_1 block_2_0_0))))
(assert (= block_3_0_1 (ite sync_2_0 false (or exec_2_1_0 block_2_0_1))))
(assert (= block_3_1_0 (ite sync_2_1 false (or exec_2_0_5 block_2_1_0))))
(assert (= block_3_1_1 (ite sync_2_1 false (or exec_2_1_1 block_2_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_3_0 () Bool)
(declare-fun sync_3_1 () Bool)

(assert (= sync_3_0 (and block_3_0_0 block_3_0_1)))
(assert (= sync_3_1 (and block_3_1_0 block_3_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_3_0_0 (not sync_3_0)) (not thread_3_0))) ; barrier 0: thread 0
(assert (=> (and block_3_0_1 (not sync_3_0)) (not thread_3_1))) ; barrier 0: thread 1
(assert (=> (and block_3_1_0 (not sync_3_1)) (not thread_3_0))) ; barrier 1: thread 0
(assert (=> (and block_3_1_1 (not sync_3_1)) (not thread_3_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_0_0 () Bool)
(declare-fun exec_3_0_1 () Bool)
(declare-fun exec_3_0_2 () Bool)
(declare-fun exec_3_0_3 () Bool)
(declare-fun exec_3_0_4 () Bool)
(declare-fun exec_3_0_5 () Bool)
(declare-fun exec_3_0_6 () Bool)
(declare-fun exec_3_0_7 () Bool)

(declare-fun exec_3_1_0 () Bool)
(declare-fun exec_3_1_1 () Bool)
(declare-fun exec_3_1_2 () Bool)
(declare-fun exec_3_1_3 () Bool)
(declare-fun exec_3_1_4 () Bool)
(declare-fun exec_3_1_5 () Bool)
(declare-fun exec_3_1_6 () Bool)

(assert (= exec_3_0_0 (and stmt_3_0_0 thread_3_0)))
(assert (= exec_3_0_1 (and stmt_3_0_1 thread_3_0)))
(assert (= exec_3_0_2 (and stmt_3_0_2 thread_3_0)))
(assert (= exec_3_0_3 (and stmt_3_0_3 thread_3_0)))
(assert (= exec_3_0_4 (and stmt_3_0_4 thread_3_0)))
(assert (= exec_3_0_5 (and stmt_3_0_5 thread_3_0)))
(assert (= exec_3_0_6 (and stmt_3_0_6 thread_3_0)))
(assert (= exec_3_0_7 (and stmt_3_0_7 thread_3_0)))

(assert (= exec_3_1_0 (and stmt_3_1_0 thread_3_1)))
(assert (= exec_3_1_1 (and stmt_3_1_1 thread_3_1)))
(assert (= exec_3_1_2 (and stmt_3_1_2 thread_3_1)))
(assert (= exec_3_1_3 (and stmt_3_1_3 thread_3_1)))
(assert (= exec_3_1_4 (and stmt_3_1_4 thread_3_1)))
(assert (= exec_3_1_5 (and stmt_3_1_5 thread_3_1)))
(assert (= exec_3_1_6 (and stmt_3_1_6 thread_3_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_3_0 () (_ BitVec 16))
(declare-fun accu_3_1 () (_ BitVec 16))

(assert (= accu_3_0 (ite exec_3_0_2 (select heap_2 #x0000) (ite exec_3_0_3 (bvadd accu_2_0 #x0001) accu_2_0))))
(assert (= accu_3_1 (ite exec_3_1_2 (select heap_2 #x0000) (ite exec_3_1_3 (bvadd accu_2_1 #x0001) accu_2_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_3_0 () (_ BitVec 16))
(declare-fun mem_3_1 () (_ BitVec 16))

(assert (= mem_3_0 mem_2_0))
(assert (= mem_3_1 mem_2_1))

; heap states - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_3 (ite exec_3_0_0 (store heap_2 #x0000 accu_2_0) (ite exec_3_0_4 (store heap_2 #x0000 accu_2_0) (ite exec_3_1_4 (store heap_2 #x0000 accu_2_1) heap_2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_4 () Bool)

(assert (= exit_4 (or exit_3 exec_3_0_7 exec_3_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_0_0 () Bool)
(declare-fun stmt_4_0_1 () Bool)
(declare-fun stmt_4_0_2 () Bool)
(declare-fun stmt_4_0_3 () Bool)
(declare-fun stmt_4_0_4 () Bool)
(declare-fun stmt_4_0_5 () Bool)
(declare-fun stmt_4_0_6 () Bool)
(declare-fun stmt_4_0_7 () Bool)

(declare-fun stmt_4_1_0 () Bool)
(declare-fun stmt_4_1_1 () Bool)
(declare-fun stmt_4_1_2 () Bool)
(declare-fun stmt_4_1_3 () Bool)
(declare-fun stmt_4_1_4 () Bool)
(declare-fun stmt_4_1_5 () Bool)
(declare-fun stmt_4_1_6 () Bool)

(assert (= stmt_4_0_0 (and stmt_3_0_0 (not exec_3_0_0))))
(assert (= stmt_4_0_1 (ite stmt_3_0_6 (and exec_3_0_6 (not (= accu_3_0 #x0000))) (ite stmt_3_0_0 exec_3_0_0 (and stmt_3_0_1 (not exec_3_0_1))))))
(assert (= stmt_4_0_2 (ite stmt_3_0_1 exec_3_0_1 (and stmt_3_0_2 (not exec_3_0_2)))))
(assert (= stmt_4_0_3 (ite stmt_3_0_2 exec_3_0_2 (and stmt_3_0_3 (not exec_3_0_3)))))
(assert (= stmt_4_0_4 (ite stmt_3_0_3 exec_3_0_3 (and stmt_3_0_4 (not exec_3_0_4)))))
(assert (= stmt_4_0_5 (ite stmt_3_0_4 exec_3_0_4 (and stmt_3_0_5 (not exec_3_0_5)))))
(assert (= stmt_4_0_6 (ite stmt_3_0_5 exec_3_0_5 (and stmt_3_0_6 (not exec_3_0_6)))))
(assert (= stmt_4_0_7 (ite stmt_3_0_6 (and exec_3_0_6 (not (not (= accu_3_0 #x0000)))) (and stmt_3_0_7 (not exec_3_0_7)))))

(assert (= stmt_4_1_0 (ite stmt_3_1_5 (and exec_3_1_5 (not (= accu_3_1 #x0000))) (and stmt_3_1_0 (not exec_3_1_0)))))
(assert (= stmt_4_1_1 (ite stmt_3_1_0 exec_3_1_0 (and stmt_3_1_1 (not exec_3_1_1)))))
(assert (= stmt_4_1_2 (ite stmt_3_1_1 exec_3_1_1 (and stmt_3_1_2 (not exec_3_1_2)))))
(assert (= stmt_4_1_3 (ite stmt_3_1_2 exec_3_1_2 (and stmt_3_1_3 (not exec_3_1_3)))))
(assert (= stmt_4_1_4 (ite stmt_3_1_3 exec_3_1_3 (and stmt_3_1_4 (not exec_3_1_4)))))
(assert (= stmt_4_1_5 (ite stmt_3_1_4 exec_3_1_4 (and stmt_3_1_5 (not exec_3_1_5)))))
(assert (= stmt_4_1_6 (ite stmt_3_1_5 (and exec_3_1_5 (not (not (= accu_3_1 #x0000)))) (and stmt_3_1_6 (not exec_3_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_0 () Bool)
(declare-fun thread_4_1 () Bool)

(assert (or thread_4_0 thread_4_1 exit_4))
(assert (or (not thread_4_0) (not thread_4_1)))
(assert (or (not thread_4_0) (not exit_4)))
(assert (or (not thread_4_1) (not exit_4)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_4_0_0 () Bool)
(declare-fun block_4_0_1 () Bool)
(declare-fun block_4_1_0 () Bool)
(declare-fun block_4_1_1 () Bool)

(assert (= block_4_0_0 (ite sync_3_0 false (or exec_3_0_1 block_3_0_0))))
(assert (= block_4_0_1 (ite sync_3_0 false (or exec_3_1_0 block_3_0_1))))
(assert (= block_4_1_0 (ite sync_3_1 false (or exec_3_0_5 block_3_1_0))))
(assert (= block_4_1_1 (ite sync_3_1 false (or exec_3_1_1 block_3_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_4_0 () Bool)
(declare-fun sync_4_1 () Bool)

(assert (= sync_4_0 (and block_4_0_0 block_4_0_1)))
(assert (= sync_4_1 (and block_4_1_0 block_4_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_4_0_0 (not sync_4_0)) (not thread_4_0))) ; barrier 0: thread 0
(assert (=> (and block_4_0_1 (not sync_4_0)) (not thread_4_1))) ; barrier 0: thread 1
(assert (=> (and block_4_1_0 (not sync_4_1)) (not thread_4_0))) ; barrier 1: thread 0
(assert (=> (and block_4_1_1 (not sync_4_1)) (not thread_4_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_0_0 () Bool)
(declare-fun exec_4_0_1 () Bool)
(declare-fun exec_4_0_2 () Bool)
(declare-fun exec_4_0_3 () Bool)
(declare-fun exec_4_0_4 () Bool)
(declare-fun exec_4_0_5 () Bool)
(declare-fun exec_4_0_6 () Bool)
(declare-fun exec_4_0_7 () Bool)

(declare-fun exec_4_1_0 () Bool)
(declare-fun exec_4_1_1 () Bool)
(declare-fun exec_4_1_2 () Bool)
(declare-fun exec_4_1_3 () Bool)
(declare-fun exec_4_1_4 () Bool)
(declare-fun exec_4_1_5 () Bool)
(declare-fun exec_4_1_6 () Bool)

(assert (= exec_4_0_0 (and stmt_4_0_0 thread_4_0)))
(assert (= exec_4_0_1 (and stmt_4_0_1 thread_4_0)))
(assert (= exec_4_0_2 (and stmt_4_0_2 thread_4_0)))
(assert (= exec_4_0_3 (and stmt_4_0_3 thread_4_0)))
(assert (= exec_4_0_4 (and stmt_4_0_4 thread_4_0)))
(assert (= exec_4_0_5 (and stmt_4_0_5 thread_4_0)))
(assert (= exec_4_0_6 (and stmt_4_0_6 thread_4_0)))
(assert (= exec_4_0_7 (and stmt_4_0_7 thread_4_0)))

(assert (= exec_4_1_0 (and stmt_4_1_0 thread_4_1)))
(assert (= exec_4_1_1 (and stmt_4_1_1 thread_4_1)))
(assert (= exec_4_1_2 (and stmt_4_1_2 thread_4_1)))
(assert (= exec_4_1_3 (and stmt_4_1_3 thread_4_1)))
(assert (= exec_4_1_4 (and stmt_4_1_4 thread_4_1)))
(assert (= exec_4_1_5 (and stmt_4_1_5 thread_4_1)))
(assert (= exec_4_1_6 (and stmt_4_1_6 thread_4_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_4_0 () (_ BitVec 16))
(declare-fun accu_4_1 () (_ BitVec 16))

(assert (= accu_4_0 (ite exec_4_0_2 (select heap_3 #x0000) (ite exec_4_0_3 (bvadd accu_3_0 #x0001) accu_3_0))))
(assert (= accu_4_1 (ite exec_4_1_2 (select heap_3 #x0000) (ite exec_4_1_3 (bvadd accu_3_1 #x0001) accu_3_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_4_0 () (_ BitVec 16))
(declare-fun mem_4_1 () (_ BitVec 16))

(assert (= mem_4_0 mem_3_0))
(assert (= mem_4_1 mem_3_1))

; heap states - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_4 (ite exec_4_0_0 (store heap_3 #x0000 accu_3_0) (ite exec_4_0_4 (store heap_3 #x0000 accu_3_0) (ite exec_4_1_4 (store heap_3 #x0000 accu_3_1) heap_3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_5 () Bool)

(assert (= exit_5 (or exit_4 exec_4_0_7 exec_4_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_0_0 () Bool)
(declare-fun stmt_5_0_1 () Bool)
(declare-fun stmt_5_0_2 () Bool)
(declare-fun stmt_5_0_3 () Bool)
(declare-fun stmt_5_0_4 () Bool)
(declare-fun stmt_5_0_5 () Bool)
(declare-fun stmt_5_0_6 () Bool)
(declare-fun stmt_5_0_7 () Bool)

(declare-fun stmt_5_1_0 () Bool)
(declare-fun stmt_5_1_1 () Bool)
(declare-fun stmt_5_1_2 () Bool)
(declare-fun stmt_5_1_3 () Bool)
(declare-fun stmt_5_1_4 () Bool)
(declare-fun stmt_5_1_5 () Bool)
(declare-fun stmt_5_1_6 () Bool)

(assert (= stmt_5_0_0 (and stmt_4_0_0 (not exec_4_0_0))))
(assert (= stmt_5_0_1 (ite stmt_4_0_6 (and exec_4_0_6 (not (= accu_4_0 #x0000))) (ite stmt_4_0_0 exec_4_0_0 (and stmt_4_0_1 (not exec_4_0_1))))))
(assert (= stmt_5_0_2 (ite stmt_4_0_1 exec_4_0_1 (and stmt_4_0_2 (not exec_4_0_2)))))
(assert (= stmt_5_0_3 (ite stmt_4_0_2 exec_4_0_2 (and stmt_4_0_3 (not exec_4_0_3)))))
(assert (= stmt_5_0_4 (ite stmt_4_0_3 exec_4_0_3 (and stmt_4_0_4 (not exec_4_0_4)))))
(assert (= stmt_5_0_5 (ite stmt_4_0_4 exec_4_0_4 (and stmt_4_0_5 (not exec_4_0_5)))))
(assert (= stmt_5_0_6 (ite stmt_4_0_5 exec_4_0_5 (and stmt_4_0_6 (not exec_4_0_6)))))
(assert (= stmt_5_0_7 (ite stmt_4_0_6 (and exec_4_0_6 (not (not (= accu_4_0 #x0000)))) (and stmt_4_0_7 (not exec_4_0_7)))))

(assert (= stmt_5_1_0 (ite stmt_4_1_5 (and exec_4_1_5 (not (= accu_4_1 #x0000))) (and stmt_4_1_0 (not exec_4_1_0)))))
(assert (= stmt_5_1_1 (ite stmt_4_1_0 exec_4_1_0 (and stmt_4_1_1 (not exec_4_1_1)))))
(assert (= stmt_5_1_2 (ite stmt_4_1_1 exec_4_1_1 (and stmt_4_1_2 (not exec_4_1_2)))))
(assert (= stmt_5_1_3 (ite stmt_4_1_2 exec_4_1_2 (and stmt_4_1_3 (not exec_4_1_3)))))
(assert (= stmt_5_1_4 (ite stmt_4_1_3 exec_4_1_3 (and stmt_4_1_4 (not exec_4_1_4)))))
(assert (= stmt_5_1_5 (ite stmt_4_1_4 exec_4_1_4 (and stmt_4_1_5 (not exec_4_1_5)))))
(assert (= stmt_5_1_6 (ite stmt_4_1_5 (and exec_4_1_5 (not (not (= accu_4_1 #x0000)))) (and stmt_4_1_6 (not exec_4_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_0 () Bool)
(declare-fun thread_5_1 () Bool)

(assert (or thread_5_0 thread_5_1 exit_5))
(assert (or (not thread_5_0) (not thread_5_1)))
(assert (or (not thread_5_0) (not exit_5)))
(assert (or (not thread_5_1) (not exit_5)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_5_0_0 () Bool)
(declare-fun block_5_0_1 () Bool)
(declare-fun block_5_1_0 () Bool)
(declare-fun block_5_1_1 () Bool)

(assert (= block_5_0_0 (ite sync_4_0 false (or exec_4_0_1 block_4_0_0))))
(assert (= block_5_0_1 (ite sync_4_0 false (or exec_4_1_0 block_4_0_1))))
(assert (= block_5_1_0 (ite sync_4_1 false (or exec_4_0_5 block_4_1_0))))
(assert (= block_5_1_1 (ite sync_4_1 false (or exec_4_1_1 block_4_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_5_0 () Bool)
(declare-fun sync_5_1 () Bool)

(assert (= sync_5_0 (and block_5_0_0 block_5_0_1)))
(assert (= sync_5_1 (and block_5_1_0 block_5_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_5_0_0 (not sync_5_0)) (not thread_5_0))) ; barrier 0: thread 0
(assert (=> (and block_5_0_1 (not sync_5_0)) (not thread_5_1))) ; barrier 0: thread 1
(assert (=> (and block_5_1_0 (not sync_5_1)) (not thread_5_0))) ; barrier 1: thread 0
(assert (=> (and block_5_1_1 (not sync_5_1)) (not thread_5_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_0_0 () Bool)
(declare-fun exec_5_0_1 () Bool)
(declare-fun exec_5_0_2 () Bool)
(declare-fun exec_5_0_3 () Bool)
(declare-fun exec_5_0_4 () Bool)
(declare-fun exec_5_0_5 () Bool)
(declare-fun exec_5_0_6 () Bool)
(declare-fun exec_5_0_7 () Bool)

(declare-fun exec_5_1_0 () Bool)
(declare-fun exec_5_1_1 () Bool)
(declare-fun exec_5_1_2 () Bool)
(declare-fun exec_5_1_3 () Bool)
(declare-fun exec_5_1_4 () Bool)
(declare-fun exec_5_1_5 () Bool)
(declare-fun exec_5_1_6 () Bool)

(assert (= exec_5_0_0 (and stmt_5_0_0 thread_5_0)))
(assert (= exec_5_0_1 (and stmt_5_0_1 thread_5_0)))
(assert (= exec_5_0_2 (and stmt_5_0_2 thread_5_0)))
(assert (= exec_5_0_3 (and stmt_5_0_3 thread_5_0)))
(assert (= exec_5_0_4 (and stmt_5_0_4 thread_5_0)))
(assert (= exec_5_0_5 (and stmt_5_0_5 thread_5_0)))
(assert (= exec_5_0_6 (and stmt_5_0_6 thread_5_0)))
(assert (= exec_5_0_7 (and stmt_5_0_7 thread_5_0)))

(assert (= exec_5_1_0 (and stmt_5_1_0 thread_5_1)))
(assert (= exec_5_1_1 (and stmt_5_1_1 thread_5_1)))
(assert (= exec_5_1_2 (and stmt_5_1_2 thread_5_1)))
(assert (= exec_5_1_3 (and stmt_5_1_3 thread_5_1)))
(assert (= exec_5_1_4 (and stmt_5_1_4 thread_5_1)))
(assert (= exec_5_1_5 (and stmt_5_1_5 thread_5_1)))
(assert (= exec_5_1_6 (and stmt_5_1_6 thread_5_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_5_0 () (_ BitVec 16))
(declare-fun accu_5_1 () (_ BitVec 16))

(assert (= accu_5_0 (ite exec_5_0_2 (select heap_4 #x0000) (ite exec_5_0_3 (bvadd accu_4_0 #x0001) accu_4_0))))
(assert (= accu_5_1 (ite exec_5_1_2 (select heap_4 #x0000) (ite exec_5_1_3 (bvadd accu_4_1 #x0001) accu_4_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_5_0 () (_ BitVec 16))
(declare-fun mem_5_1 () (_ BitVec 16))

(assert (= mem_5_0 mem_4_0))
(assert (= mem_5_1 mem_4_1))

; heap states - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_5 (ite exec_5_0_0 (store heap_4 #x0000 accu_4_0) (ite exec_5_0_4 (store heap_4 #x0000 accu_4_0) (ite exec_5_1_4 (store heap_4 #x0000 accu_4_1) heap_4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_6 () Bool)

(assert (= exit_6 (or exit_5 exec_5_0_7 exec_5_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_0_0 () Bool)
(declare-fun stmt_6_0_1 () Bool)
(declare-fun stmt_6_0_2 () Bool)
(declare-fun stmt_6_0_3 () Bool)
(declare-fun stmt_6_0_4 () Bool)
(declare-fun stmt_6_0_5 () Bool)
(declare-fun stmt_6_0_6 () Bool)
(declare-fun stmt_6_0_7 () Bool)

(declare-fun stmt_6_1_0 () Bool)
(declare-fun stmt_6_1_1 () Bool)
(declare-fun stmt_6_1_2 () Bool)
(declare-fun stmt_6_1_3 () Bool)
(declare-fun stmt_6_1_4 () Bool)
(declare-fun stmt_6_1_5 () Bool)
(declare-fun stmt_6_1_6 () Bool)

(assert (= stmt_6_0_0 (and stmt_5_0_0 (not exec_5_0_0))))
(assert (= stmt_6_0_1 (ite stmt_5_0_6 (and exec_5_0_6 (not (= accu_5_0 #x0000))) (ite stmt_5_0_0 exec_5_0_0 (and stmt_5_0_1 (not exec_5_0_1))))))
(assert (= stmt_6_0_2 (ite stmt_5_0_1 exec_5_0_1 (and stmt_5_0_2 (not exec_5_0_2)))))
(assert (= stmt_6_0_3 (ite stmt_5_0_2 exec_5_0_2 (and stmt_5_0_3 (not exec_5_0_3)))))
(assert (= stmt_6_0_4 (ite stmt_5_0_3 exec_5_0_3 (and stmt_5_0_4 (not exec_5_0_4)))))
(assert (= stmt_6_0_5 (ite stmt_5_0_4 exec_5_0_4 (and stmt_5_0_5 (not exec_5_0_5)))))
(assert (= stmt_6_0_6 (ite stmt_5_0_5 exec_5_0_5 (and stmt_5_0_6 (not exec_5_0_6)))))
(assert (= stmt_6_0_7 (ite stmt_5_0_6 (and exec_5_0_6 (not (not (= accu_5_0 #x0000)))) (and stmt_5_0_7 (not exec_5_0_7)))))

(assert (= stmt_6_1_0 (ite stmt_5_1_5 (and exec_5_1_5 (not (= accu_5_1 #x0000))) (and stmt_5_1_0 (not exec_5_1_0)))))
(assert (= stmt_6_1_1 (ite stmt_5_1_0 exec_5_1_0 (and stmt_5_1_1 (not exec_5_1_1)))))
(assert (= stmt_6_1_2 (ite stmt_5_1_1 exec_5_1_1 (and stmt_5_1_2 (not exec_5_1_2)))))
(assert (= stmt_6_1_3 (ite stmt_5_1_2 exec_5_1_2 (and stmt_5_1_3 (not exec_5_1_3)))))
(assert (= stmt_6_1_4 (ite stmt_5_1_3 exec_5_1_3 (and stmt_5_1_4 (not exec_5_1_4)))))
(assert (= stmt_6_1_5 (ite stmt_5_1_4 exec_5_1_4 (and stmt_5_1_5 (not exec_5_1_5)))))
(assert (= stmt_6_1_6 (ite stmt_5_1_5 (and exec_5_1_5 (not (not (= accu_5_1 #x0000)))) (and stmt_5_1_6 (not exec_5_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_0 () Bool)
(declare-fun thread_6_1 () Bool)

(assert (or thread_6_0 thread_6_1 exit_6))
(assert (or (not thread_6_0) (not thread_6_1)))
(assert (or (not thread_6_0) (not exit_6)))
(assert (or (not thread_6_1) (not exit_6)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_6_0_0 () Bool)
(declare-fun block_6_0_1 () Bool)
(declare-fun block_6_1_0 () Bool)
(declare-fun block_6_1_1 () Bool)

(assert (= block_6_0_0 (ite sync_5_0 false (or exec_5_0_1 block_5_0_0))))
(assert (= block_6_0_1 (ite sync_5_0 false (or exec_5_1_0 block_5_0_1))))
(assert (= block_6_1_0 (ite sync_5_1 false (or exec_5_0_5 block_5_1_0))))
(assert (= block_6_1_1 (ite sync_5_1 false (or exec_5_1_1 block_5_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_6_0 () Bool)
(declare-fun sync_6_1 () Bool)

(assert (= sync_6_0 (and block_6_0_0 block_6_0_1)))
(assert (= sync_6_1 (and block_6_1_0 block_6_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_6_0_0 (not sync_6_0)) (not thread_6_0))) ; barrier 0: thread 0
(assert (=> (and block_6_0_1 (not sync_6_0)) (not thread_6_1))) ; barrier 0: thread 1
(assert (=> (and block_6_1_0 (not sync_6_1)) (not thread_6_0))) ; barrier 1: thread 0
(assert (=> (and block_6_1_1 (not sync_6_1)) (not thread_6_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_0_0 () Bool)
(declare-fun exec_6_0_1 () Bool)
(declare-fun exec_6_0_2 () Bool)
(declare-fun exec_6_0_3 () Bool)
(declare-fun exec_6_0_4 () Bool)
(declare-fun exec_6_0_5 () Bool)
(declare-fun exec_6_0_6 () Bool)
(declare-fun exec_6_0_7 () Bool)

(declare-fun exec_6_1_0 () Bool)
(declare-fun exec_6_1_1 () Bool)
(declare-fun exec_6_1_2 () Bool)
(declare-fun exec_6_1_3 () Bool)
(declare-fun exec_6_1_4 () Bool)
(declare-fun exec_6_1_5 () Bool)
(declare-fun exec_6_1_6 () Bool)

(assert (= exec_6_0_0 (and stmt_6_0_0 thread_6_0)))
(assert (= exec_6_0_1 (and stmt_6_0_1 thread_6_0)))
(assert (= exec_6_0_2 (and stmt_6_0_2 thread_6_0)))
(assert (= exec_6_0_3 (and stmt_6_0_3 thread_6_0)))
(assert (= exec_6_0_4 (and stmt_6_0_4 thread_6_0)))
(assert (= exec_6_0_5 (and stmt_6_0_5 thread_6_0)))
(assert (= exec_6_0_6 (and stmt_6_0_6 thread_6_0)))
(assert (= exec_6_0_7 (and stmt_6_0_7 thread_6_0)))

(assert (= exec_6_1_0 (and stmt_6_1_0 thread_6_1)))
(assert (= exec_6_1_1 (and stmt_6_1_1 thread_6_1)))
(assert (= exec_6_1_2 (and stmt_6_1_2 thread_6_1)))
(assert (= exec_6_1_3 (and stmt_6_1_3 thread_6_1)))
(assert (= exec_6_1_4 (and stmt_6_1_4 thread_6_1)))
(assert (= exec_6_1_5 (and stmt_6_1_5 thread_6_1)))
(assert (= exec_6_1_6 (and stmt_6_1_6 thread_6_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_6_0 () (_ BitVec 16))
(declare-fun accu_6_1 () (_ BitVec 16))

(assert (= accu_6_0 (ite exec_6_0_2 (select heap_5 #x0000) (ite exec_6_0_3 (bvadd accu_5_0 #x0001) accu_5_0))))
(assert (= accu_6_1 (ite exec_6_1_2 (select heap_5 #x0000) (ite exec_6_1_3 (bvadd accu_5_1 #x0001) accu_5_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_6_0 () (_ BitVec 16))
(declare-fun mem_6_1 () (_ BitVec 16))

(assert (= mem_6_0 mem_5_0))
(assert (= mem_6_1 mem_5_1))

; heap states - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_6 (ite exec_6_0_0 (store heap_5 #x0000 accu_5_0) (ite exec_6_0_4 (store heap_5 #x0000 accu_5_0) (ite exec_6_1_4 (store heap_5 #x0000 accu_5_1) heap_5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_7 () Bool)

(assert (= exit_7 (or exit_6 exec_6_0_7 exec_6_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_0_0 () Bool)
(declare-fun stmt_7_0_1 () Bool)
(declare-fun stmt_7_0_2 () Bool)
(declare-fun stmt_7_0_3 () Bool)
(declare-fun stmt_7_0_4 () Bool)
(declare-fun stmt_7_0_5 () Bool)
(declare-fun stmt_7_0_6 () Bool)
(declare-fun stmt_7_0_7 () Bool)

(declare-fun stmt_7_1_0 () Bool)
(declare-fun stmt_7_1_1 () Bool)
(declare-fun stmt_7_1_2 () Bool)
(declare-fun stmt_7_1_3 () Bool)
(declare-fun stmt_7_1_4 () Bool)
(declare-fun stmt_7_1_5 () Bool)
(declare-fun stmt_7_1_6 () Bool)

(assert (= stmt_7_0_0 (and stmt_6_0_0 (not exec_6_0_0))))
(assert (= stmt_7_0_1 (ite stmt_6_0_6 (and exec_6_0_6 (not (= accu_6_0 #x0000))) (ite stmt_6_0_0 exec_6_0_0 (and stmt_6_0_1 (not exec_6_0_1))))))
(assert (= stmt_7_0_2 (ite stmt_6_0_1 exec_6_0_1 (and stmt_6_0_2 (not exec_6_0_2)))))
(assert (= stmt_7_0_3 (ite stmt_6_0_2 exec_6_0_2 (and stmt_6_0_3 (not exec_6_0_3)))))
(assert (= stmt_7_0_4 (ite stmt_6_0_3 exec_6_0_3 (and stmt_6_0_4 (not exec_6_0_4)))))
(assert (= stmt_7_0_5 (ite stmt_6_0_4 exec_6_0_4 (and stmt_6_0_5 (not exec_6_0_5)))))
(assert (= stmt_7_0_6 (ite stmt_6_0_5 exec_6_0_5 (and stmt_6_0_6 (not exec_6_0_6)))))
(assert (= stmt_7_0_7 (ite stmt_6_0_6 (and exec_6_0_6 (not (not (= accu_6_0 #x0000)))) (and stmt_6_0_7 (not exec_6_0_7)))))

(assert (= stmt_7_1_0 (ite stmt_6_1_5 (and exec_6_1_5 (not (= accu_6_1 #x0000))) (and stmt_6_1_0 (not exec_6_1_0)))))
(assert (= stmt_7_1_1 (ite stmt_6_1_0 exec_6_1_0 (and stmt_6_1_1 (not exec_6_1_1)))))
(assert (= stmt_7_1_2 (ite stmt_6_1_1 exec_6_1_1 (and stmt_6_1_2 (not exec_6_1_2)))))
(assert (= stmt_7_1_3 (ite stmt_6_1_2 exec_6_1_2 (and stmt_6_1_3 (not exec_6_1_3)))))
(assert (= stmt_7_1_4 (ite stmt_6_1_3 exec_6_1_3 (and stmt_6_1_4 (not exec_6_1_4)))))
(assert (= stmt_7_1_5 (ite stmt_6_1_4 exec_6_1_4 (and stmt_6_1_5 (not exec_6_1_5)))))
(assert (= stmt_7_1_6 (ite stmt_6_1_5 (and exec_6_1_5 (not (not (= accu_6_1 #x0000)))) (and stmt_6_1_6 (not exec_6_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_0 () Bool)
(declare-fun thread_7_1 () Bool)

(assert (or thread_7_0 thread_7_1 exit_7))
(assert (or (not thread_7_0) (not thread_7_1)))
(assert (or (not thread_7_0) (not exit_7)))
(assert (or (not thread_7_1) (not exit_7)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_7_0_0 () Bool)
(declare-fun block_7_0_1 () Bool)
(declare-fun block_7_1_0 () Bool)
(declare-fun block_7_1_1 () Bool)

(assert (= block_7_0_0 (ite sync_6_0 false (or exec_6_0_1 block_6_0_0))))
(assert (= block_7_0_1 (ite sync_6_0 false (or exec_6_1_0 block_6_0_1))))
(assert (= block_7_1_0 (ite sync_6_1 false (or exec_6_0_5 block_6_1_0))))
(assert (= block_7_1_1 (ite sync_6_1 false (or exec_6_1_1 block_6_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_7_0 () Bool)
(declare-fun sync_7_1 () Bool)

(assert (= sync_7_0 (and block_7_0_0 block_7_0_1)))
(assert (= sync_7_1 (and block_7_1_0 block_7_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_7_0_0 (not sync_7_0)) (not thread_7_0))) ; barrier 0: thread 0
(assert (=> (and block_7_0_1 (not sync_7_0)) (not thread_7_1))) ; barrier 0: thread 1
(assert (=> (and block_7_1_0 (not sync_7_1)) (not thread_7_0))) ; barrier 1: thread 0
(assert (=> (and block_7_1_1 (not sync_7_1)) (not thread_7_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_0_0 () Bool)
(declare-fun exec_7_0_1 () Bool)
(declare-fun exec_7_0_2 () Bool)
(declare-fun exec_7_0_3 () Bool)
(declare-fun exec_7_0_4 () Bool)
(declare-fun exec_7_0_5 () Bool)
(declare-fun exec_7_0_6 () Bool)
(declare-fun exec_7_0_7 () Bool)

(declare-fun exec_7_1_0 () Bool)
(declare-fun exec_7_1_1 () Bool)
(declare-fun exec_7_1_2 () Bool)
(declare-fun exec_7_1_3 () Bool)
(declare-fun exec_7_1_4 () Bool)
(declare-fun exec_7_1_5 () Bool)
(declare-fun exec_7_1_6 () Bool)

(assert (= exec_7_0_0 (and stmt_7_0_0 thread_7_0)))
(assert (= exec_7_0_1 (and stmt_7_0_1 thread_7_0)))
(assert (= exec_7_0_2 (and stmt_7_0_2 thread_7_0)))
(assert (= exec_7_0_3 (and stmt_7_0_3 thread_7_0)))
(assert (= exec_7_0_4 (and stmt_7_0_4 thread_7_0)))
(assert (= exec_7_0_5 (and stmt_7_0_5 thread_7_0)))
(assert (= exec_7_0_6 (and stmt_7_0_6 thread_7_0)))
(assert (= exec_7_0_7 (and stmt_7_0_7 thread_7_0)))

(assert (= exec_7_1_0 (and stmt_7_1_0 thread_7_1)))
(assert (= exec_7_1_1 (and stmt_7_1_1 thread_7_1)))
(assert (= exec_7_1_2 (and stmt_7_1_2 thread_7_1)))
(assert (= exec_7_1_3 (and stmt_7_1_3 thread_7_1)))
(assert (= exec_7_1_4 (and stmt_7_1_4 thread_7_1)))
(assert (= exec_7_1_5 (and stmt_7_1_5 thread_7_1)))
(assert (= exec_7_1_6 (and stmt_7_1_6 thread_7_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_7_0 () (_ BitVec 16))
(declare-fun accu_7_1 () (_ BitVec 16))

(assert (= accu_7_0 (ite exec_7_0_2 (select heap_6 #x0000) (ite exec_7_0_3 (bvadd accu_6_0 #x0001) accu_6_0))))
(assert (= accu_7_1 (ite exec_7_1_2 (select heap_6 #x0000) (ite exec_7_1_3 (bvadd accu_6_1 #x0001) accu_6_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_7_0 () (_ BitVec 16))
(declare-fun mem_7_1 () (_ BitVec 16))

(assert (= mem_7_0 mem_6_0))
(assert (= mem_7_1 mem_6_1))

; heap states - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_7 (ite exec_7_0_0 (store heap_6 #x0000 accu_6_0) (ite exec_7_0_4 (store heap_6 #x0000 accu_6_0) (ite exec_7_1_4 (store heap_6 #x0000 accu_6_1) heap_6)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_8 () Bool)

(assert (= exit_8 (or exit_7 exec_7_0_7 exec_7_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_0_0 () Bool)
(declare-fun stmt_8_0_1 () Bool)
(declare-fun stmt_8_0_2 () Bool)
(declare-fun stmt_8_0_3 () Bool)
(declare-fun stmt_8_0_4 () Bool)
(declare-fun stmt_8_0_5 () Bool)
(declare-fun stmt_8_0_6 () Bool)
(declare-fun stmt_8_0_7 () Bool)

(declare-fun stmt_8_1_0 () Bool)
(declare-fun stmt_8_1_1 () Bool)
(declare-fun stmt_8_1_2 () Bool)
(declare-fun stmt_8_1_3 () Bool)
(declare-fun stmt_8_1_4 () Bool)
(declare-fun stmt_8_1_5 () Bool)
(declare-fun stmt_8_1_6 () Bool)

(assert (= stmt_8_0_0 (and stmt_7_0_0 (not exec_7_0_0))))
(assert (= stmt_8_0_1 (ite stmt_7_0_6 (and exec_7_0_6 (not (= accu_7_0 #x0000))) (ite stmt_7_0_0 exec_7_0_0 (and stmt_7_0_1 (not exec_7_0_1))))))
(assert (= stmt_8_0_2 (ite stmt_7_0_1 exec_7_0_1 (and stmt_7_0_2 (not exec_7_0_2)))))
(assert (= stmt_8_0_3 (ite stmt_7_0_2 exec_7_0_2 (and stmt_7_0_3 (not exec_7_0_3)))))
(assert (= stmt_8_0_4 (ite stmt_7_0_3 exec_7_0_3 (and stmt_7_0_4 (not exec_7_0_4)))))
(assert (= stmt_8_0_5 (ite stmt_7_0_4 exec_7_0_4 (and stmt_7_0_5 (not exec_7_0_5)))))
(assert (= stmt_8_0_6 (ite stmt_7_0_5 exec_7_0_5 (and stmt_7_0_6 (not exec_7_0_6)))))
(assert (= stmt_8_0_7 (ite stmt_7_0_6 (and exec_7_0_6 (not (not (= accu_7_0 #x0000)))) (and stmt_7_0_7 (not exec_7_0_7)))))

(assert (= stmt_8_1_0 (ite stmt_7_1_5 (and exec_7_1_5 (not (= accu_7_1 #x0000))) (and stmt_7_1_0 (not exec_7_1_0)))))
(assert (= stmt_8_1_1 (ite stmt_7_1_0 exec_7_1_0 (and stmt_7_1_1 (not exec_7_1_1)))))
(assert (= stmt_8_1_2 (ite stmt_7_1_1 exec_7_1_1 (and stmt_7_1_2 (not exec_7_1_2)))))
(assert (= stmt_8_1_3 (ite stmt_7_1_2 exec_7_1_2 (and stmt_7_1_3 (not exec_7_1_3)))))
(assert (= stmt_8_1_4 (ite stmt_7_1_3 exec_7_1_3 (and stmt_7_1_4 (not exec_7_1_4)))))
(assert (= stmt_8_1_5 (ite stmt_7_1_4 exec_7_1_4 (and stmt_7_1_5 (not exec_7_1_5)))))
(assert (= stmt_8_1_6 (ite stmt_7_1_5 (and exec_7_1_5 (not (not (= accu_7_1 #x0000)))) (and stmt_7_1_6 (not exec_7_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_0 () Bool)
(declare-fun thread_8_1 () Bool)

(assert (or thread_8_0 thread_8_1 exit_8))
(assert (or (not thread_8_0) (not thread_8_1)))
(assert (or (not thread_8_0) (not exit_8)))
(assert (or (not thread_8_1) (not exit_8)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_8_0_0 () Bool)
(declare-fun block_8_0_1 () Bool)
(declare-fun block_8_1_0 () Bool)
(declare-fun block_8_1_1 () Bool)

(assert (= block_8_0_0 (ite sync_7_0 false (or exec_7_0_1 block_7_0_0))))
(assert (= block_8_0_1 (ite sync_7_0 false (or exec_7_1_0 block_7_0_1))))
(assert (= block_8_1_0 (ite sync_7_1 false (or exec_7_0_5 block_7_1_0))))
(assert (= block_8_1_1 (ite sync_7_1 false (or exec_7_1_1 block_7_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_8_0 () Bool)
(declare-fun sync_8_1 () Bool)

(assert (= sync_8_0 (and block_8_0_0 block_8_0_1)))
(assert (= sync_8_1 (and block_8_1_0 block_8_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_8_0_0 (not sync_8_0)) (not thread_8_0))) ; barrier 0: thread 0
(assert (=> (and block_8_0_1 (not sync_8_0)) (not thread_8_1))) ; barrier 0: thread 1
(assert (=> (and block_8_1_0 (not sync_8_1)) (not thread_8_0))) ; barrier 1: thread 0
(assert (=> (and block_8_1_1 (not sync_8_1)) (not thread_8_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_0_0 () Bool)
(declare-fun exec_8_0_1 () Bool)
(declare-fun exec_8_0_2 () Bool)
(declare-fun exec_8_0_3 () Bool)
(declare-fun exec_8_0_4 () Bool)
(declare-fun exec_8_0_5 () Bool)
(declare-fun exec_8_0_6 () Bool)
(declare-fun exec_8_0_7 () Bool)

(declare-fun exec_8_1_0 () Bool)
(declare-fun exec_8_1_1 () Bool)
(declare-fun exec_8_1_2 () Bool)
(declare-fun exec_8_1_3 () Bool)
(declare-fun exec_8_1_4 () Bool)
(declare-fun exec_8_1_5 () Bool)
(declare-fun exec_8_1_6 () Bool)

(assert (= exec_8_0_0 (and stmt_8_0_0 thread_8_0)))
(assert (= exec_8_0_1 (and stmt_8_0_1 thread_8_0)))
(assert (= exec_8_0_2 (and stmt_8_0_2 thread_8_0)))
(assert (= exec_8_0_3 (and stmt_8_0_3 thread_8_0)))
(assert (= exec_8_0_4 (and stmt_8_0_4 thread_8_0)))
(assert (= exec_8_0_5 (and stmt_8_0_5 thread_8_0)))
(assert (= exec_8_0_6 (and stmt_8_0_6 thread_8_0)))
(assert (= exec_8_0_7 (and stmt_8_0_7 thread_8_0)))

(assert (= exec_8_1_0 (and stmt_8_1_0 thread_8_1)))
(assert (= exec_8_1_1 (and stmt_8_1_1 thread_8_1)))
(assert (= exec_8_1_2 (and stmt_8_1_2 thread_8_1)))
(assert (= exec_8_1_3 (and stmt_8_1_3 thread_8_1)))
(assert (= exec_8_1_4 (and stmt_8_1_4 thread_8_1)))
(assert (= exec_8_1_5 (and stmt_8_1_5 thread_8_1)))
(assert (= exec_8_1_6 (and stmt_8_1_6 thread_8_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_8_0 () (_ BitVec 16))
(declare-fun accu_8_1 () (_ BitVec 16))

(assert (= accu_8_0 (ite exec_8_0_2 (select heap_7 #x0000) (ite exec_8_0_3 (bvadd accu_7_0 #x0001) accu_7_0))))
(assert (= accu_8_1 (ite exec_8_1_2 (select heap_7 #x0000) (ite exec_8_1_3 (bvadd accu_7_1 #x0001) accu_7_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_8_0 () (_ BitVec 16))
(declare-fun mem_8_1 () (_ BitVec 16))

(assert (= mem_8_0 mem_7_0))
(assert (= mem_8_1 mem_7_1))

; heap states - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_8 (ite exec_8_0_0 (store heap_7 #x0000 accu_7_0) (ite exec_8_0_4 (store heap_7 #x0000 accu_7_0) (ite exec_8_1_4 (store heap_7 #x0000 accu_7_1) heap_7)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_9 () Bool)

(assert (= exit_9 (or exit_8 exec_8_0_7 exec_8_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_9_0_0 () Bool)
(declare-fun stmt_9_0_1 () Bool)
(declare-fun stmt_9_0_2 () Bool)
(declare-fun stmt_9_0_3 () Bool)
(declare-fun stmt_9_0_4 () Bool)
(declare-fun stmt_9_0_5 () Bool)
(declare-fun stmt_9_0_6 () Bool)
(declare-fun stmt_9_0_7 () Bool)

(declare-fun stmt_9_1_0 () Bool)
(declare-fun stmt_9_1_1 () Bool)
(declare-fun stmt_9_1_2 () Bool)
(declare-fun stmt_9_1_3 () Bool)
(declare-fun stmt_9_1_4 () Bool)
(declare-fun stmt_9_1_5 () Bool)
(declare-fun stmt_9_1_6 () Bool)

(assert (= stmt_9_0_0 (and stmt_8_0_0 (not exec_8_0_0))))
(assert (= stmt_9_0_1 (ite stmt_8_0_6 (and exec_8_0_6 (not (= accu_8_0 #x0000))) (ite stmt_8_0_0 exec_8_0_0 (and stmt_8_0_1 (not exec_8_0_1))))))
(assert (= stmt_9_0_2 (ite stmt_8_0_1 exec_8_0_1 (and stmt_8_0_2 (not exec_8_0_2)))))
(assert (= stmt_9_0_3 (ite stmt_8_0_2 exec_8_0_2 (and stmt_8_0_3 (not exec_8_0_3)))))
(assert (= stmt_9_0_4 (ite stmt_8_0_3 exec_8_0_3 (and stmt_8_0_4 (not exec_8_0_4)))))
(assert (= stmt_9_0_5 (ite stmt_8_0_4 exec_8_0_4 (and stmt_8_0_5 (not exec_8_0_5)))))
(assert (= stmt_9_0_6 (ite stmt_8_0_5 exec_8_0_5 (and stmt_8_0_6 (not exec_8_0_6)))))
(assert (= stmt_9_0_7 (ite stmt_8_0_6 (and exec_8_0_6 (not (not (= accu_8_0 #x0000)))) (and stmt_8_0_7 (not exec_8_0_7)))))

(assert (= stmt_9_1_0 (ite stmt_8_1_5 (and exec_8_1_5 (not (= accu_8_1 #x0000))) (and stmt_8_1_0 (not exec_8_1_0)))))
(assert (= stmt_9_1_1 (ite stmt_8_1_0 exec_8_1_0 (and stmt_8_1_1 (not exec_8_1_1)))))
(assert (= stmt_9_1_2 (ite stmt_8_1_1 exec_8_1_1 (and stmt_8_1_2 (not exec_8_1_2)))))
(assert (= stmt_9_1_3 (ite stmt_8_1_2 exec_8_1_2 (and stmt_8_1_3 (not exec_8_1_3)))))
(assert (= stmt_9_1_4 (ite stmt_8_1_3 exec_8_1_3 (and stmt_8_1_4 (not exec_8_1_4)))))
(assert (= stmt_9_1_5 (ite stmt_8_1_4 exec_8_1_4 (and stmt_8_1_5 (not exec_8_1_5)))))
(assert (= stmt_9_1_6 (ite stmt_8_1_5 (and exec_8_1_5 (not (not (= accu_8_1 #x0000)))) (and stmt_8_1_6 (not exec_8_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_9_0 () Bool)
(declare-fun thread_9_1 () Bool)

(assert (or thread_9_0 thread_9_1 exit_9))
(assert (or (not thread_9_0) (not thread_9_1)))
(assert (or (not thread_9_0) (not exit_9)))
(assert (or (not thread_9_1) (not exit_9)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_9_0_0 () Bool)
(declare-fun block_9_0_1 () Bool)
(declare-fun block_9_1_0 () Bool)
(declare-fun block_9_1_1 () Bool)

(assert (= block_9_0_0 (ite sync_8_0 false (or exec_8_0_1 block_8_0_0))))
(assert (= block_9_0_1 (ite sync_8_0 false (or exec_8_1_0 block_8_0_1))))
(assert (= block_9_1_0 (ite sync_8_1 false (or exec_8_0_5 block_8_1_0))))
(assert (= block_9_1_1 (ite sync_8_1 false (or exec_8_1_1 block_8_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_9_0 () Bool)
(declare-fun sync_9_1 () Bool)

(assert (= sync_9_0 (and block_9_0_0 block_9_0_1)))
(assert (= sync_9_1 (and block_9_1_0 block_9_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_9_0_0 (not sync_9_0)) (not thread_9_0))) ; barrier 0: thread 0
(assert (=> (and block_9_0_1 (not sync_9_0)) (not thread_9_1))) ; barrier 0: thread 1
(assert (=> (and block_9_1_0 (not sync_9_1)) (not thread_9_0))) ; barrier 1: thread 0
(assert (=> (and block_9_1_1 (not sync_9_1)) (not thread_9_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_9_0_0 () Bool)
(declare-fun exec_9_0_1 () Bool)
(declare-fun exec_9_0_2 () Bool)
(declare-fun exec_9_0_3 () Bool)
(declare-fun exec_9_0_4 () Bool)
(declare-fun exec_9_0_5 () Bool)
(declare-fun exec_9_0_6 () Bool)
(declare-fun exec_9_0_7 () Bool)

(declare-fun exec_9_1_0 () Bool)
(declare-fun exec_9_1_1 () Bool)
(declare-fun exec_9_1_2 () Bool)
(declare-fun exec_9_1_3 () Bool)
(declare-fun exec_9_1_4 () Bool)
(declare-fun exec_9_1_5 () Bool)
(declare-fun exec_9_1_6 () Bool)

(assert (= exec_9_0_0 (and stmt_9_0_0 thread_9_0)))
(assert (= exec_9_0_1 (and stmt_9_0_1 thread_9_0)))
(assert (= exec_9_0_2 (and stmt_9_0_2 thread_9_0)))
(assert (= exec_9_0_3 (and stmt_9_0_3 thread_9_0)))
(assert (= exec_9_0_4 (and stmt_9_0_4 thread_9_0)))
(assert (= exec_9_0_5 (and stmt_9_0_5 thread_9_0)))
(assert (= exec_9_0_6 (and stmt_9_0_6 thread_9_0)))
(assert (= exec_9_0_7 (and stmt_9_0_7 thread_9_0)))

(assert (= exec_9_1_0 (and stmt_9_1_0 thread_9_1)))
(assert (= exec_9_1_1 (and stmt_9_1_1 thread_9_1)))
(assert (= exec_9_1_2 (and stmt_9_1_2 thread_9_1)))
(assert (= exec_9_1_3 (and stmt_9_1_3 thread_9_1)))
(assert (= exec_9_1_4 (and stmt_9_1_4 thread_9_1)))
(assert (= exec_9_1_5 (and stmt_9_1_5 thread_9_1)))
(assert (= exec_9_1_6 (and stmt_9_1_6 thread_9_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_9_0 () (_ BitVec 16))
(declare-fun accu_9_1 () (_ BitVec 16))

(assert (= accu_9_0 (ite exec_9_0_2 (select heap_8 #x0000) (ite exec_9_0_3 (bvadd accu_8_0 #x0001) accu_8_0))))
(assert (= accu_9_1 (ite exec_9_1_2 (select heap_8 #x0000) (ite exec_9_1_3 (bvadd accu_8_1 #x0001) accu_8_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_9_0 () (_ BitVec 16))
(declare-fun mem_9_1 () (_ BitVec 16))

(assert (= mem_9_0 mem_8_0))
(assert (= mem_9_1 mem_8_1))

; heap states - heap_<step>
(declare-fun heap_9 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_9 (ite exec_9_0_0 (store heap_8 #x0000 accu_8_0) (ite exec_9_0_4 (store heap_8 #x0000 accu_8_0) (ite exec_9_1_4 (store heap_8 #x0000 accu_8_1) heap_8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 10
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_10 () Bool)

(assert (= exit_10 (or exit_9 exec_9_0_7 exec_9_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_10_0_0 () Bool)
(declare-fun stmt_10_0_1 () Bool)
(declare-fun stmt_10_0_2 () Bool)
(declare-fun stmt_10_0_3 () Bool)
(declare-fun stmt_10_0_4 () Bool)
(declare-fun stmt_10_0_5 () Bool)
(declare-fun stmt_10_0_6 () Bool)
(declare-fun stmt_10_0_7 () Bool)

(declare-fun stmt_10_1_0 () Bool)
(declare-fun stmt_10_1_1 () Bool)
(declare-fun stmt_10_1_2 () Bool)
(declare-fun stmt_10_1_3 () Bool)
(declare-fun stmt_10_1_4 () Bool)
(declare-fun stmt_10_1_5 () Bool)
(declare-fun stmt_10_1_6 () Bool)

(assert (= stmt_10_0_0 (and stmt_9_0_0 (not exec_9_0_0))))
(assert (= stmt_10_0_1 (ite stmt_9_0_6 (and exec_9_0_6 (not (= accu_9_0 #x0000))) (ite stmt_9_0_0 exec_9_0_0 (and stmt_9_0_1 (not exec_9_0_1))))))
(assert (= stmt_10_0_2 (ite stmt_9_0_1 exec_9_0_1 (and stmt_9_0_2 (not exec_9_0_2)))))
(assert (= stmt_10_0_3 (ite stmt_9_0_2 exec_9_0_2 (and stmt_9_0_3 (not exec_9_0_3)))))
(assert (= stmt_10_0_4 (ite stmt_9_0_3 exec_9_0_3 (and stmt_9_0_4 (not exec_9_0_4)))))
(assert (= stmt_10_0_5 (ite stmt_9_0_4 exec_9_0_4 (and stmt_9_0_5 (not exec_9_0_5)))))
(assert (= stmt_10_0_6 (ite stmt_9_0_5 exec_9_0_5 (and stmt_9_0_6 (not exec_9_0_6)))))
(assert (= stmt_10_0_7 (ite stmt_9_0_6 (and exec_9_0_6 (not (not (= accu_9_0 #x0000)))) (and stmt_9_0_7 (not exec_9_0_7)))))

(assert (= stmt_10_1_0 (ite stmt_9_1_5 (and exec_9_1_5 (not (= accu_9_1 #x0000))) (and stmt_9_1_0 (not exec_9_1_0)))))
(assert (= stmt_10_1_1 (ite stmt_9_1_0 exec_9_1_0 (and stmt_9_1_1 (not exec_9_1_1)))))
(assert (= stmt_10_1_2 (ite stmt_9_1_1 exec_9_1_1 (and stmt_9_1_2 (not exec_9_1_2)))))
(assert (= stmt_10_1_3 (ite stmt_9_1_2 exec_9_1_2 (and stmt_9_1_3 (not exec_9_1_3)))))
(assert (= stmt_10_1_4 (ite stmt_9_1_3 exec_9_1_3 (and stmt_9_1_4 (not exec_9_1_4)))))
(assert (= stmt_10_1_5 (ite stmt_9_1_4 exec_9_1_4 (and stmt_9_1_5 (not exec_9_1_5)))))
(assert (= stmt_10_1_6 (ite stmt_9_1_5 (and exec_9_1_5 (not (not (= accu_9_1 #x0000)))) (and stmt_9_1_6 (not exec_9_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_10_0 () Bool)
(declare-fun thread_10_1 () Bool)

(assert (or thread_10_0 thread_10_1 exit_10))
(assert (or (not thread_10_0) (not thread_10_1)))
(assert (or (not thread_10_0) (not exit_10)))
(assert (or (not thread_10_1) (not exit_10)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_10_0_0 () Bool)
(declare-fun block_10_0_1 () Bool)
(declare-fun block_10_1_0 () Bool)
(declare-fun block_10_1_1 () Bool)

(assert (= block_10_0_0 (ite sync_9_0 false (or exec_9_0_1 block_9_0_0))))
(assert (= block_10_0_1 (ite sync_9_0 false (or exec_9_1_0 block_9_0_1))))
(assert (= block_10_1_0 (ite sync_9_1 false (or exec_9_0_5 block_9_1_0))))
(assert (= block_10_1_1 (ite sync_9_1 false (or exec_9_1_1 block_9_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_10_0 () Bool)
(declare-fun sync_10_1 () Bool)

(assert (= sync_10_0 (and block_10_0_0 block_10_0_1)))
(assert (= sync_10_1 (and block_10_1_0 block_10_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_10_0_0 (not sync_10_0)) (not thread_10_0))) ; barrier 0: thread 0
(assert (=> (and block_10_0_1 (not sync_10_0)) (not thread_10_1))) ; barrier 0: thread 1
(assert (=> (and block_10_1_0 (not sync_10_1)) (not thread_10_0))) ; barrier 1: thread 0
(assert (=> (and block_10_1_1 (not sync_10_1)) (not thread_10_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_10_0_0 () Bool)
(declare-fun exec_10_0_1 () Bool)
(declare-fun exec_10_0_2 () Bool)
(declare-fun exec_10_0_3 () Bool)
(declare-fun exec_10_0_4 () Bool)
(declare-fun exec_10_0_5 () Bool)
(declare-fun exec_10_0_6 () Bool)
(declare-fun exec_10_0_7 () Bool)

(declare-fun exec_10_1_0 () Bool)
(declare-fun exec_10_1_1 () Bool)
(declare-fun exec_10_1_2 () Bool)
(declare-fun exec_10_1_3 () Bool)
(declare-fun exec_10_1_4 () Bool)
(declare-fun exec_10_1_5 () Bool)
(declare-fun exec_10_1_6 () Bool)

(assert (= exec_10_0_0 (and stmt_10_0_0 thread_10_0)))
(assert (= exec_10_0_1 (and stmt_10_0_1 thread_10_0)))
(assert (= exec_10_0_2 (and stmt_10_0_2 thread_10_0)))
(assert (= exec_10_0_3 (and stmt_10_0_3 thread_10_0)))
(assert (= exec_10_0_4 (and stmt_10_0_4 thread_10_0)))
(assert (= exec_10_0_5 (and stmt_10_0_5 thread_10_0)))
(assert (= exec_10_0_6 (and stmt_10_0_6 thread_10_0)))
(assert (= exec_10_0_7 (and stmt_10_0_7 thread_10_0)))

(assert (= exec_10_1_0 (and stmt_10_1_0 thread_10_1)))
(assert (= exec_10_1_1 (and stmt_10_1_1 thread_10_1)))
(assert (= exec_10_1_2 (and stmt_10_1_2 thread_10_1)))
(assert (= exec_10_1_3 (and stmt_10_1_3 thread_10_1)))
(assert (= exec_10_1_4 (and stmt_10_1_4 thread_10_1)))
(assert (= exec_10_1_5 (and stmt_10_1_5 thread_10_1)))
(assert (= exec_10_1_6 (and stmt_10_1_6 thread_10_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_10_0 () (_ BitVec 16))
(declare-fun accu_10_1 () (_ BitVec 16))

(assert (= accu_10_0 (ite exec_10_0_2 (select heap_9 #x0000) (ite exec_10_0_3 (bvadd accu_9_0 #x0001) accu_9_0))))
(assert (= accu_10_1 (ite exec_10_1_2 (select heap_9 #x0000) (ite exec_10_1_3 (bvadd accu_9_1 #x0001) accu_9_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_10_0 () (_ BitVec 16))
(declare-fun mem_10_1 () (_ BitVec 16))

(assert (= mem_10_0 mem_9_0))
(assert (= mem_10_1 mem_9_1))

; heap states - heap_<step>
(declare-fun heap_10 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_10 (ite exec_10_0_0 (store heap_9 #x0000 accu_9_0) (ite exec_10_0_4 (store heap_9 #x0000 accu_9_0) (ite exec_10_1_4 (store heap_9 #x0000 accu_9_1) heap_9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 11
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_11 () Bool)

(assert (= exit_11 (or exit_10 exec_10_0_7 exec_10_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_11_0_0 () Bool)
(declare-fun stmt_11_0_1 () Bool)
(declare-fun stmt_11_0_2 () Bool)
(declare-fun stmt_11_0_3 () Bool)
(declare-fun stmt_11_0_4 () Bool)
(declare-fun stmt_11_0_5 () Bool)
(declare-fun stmt_11_0_6 () Bool)
(declare-fun stmt_11_0_7 () Bool)

(declare-fun stmt_11_1_0 () Bool)
(declare-fun stmt_11_1_1 () Bool)
(declare-fun stmt_11_1_2 () Bool)
(declare-fun stmt_11_1_3 () Bool)
(declare-fun stmt_11_1_4 () Bool)
(declare-fun stmt_11_1_5 () Bool)
(declare-fun stmt_11_1_6 () Bool)

(assert (= stmt_11_0_0 (and stmt_10_0_0 (not exec_10_0_0))))
(assert (= stmt_11_0_1 (ite stmt_10_0_6 (and exec_10_0_6 (not (= accu_10_0 #x0000))) (ite stmt_10_0_0 exec_10_0_0 (and stmt_10_0_1 (not exec_10_0_1))))))
(assert (= stmt_11_0_2 (ite stmt_10_0_1 exec_10_0_1 (and stmt_10_0_2 (not exec_10_0_2)))))
(assert (= stmt_11_0_3 (ite stmt_10_0_2 exec_10_0_2 (and stmt_10_0_3 (not exec_10_0_3)))))
(assert (= stmt_11_0_4 (ite stmt_10_0_3 exec_10_0_3 (and stmt_10_0_4 (not exec_10_0_4)))))
(assert (= stmt_11_0_5 (ite stmt_10_0_4 exec_10_0_4 (and stmt_10_0_5 (not exec_10_0_5)))))
(assert (= stmt_11_0_6 (ite stmt_10_0_5 exec_10_0_5 (and stmt_10_0_6 (not exec_10_0_6)))))
(assert (= stmt_11_0_7 (ite stmt_10_0_6 (and exec_10_0_6 (not (not (= accu_10_0 #x0000)))) (and stmt_10_0_7 (not exec_10_0_7)))))

(assert (= stmt_11_1_0 (ite stmt_10_1_5 (and exec_10_1_5 (not (= accu_10_1 #x0000))) (and stmt_10_1_0 (not exec_10_1_0)))))
(assert (= stmt_11_1_1 (ite stmt_10_1_0 exec_10_1_0 (and stmt_10_1_1 (not exec_10_1_1)))))
(assert (= stmt_11_1_2 (ite stmt_10_1_1 exec_10_1_1 (and stmt_10_1_2 (not exec_10_1_2)))))
(assert (= stmt_11_1_3 (ite stmt_10_1_2 exec_10_1_2 (and stmt_10_1_3 (not exec_10_1_3)))))
(assert (= stmt_11_1_4 (ite stmt_10_1_3 exec_10_1_3 (and stmt_10_1_4 (not exec_10_1_4)))))
(assert (= stmt_11_1_5 (ite stmt_10_1_4 exec_10_1_4 (and stmt_10_1_5 (not exec_10_1_5)))))
(assert (= stmt_11_1_6 (ite stmt_10_1_5 (and exec_10_1_5 (not (not (= accu_10_1 #x0000)))) (and stmt_10_1_6 (not exec_10_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_11_0 () Bool)
(declare-fun thread_11_1 () Bool)

(assert (or thread_11_0 thread_11_1 exit_11))
(assert (or (not thread_11_0) (not thread_11_1)))
(assert (or (not thread_11_0) (not exit_11)))
(assert (or (not thread_11_1) (not exit_11)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_11_0_0 () Bool)
(declare-fun block_11_0_1 () Bool)
(declare-fun block_11_1_0 () Bool)
(declare-fun block_11_1_1 () Bool)

(assert (= block_11_0_0 (ite sync_10_0 false (or exec_10_0_1 block_10_0_0))))
(assert (= block_11_0_1 (ite sync_10_0 false (or exec_10_1_0 block_10_0_1))))
(assert (= block_11_1_0 (ite sync_10_1 false (or exec_10_0_5 block_10_1_0))))
(assert (= block_11_1_1 (ite sync_10_1 false (or exec_10_1_1 block_10_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_11_0 () Bool)
(declare-fun sync_11_1 () Bool)

(assert (= sync_11_0 (and block_11_0_0 block_11_0_1)))
(assert (= sync_11_1 (and block_11_1_0 block_11_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_11_0_0 (not sync_11_0)) (not thread_11_0))) ; barrier 0: thread 0
(assert (=> (and block_11_0_1 (not sync_11_0)) (not thread_11_1))) ; barrier 0: thread 1
(assert (=> (and block_11_1_0 (not sync_11_1)) (not thread_11_0))) ; barrier 1: thread 0
(assert (=> (and block_11_1_1 (not sync_11_1)) (not thread_11_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_11_0_0 () Bool)
(declare-fun exec_11_0_1 () Bool)
(declare-fun exec_11_0_2 () Bool)
(declare-fun exec_11_0_3 () Bool)
(declare-fun exec_11_0_4 () Bool)
(declare-fun exec_11_0_5 () Bool)
(declare-fun exec_11_0_6 () Bool)
(declare-fun exec_11_0_7 () Bool)

(declare-fun exec_11_1_0 () Bool)
(declare-fun exec_11_1_1 () Bool)
(declare-fun exec_11_1_2 () Bool)
(declare-fun exec_11_1_3 () Bool)
(declare-fun exec_11_1_4 () Bool)
(declare-fun exec_11_1_5 () Bool)
(declare-fun exec_11_1_6 () Bool)

(assert (= exec_11_0_0 (and stmt_11_0_0 thread_11_0)))
(assert (= exec_11_0_1 (and stmt_11_0_1 thread_11_0)))
(assert (= exec_11_0_2 (and stmt_11_0_2 thread_11_0)))
(assert (= exec_11_0_3 (and stmt_11_0_3 thread_11_0)))
(assert (= exec_11_0_4 (and stmt_11_0_4 thread_11_0)))
(assert (= exec_11_0_5 (and stmt_11_0_5 thread_11_0)))
(assert (= exec_11_0_6 (and stmt_11_0_6 thread_11_0)))
(assert (= exec_11_0_7 (and stmt_11_0_7 thread_11_0)))

(assert (= exec_11_1_0 (and stmt_11_1_0 thread_11_1)))
(assert (= exec_11_1_1 (and stmt_11_1_1 thread_11_1)))
(assert (= exec_11_1_2 (and stmt_11_1_2 thread_11_1)))
(assert (= exec_11_1_3 (and stmt_11_1_3 thread_11_1)))
(assert (= exec_11_1_4 (and stmt_11_1_4 thread_11_1)))
(assert (= exec_11_1_5 (and stmt_11_1_5 thread_11_1)))
(assert (= exec_11_1_6 (and stmt_11_1_6 thread_11_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_11_0 () (_ BitVec 16))
(declare-fun accu_11_1 () (_ BitVec 16))

(assert (= accu_11_0 (ite exec_11_0_2 (select heap_10 #x0000) (ite exec_11_0_3 (bvadd accu_10_0 #x0001) accu_10_0))))
(assert (= accu_11_1 (ite exec_11_1_2 (select heap_10 #x0000) (ite exec_11_1_3 (bvadd accu_10_1 #x0001) accu_10_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_11_0 () (_ BitVec 16))
(declare-fun mem_11_1 () (_ BitVec 16))

(assert (= mem_11_0 mem_10_0))
(assert (= mem_11_1 mem_10_1))

; heap states - heap_<step>
(declare-fun heap_11 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_11 (ite exec_11_0_0 (store heap_10 #x0000 accu_10_0) (ite exec_11_0_4 (store heap_10 #x0000 accu_10_0) (ite exec_11_1_4 (store heap_10 #x0000 accu_10_1) heap_10)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_12 () Bool)

(assert (= exit_12 (or exit_11 exec_11_0_7 exec_11_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_12_0_0 () Bool)
(declare-fun stmt_12_0_1 () Bool)
(declare-fun stmt_12_0_2 () Bool)
(declare-fun stmt_12_0_3 () Bool)
(declare-fun stmt_12_0_4 () Bool)
(declare-fun stmt_12_0_5 () Bool)
(declare-fun stmt_12_0_6 () Bool)
(declare-fun stmt_12_0_7 () Bool)

(declare-fun stmt_12_1_0 () Bool)
(declare-fun stmt_12_1_1 () Bool)
(declare-fun stmt_12_1_2 () Bool)
(declare-fun stmt_12_1_3 () Bool)
(declare-fun stmt_12_1_4 () Bool)
(declare-fun stmt_12_1_5 () Bool)
(declare-fun stmt_12_1_6 () Bool)

(assert (= stmt_12_0_0 (and stmt_11_0_0 (not exec_11_0_0))))
(assert (= stmt_12_0_1 (ite stmt_11_0_6 (and exec_11_0_6 (not (= accu_11_0 #x0000))) (ite stmt_11_0_0 exec_11_0_0 (and stmt_11_0_1 (not exec_11_0_1))))))
(assert (= stmt_12_0_2 (ite stmt_11_0_1 exec_11_0_1 (and stmt_11_0_2 (not exec_11_0_2)))))
(assert (= stmt_12_0_3 (ite stmt_11_0_2 exec_11_0_2 (and stmt_11_0_3 (not exec_11_0_3)))))
(assert (= stmt_12_0_4 (ite stmt_11_0_3 exec_11_0_3 (and stmt_11_0_4 (not exec_11_0_4)))))
(assert (= stmt_12_0_5 (ite stmt_11_0_4 exec_11_0_4 (and stmt_11_0_5 (not exec_11_0_5)))))
(assert (= stmt_12_0_6 (ite stmt_11_0_5 exec_11_0_5 (and stmt_11_0_6 (not exec_11_0_6)))))
(assert (= stmt_12_0_7 (ite stmt_11_0_6 (and exec_11_0_6 (not (not (= accu_11_0 #x0000)))) (and stmt_11_0_7 (not exec_11_0_7)))))

(assert (= stmt_12_1_0 (ite stmt_11_1_5 (and exec_11_1_5 (not (= accu_11_1 #x0000))) (and stmt_11_1_0 (not exec_11_1_0)))))
(assert (= stmt_12_1_1 (ite stmt_11_1_0 exec_11_1_0 (and stmt_11_1_1 (not exec_11_1_1)))))
(assert (= stmt_12_1_2 (ite stmt_11_1_1 exec_11_1_1 (and stmt_11_1_2 (not exec_11_1_2)))))
(assert (= stmt_12_1_3 (ite stmt_11_1_2 exec_11_1_2 (and stmt_11_1_3 (not exec_11_1_3)))))
(assert (= stmt_12_1_4 (ite stmt_11_1_3 exec_11_1_3 (and stmt_11_1_4 (not exec_11_1_4)))))
(assert (= stmt_12_1_5 (ite stmt_11_1_4 exec_11_1_4 (and stmt_11_1_5 (not exec_11_1_5)))))
(assert (= stmt_12_1_6 (ite stmt_11_1_5 (and exec_11_1_5 (not (not (= accu_11_1 #x0000)))) (and stmt_11_1_6 (not exec_11_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_12_0 () Bool)
(declare-fun thread_12_1 () Bool)

(assert (or thread_12_0 thread_12_1 exit_12))
(assert (or (not thread_12_0) (not thread_12_1)))
(assert (or (not thread_12_0) (not exit_12)))
(assert (or (not thread_12_1) (not exit_12)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_12_0_0 () Bool)
(declare-fun block_12_0_1 () Bool)
(declare-fun block_12_1_0 () Bool)
(declare-fun block_12_1_1 () Bool)

(assert (= block_12_0_0 (ite sync_11_0 false (or exec_11_0_1 block_11_0_0))))
(assert (= block_12_0_1 (ite sync_11_0 false (or exec_11_1_0 block_11_0_1))))
(assert (= block_12_1_0 (ite sync_11_1 false (or exec_11_0_5 block_11_1_0))))
(assert (= block_12_1_1 (ite sync_11_1 false (or exec_11_1_1 block_11_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_12_0 () Bool)
(declare-fun sync_12_1 () Bool)

(assert (= sync_12_0 (and block_12_0_0 block_12_0_1)))
(assert (= sync_12_1 (and block_12_1_0 block_12_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_12_0_0 (not sync_12_0)) (not thread_12_0))) ; barrier 0: thread 0
(assert (=> (and block_12_0_1 (not sync_12_0)) (not thread_12_1))) ; barrier 0: thread 1
(assert (=> (and block_12_1_0 (not sync_12_1)) (not thread_12_0))) ; barrier 1: thread 0
(assert (=> (and block_12_1_1 (not sync_12_1)) (not thread_12_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_12_0_0 () Bool)
(declare-fun exec_12_0_1 () Bool)
(declare-fun exec_12_0_2 () Bool)
(declare-fun exec_12_0_3 () Bool)
(declare-fun exec_12_0_4 () Bool)
(declare-fun exec_12_0_5 () Bool)
(declare-fun exec_12_0_6 () Bool)
(declare-fun exec_12_0_7 () Bool)

(declare-fun exec_12_1_0 () Bool)
(declare-fun exec_12_1_1 () Bool)
(declare-fun exec_12_1_2 () Bool)
(declare-fun exec_12_1_3 () Bool)
(declare-fun exec_12_1_4 () Bool)
(declare-fun exec_12_1_5 () Bool)
(declare-fun exec_12_1_6 () Bool)

(assert (= exec_12_0_0 (and stmt_12_0_0 thread_12_0)))
(assert (= exec_12_0_1 (and stmt_12_0_1 thread_12_0)))
(assert (= exec_12_0_2 (and stmt_12_0_2 thread_12_0)))
(assert (= exec_12_0_3 (and stmt_12_0_3 thread_12_0)))
(assert (= exec_12_0_4 (and stmt_12_0_4 thread_12_0)))
(assert (= exec_12_0_5 (and stmt_12_0_5 thread_12_0)))
(assert (= exec_12_0_6 (and stmt_12_0_6 thread_12_0)))
(assert (= exec_12_0_7 (and stmt_12_0_7 thread_12_0)))

(assert (= exec_12_1_0 (and stmt_12_1_0 thread_12_1)))
(assert (= exec_12_1_1 (and stmt_12_1_1 thread_12_1)))
(assert (= exec_12_1_2 (and stmt_12_1_2 thread_12_1)))
(assert (= exec_12_1_3 (and stmt_12_1_3 thread_12_1)))
(assert (= exec_12_1_4 (and stmt_12_1_4 thread_12_1)))
(assert (= exec_12_1_5 (and stmt_12_1_5 thread_12_1)))
(assert (= exec_12_1_6 (and stmt_12_1_6 thread_12_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_12_0 () (_ BitVec 16))
(declare-fun accu_12_1 () (_ BitVec 16))

(assert (= accu_12_0 (ite exec_12_0_2 (select heap_11 #x0000) (ite exec_12_0_3 (bvadd accu_11_0 #x0001) accu_11_0))))
(assert (= accu_12_1 (ite exec_12_1_2 (select heap_11 #x0000) (ite exec_12_1_3 (bvadd accu_11_1 #x0001) accu_11_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_12_0 () (_ BitVec 16))
(declare-fun mem_12_1 () (_ BitVec 16))

(assert (= mem_12_0 mem_11_0))
(assert (= mem_12_1 mem_11_1))

; heap states - heap_<step>
(declare-fun heap_12 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_12 (ite exec_12_0_0 (store heap_11 #x0000 accu_11_0) (ite exec_12_0_4 (store heap_11 #x0000 accu_11_0) (ite exec_12_1_4 (store heap_11 #x0000 accu_11_1) heap_11)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 13
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_13 () Bool)

(assert (= exit_13 (or exit_12 exec_12_0_7 exec_12_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_13_0_0 () Bool)
(declare-fun stmt_13_0_1 () Bool)
(declare-fun stmt_13_0_2 () Bool)
(declare-fun stmt_13_0_3 () Bool)
(declare-fun stmt_13_0_4 () Bool)
(declare-fun stmt_13_0_5 () Bool)
(declare-fun stmt_13_0_6 () Bool)
(declare-fun stmt_13_0_7 () Bool)

(declare-fun stmt_13_1_0 () Bool)
(declare-fun stmt_13_1_1 () Bool)
(declare-fun stmt_13_1_2 () Bool)
(declare-fun stmt_13_1_3 () Bool)
(declare-fun stmt_13_1_4 () Bool)
(declare-fun stmt_13_1_5 () Bool)
(declare-fun stmt_13_1_6 () Bool)

(assert (= stmt_13_0_0 (and stmt_12_0_0 (not exec_12_0_0))))
(assert (= stmt_13_0_1 (ite stmt_12_0_6 (and exec_12_0_6 (not (= accu_12_0 #x0000))) (ite stmt_12_0_0 exec_12_0_0 (and stmt_12_0_1 (not exec_12_0_1))))))
(assert (= stmt_13_0_2 (ite stmt_12_0_1 exec_12_0_1 (and stmt_12_0_2 (not exec_12_0_2)))))
(assert (= stmt_13_0_3 (ite stmt_12_0_2 exec_12_0_2 (and stmt_12_0_3 (not exec_12_0_3)))))
(assert (= stmt_13_0_4 (ite stmt_12_0_3 exec_12_0_3 (and stmt_12_0_4 (not exec_12_0_4)))))
(assert (= stmt_13_0_5 (ite stmt_12_0_4 exec_12_0_4 (and stmt_12_0_5 (not exec_12_0_5)))))
(assert (= stmt_13_0_6 (ite stmt_12_0_5 exec_12_0_5 (and stmt_12_0_6 (not exec_12_0_6)))))
(assert (= stmt_13_0_7 (ite stmt_12_0_6 (and exec_12_0_6 (not (not (= accu_12_0 #x0000)))) (and stmt_12_0_7 (not exec_12_0_7)))))

(assert (= stmt_13_1_0 (ite stmt_12_1_5 (and exec_12_1_5 (not (= accu_12_1 #x0000))) (and stmt_12_1_0 (not exec_12_1_0)))))
(assert (= stmt_13_1_1 (ite stmt_12_1_0 exec_12_1_0 (and stmt_12_1_1 (not exec_12_1_1)))))
(assert (= stmt_13_1_2 (ite stmt_12_1_1 exec_12_1_1 (and stmt_12_1_2 (not exec_12_1_2)))))
(assert (= stmt_13_1_3 (ite stmt_12_1_2 exec_12_1_2 (and stmt_12_1_3 (not exec_12_1_3)))))
(assert (= stmt_13_1_4 (ite stmt_12_1_3 exec_12_1_3 (and stmt_12_1_4 (not exec_12_1_4)))))
(assert (= stmt_13_1_5 (ite stmt_12_1_4 exec_12_1_4 (and stmt_12_1_5 (not exec_12_1_5)))))
(assert (= stmt_13_1_6 (ite stmt_12_1_5 (and exec_12_1_5 (not (not (= accu_12_1 #x0000)))) (and stmt_12_1_6 (not exec_12_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_13_0 () Bool)
(declare-fun thread_13_1 () Bool)

(assert (or thread_13_0 thread_13_1 exit_13))
(assert (or (not thread_13_0) (not thread_13_1)))
(assert (or (not thread_13_0) (not exit_13)))
(assert (or (not thread_13_1) (not exit_13)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_13_0_0 () Bool)
(declare-fun block_13_0_1 () Bool)
(declare-fun block_13_1_0 () Bool)
(declare-fun block_13_1_1 () Bool)

(assert (= block_13_0_0 (ite sync_12_0 false (or exec_12_0_1 block_12_0_0))))
(assert (= block_13_0_1 (ite sync_12_0 false (or exec_12_1_0 block_12_0_1))))
(assert (= block_13_1_0 (ite sync_12_1 false (or exec_12_0_5 block_12_1_0))))
(assert (= block_13_1_1 (ite sync_12_1 false (or exec_12_1_1 block_12_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_13_0 () Bool)
(declare-fun sync_13_1 () Bool)

(assert (= sync_13_0 (and block_13_0_0 block_13_0_1)))
(assert (= sync_13_1 (and block_13_1_0 block_13_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_13_0_0 (not sync_13_0)) (not thread_13_0))) ; barrier 0: thread 0
(assert (=> (and block_13_0_1 (not sync_13_0)) (not thread_13_1))) ; barrier 0: thread 1
(assert (=> (and block_13_1_0 (not sync_13_1)) (not thread_13_0))) ; barrier 1: thread 0
(assert (=> (and block_13_1_1 (not sync_13_1)) (not thread_13_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_13_0_0 () Bool)
(declare-fun exec_13_0_1 () Bool)
(declare-fun exec_13_0_2 () Bool)
(declare-fun exec_13_0_3 () Bool)
(declare-fun exec_13_0_4 () Bool)
(declare-fun exec_13_0_5 () Bool)
(declare-fun exec_13_0_6 () Bool)
(declare-fun exec_13_0_7 () Bool)

(declare-fun exec_13_1_0 () Bool)
(declare-fun exec_13_1_1 () Bool)
(declare-fun exec_13_1_2 () Bool)
(declare-fun exec_13_1_3 () Bool)
(declare-fun exec_13_1_4 () Bool)
(declare-fun exec_13_1_5 () Bool)
(declare-fun exec_13_1_6 () Bool)

(assert (= exec_13_0_0 (and stmt_13_0_0 thread_13_0)))
(assert (= exec_13_0_1 (and stmt_13_0_1 thread_13_0)))
(assert (= exec_13_0_2 (and stmt_13_0_2 thread_13_0)))
(assert (= exec_13_0_3 (and stmt_13_0_3 thread_13_0)))
(assert (= exec_13_0_4 (and stmt_13_0_4 thread_13_0)))
(assert (= exec_13_0_5 (and stmt_13_0_5 thread_13_0)))
(assert (= exec_13_0_6 (and stmt_13_0_6 thread_13_0)))
(assert (= exec_13_0_7 (and stmt_13_0_7 thread_13_0)))

(assert (= exec_13_1_0 (and stmt_13_1_0 thread_13_1)))
(assert (= exec_13_1_1 (and stmt_13_1_1 thread_13_1)))
(assert (= exec_13_1_2 (and stmt_13_1_2 thread_13_1)))
(assert (= exec_13_1_3 (and stmt_13_1_3 thread_13_1)))
(assert (= exec_13_1_4 (and stmt_13_1_4 thread_13_1)))
(assert (= exec_13_1_5 (and stmt_13_1_5 thread_13_1)))
(assert (= exec_13_1_6 (and stmt_13_1_6 thread_13_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_13_0 () (_ BitVec 16))
(declare-fun accu_13_1 () (_ BitVec 16))

(assert (= accu_13_0 (ite exec_13_0_2 (select heap_12 #x0000) (ite exec_13_0_3 (bvadd accu_12_0 #x0001) accu_12_0))))
(assert (= accu_13_1 (ite exec_13_1_2 (select heap_12 #x0000) (ite exec_13_1_3 (bvadd accu_12_1 #x0001) accu_12_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_13_0 () (_ BitVec 16))
(declare-fun mem_13_1 () (_ BitVec 16))

(assert (= mem_13_0 mem_12_0))
(assert (= mem_13_1 mem_12_1))

; heap states - heap_<step>
(declare-fun heap_13 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_13 (ite exec_13_0_0 (store heap_12 #x0000 accu_12_0) (ite exec_13_0_4 (store heap_12 #x0000 accu_12_0) (ite exec_13_1_4 (store heap_12 #x0000 accu_12_1) heap_12)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 14
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_14 () Bool)

(assert (= exit_14 (or exit_13 exec_13_0_7 exec_13_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_14_0_0 () Bool)
(declare-fun stmt_14_0_1 () Bool)
(declare-fun stmt_14_0_2 () Bool)
(declare-fun stmt_14_0_3 () Bool)
(declare-fun stmt_14_0_4 () Bool)
(declare-fun stmt_14_0_5 () Bool)
(declare-fun stmt_14_0_6 () Bool)
(declare-fun stmt_14_0_7 () Bool)

(declare-fun stmt_14_1_0 () Bool)
(declare-fun stmt_14_1_1 () Bool)
(declare-fun stmt_14_1_2 () Bool)
(declare-fun stmt_14_1_3 () Bool)
(declare-fun stmt_14_1_4 () Bool)
(declare-fun stmt_14_1_5 () Bool)
(declare-fun stmt_14_1_6 () Bool)

(assert (= stmt_14_0_0 (and stmt_13_0_0 (not exec_13_0_0))))
(assert (= stmt_14_0_1 (ite stmt_13_0_6 (and exec_13_0_6 (not (= accu_13_0 #x0000))) (ite stmt_13_0_0 exec_13_0_0 (and stmt_13_0_1 (not exec_13_0_1))))))
(assert (= stmt_14_0_2 (ite stmt_13_0_1 exec_13_0_1 (and stmt_13_0_2 (not exec_13_0_2)))))
(assert (= stmt_14_0_3 (ite stmt_13_0_2 exec_13_0_2 (and stmt_13_0_3 (not exec_13_0_3)))))
(assert (= stmt_14_0_4 (ite stmt_13_0_3 exec_13_0_3 (and stmt_13_0_4 (not exec_13_0_4)))))
(assert (= stmt_14_0_5 (ite stmt_13_0_4 exec_13_0_4 (and stmt_13_0_5 (not exec_13_0_5)))))
(assert (= stmt_14_0_6 (ite stmt_13_0_5 exec_13_0_5 (and stmt_13_0_6 (not exec_13_0_6)))))
(assert (= stmt_14_0_7 (ite stmt_13_0_6 (and exec_13_0_6 (not (not (= accu_13_0 #x0000)))) (and stmt_13_0_7 (not exec_13_0_7)))))

(assert (= stmt_14_1_0 (ite stmt_13_1_5 (and exec_13_1_5 (not (= accu_13_1 #x0000))) (and stmt_13_1_0 (not exec_13_1_0)))))
(assert (= stmt_14_1_1 (ite stmt_13_1_0 exec_13_1_0 (and stmt_13_1_1 (not exec_13_1_1)))))
(assert (= stmt_14_1_2 (ite stmt_13_1_1 exec_13_1_1 (and stmt_13_1_2 (not exec_13_1_2)))))
(assert (= stmt_14_1_3 (ite stmt_13_1_2 exec_13_1_2 (and stmt_13_1_3 (not exec_13_1_3)))))
(assert (= stmt_14_1_4 (ite stmt_13_1_3 exec_13_1_3 (and stmt_13_1_4 (not exec_13_1_4)))))
(assert (= stmt_14_1_5 (ite stmt_13_1_4 exec_13_1_4 (and stmt_13_1_5 (not exec_13_1_5)))))
(assert (= stmt_14_1_6 (ite stmt_13_1_5 (and exec_13_1_5 (not (not (= accu_13_1 #x0000)))) (and stmt_13_1_6 (not exec_13_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_14_0 () Bool)
(declare-fun thread_14_1 () Bool)

(assert (or thread_14_0 thread_14_1 exit_14))
(assert (or (not thread_14_0) (not thread_14_1)))
(assert (or (not thread_14_0) (not exit_14)))
(assert (or (not thread_14_1) (not exit_14)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_14_0_0 () Bool)
(declare-fun block_14_0_1 () Bool)
(declare-fun block_14_1_0 () Bool)
(declare-fun block_14_1_1 () Bool)

(assert (= block_14_0_0 (ite sync_13_0 false (or exec_13_0_1 block_13_0_0))))
(assert (= block_14_0_1 (ite sync_13_0 false (or exec_13_1_0 block_13_0_1))))
(assert (= block_14_1_0 (ite sync_13_1 false (or exec_13_0_5 block_13_1_0))))
(assert (= block_14_1_1 (ite sync_13_1 false (or exec_13_1_1 block_13_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_14_0 () Bool)
(declare-fun sync_14_1 () Bool)

(assert (= sync_14_0 (and block_14_0_0 block_14_0_1)))
(assert (= sync_14_1 (and block_14_1_0 block_14_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_14_0_0 (not sync_14_0)) (not thread_14_0))) ; barrier 0: thread 0
(assert (=> (and block_14_0_1 (not sync_14_0)) (not thread_14_1))) ; barrier 0: thread 1
(assert (=> (and block_14_1_0 (not sync_14_1)) (not thread_14_0))) ; barrier 1: thread 0
(assert (=> (and block_14_1_1 (not sync_14_1)) (not thread_14_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_14_0_0 () Bool)
(declare-fun exec_14_0_1 () Bool)
(declare-fun exec_14_0_2 () Bool)
(declare-fun exec_14_0_3 () Bool)
(declare-fun exec_14_0_4 () Bool)
(declare-fun exec_14_0_5 () Bool)
(declare-fun exec_14_0_6 () Bool)
(declare-fun exec_14_0_7 () Bool)

(declare-fun exec_14_1_0 () Bool)
(declare-fun exec_14_1_1 () Bool)
(declare-fun exec_14_1_2 () Bool)
(declare-fun exec_14_1_3 () Bool)
(declare-fun exec_14_1_4 () Bool)
(declare-fun exec_14_1_5 () Bool)
(declare-fun exec_14_1_6 () Bool)

(assert (= exec_14_0_0 (and stmt_14_0_0 thread_14_0)))
(assert (= exec_14_0_1 (and stmt_14_0_1 thread_14_0)))
(assert (= exec_14_0_2 (and stmt_14_0_2 thread_14_0)))
(assert (= exec_14_0_3 (and stmt_14_0_3 thread_14_0)))
(assert (= exec_14_0_4 (and stmt_14_0_4 thread_14_0)))
(assert (= exec_14_0_5 (and stmt_14_0_5 thread_14_0)))
(assert (= exec_14_0_6 (and stmt_14_0_6 thread_14_0)))
(assert (= exec_14_0_7 (and stmt_14_0_7 thread_14_0)))

(assert (= exec_14_1_0 (and stmt_14_1_0 thread_14_1)))
(assert (= exec_14_1_1 (and stmt_14_1_1 thread_14_1)))
(assert (= exec_14_1_2 (and stmt_14_1_2 thread_14_1)))
(assert (= exec_14_1_3 (and stmt_14_1_3 thread_14_1)))
(assert (= exec_14_1_4 (and stmt_14_1_4 thread_14_1)))
(assert (= exec_14_1_5 (and stmt_14_1_5 thread_14_1)))
(assert (= exec_14_1_6 (and stmt_14_1_6 thread_14_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_14_0 () (_ BitVec 16))
(declare-fun accu_14_1 () (_ BitVec 16))

(assert (= accu_14_0 (ite exec_14_0_2 (select heap_13 #x0000) (ite exec_14_0_3 (bvadd accu_13_0 #x0001) accu_13_0))))
(assert (= accu_14_1 (ite exec_14_1_2 (select heap_13 #x0000) (ite exec_14_1_3 (bvadd accu_13_1 #x0001) accu_13_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_14_0 () (_ BitVec 16))
(declare-fun mem_14_1 () (_ BitVec 16))

(assert (= mem_14_0 mem_13_0))
(assert (= mem_14_1 mem_13_1))

; heap states - heap_<step>
(declare-fun heap_14 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_14 (ite exec_14_0_0 (store heap_13 #x0000 accu_13_0) (ite exec_14_0_4 (store heap_13 #x0000 accu_13_0) (ite exec_14_1_4 (store heap_13 #x0000 accu_13_1) heap_13)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 15
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_15 () Bool)

(assert (= exit_15 (or exit_14 exec_14_0_7 exec_14_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_15_0_0 () Bool)
(declare-fun stmt_15_0_1 () Bool)
(declare-fun stmt_15_0_2 () Bool)
(declare-fun stmt_15_0_3 () Bool)
(declare-fun stmt_15_0_4 () Bool)
(declare-fun stmt_15_0_5 () Bool)
(declare-fun stmt_15_0_6 () Bool)
(declare-fun stmt_15_0_7 () Bool)

(declare-fun stmt_15_1_0 () Bool)
(declare-fun stmt_15_1_1 () Bool)
(declare-fun stmt_15_1_2 () Bool)
(declare-fun stmt_15_1_3 () Bool)
(declare-fun stmt_15_1_4 () Bool)
(declare-fun stmt_15_1_5 () Bool)
(declare-fun stmt_15_1_6 () Bool)

(assert (= stmt_15_0_0 (and stmt_14_0_0 (not exec_14_0_0))))
(assert (= stmt_15_0_1 (ite stmt_14_0_6 (and exec_14_0_6 (not (= accu_14_0 #x0000))) (ite stmt_14_0_0 exec_14_0_0 (and stmt_14_0_1 (not exec_14_0_1))))))
(assert (= stmt_15_0_2 (ite stmt_14_0_1 exec_14_0_1 (and stmt_14_0_2 (not exec_14_0_2)))))
(assert (= stmt_15_0_3 (ite stmt_14_0_2 exec_14_0_2 (and stmt_14_0_3 (not exec_14_0_3)))))
(assert (= stmt_15_0_4 (ite stmt_14_0_3 exec_14_0_3 (and stmt_14_0_4 (not exec_14_0_4)))))
(assert (= stmt_15_0_5 (ite stmt_14_0_4 exec_14_0_4 (and stmt_14_0_5 (not exec_14_0_5)))))
(assert (= stmt_15_0_6 (ite stmt_14_0_5 exec_14_0_5 (and stmt_14_0_6 (not exec_14_0_6)))))
(assert (= stmt_15_0_7 (ite stmt_14_0_6 (and exec_14_0_6 (not (not (= accu_14_0 #x0000)))) (and stmt_14_0_7 (not exec_14_0_7)))))

(assert (= stmt_15_1_0 (ite stmt_14_1_5 (and exec_14_1_5 (not (= accu_14_1 #x0000))) (and stmt_14_1_0 (not exec_14_1_0)))))
(assert (= stmt_15_1_1 (ite stmt_14_1_0 exec_14_1_0 (and stmt_14_1_1 (not exec_14_1_1)))))
(assert (= stmt_15_1_2 (ite stmt_14_1_1 exec_14_1_1 (and stmt_14_1_2 (not exec_14_1_2)))))
(assert (= stmt_15_1_3 (ite stmt_14_1_2 exec_14_1_2 (and stmt_14_1_3 (not exec_14_1_3)))))
(assert (= stmt_15_1_4 (ite stmt_14_1_3 exec_14_1_3 (and stmt_14_1_4 (not exec_14_1_4)))))
(assert (= stmt_15_1_5 (ite stmt_14_1_4 exec_14_1_4 (and stmt_14_1_5 (not exec_14_1_5)))))
(assert (= stmt_15_1_6 (ite stmt_14_1_5 (and exec_14_1_5 (not (not (= accu_14_1 #x0000)))) (and stmt_14_1_6 (not exec_14_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_15_0 () Bool)
(declare-fun thread_15_1 () Bool)

(assert (or thread_15_0 thread_15_1 exit_15))
(assert (or (not thread_15_0) (not thread_15_1)))
(assert (or (not thread_15_0) (not exit_15)))
(assert (or (not thread_15_1) (not exit_15)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_15_0_0 () Bool)
(declare-fun block_15_0_1 () Bool)
(declare-fun block_15_1_0 () Bool)
(declare-fun block_15_1_1 () Bool)

(assert (= block_15_0_0 (ite sync_14_0 false (or exec_14_0_1 block_14_0_0))))
(assert (= block_15_0_1 (ite sync_14_0 false (or exec_14_1_0 block_14_0_1))))
(assert (= block_15_1_0 (ite sync_14_1 false (or exec_14_0_5 block_14_1_0))))
(assert (= block_15_1_1 (ite sync_14_1 false (or exec_14_1_1 block_14_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_15_0 () Bool)
(declare-fun sync_15_1 () Bool)

(assert (= sync_15_0 (and block_15_0_0 block_15_0_1)))
(assert (= sync_15_1 (and block_15_1_0 block_15_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_15_0_0 (not sync_15_0)) (not thread_15_0))) ; barrier 0: thread 0
(assert (=> (and block_15_0_1 (not sync_15_0)) (not thread_15_1))) ; barrier 0: thread 1
(assert (=> (and block_15_1_0 (not sync_15_1)) (not thread_15_0))) ; barrier 1: thread 0
(assert (=> (and block_15_1_1 (not sync_15_1)) (not thread_15_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_15_0_0 () Bool)
(declare-fun exec_15_0_1 () Bool)
(declare-fun exec_15_0_2 () Bool)
(declare-fun exec_15_0_3 () Bool)
(declare-fun exec_15_0_4 () Bool)
(declare-fun exec_15_0_5 () Bool)
(declare-fun exec_15_0_6 () Bool)
(declare-fun exec_15_0_7 () Bool)

(declare-fun exec_15_1_0 () Bool)
(declare-fun exec_15_1_1 () Bool)
(declare-fun exec_15_1_2 () Bool)
(declare-fun exec_15_1_3 () Bool)
(declare-fun exec_15_1_4 () Bool)
(declare-fun exec_15_1_5 () Bool)
(declare-fun exec_15_1_6 () Bool)

(assert (= exec_15_0_0 (and stmt_15_0_0 thread_15_0)))
(assert (= exec_15_0_1 (and stmt_15_0_1 thread_15_0)))
(assert (= exec_15_0_2 (and stmt_15_0_2 thread_15_0)))
(assert (= exec_15_0_3 (and stmt_15_0_3 thread_15_0)))
(assert (= exec_15_0_4 (and stmt_15_0_4 thread_15_0)))
(assert (= exec_15_0_5 (and stmt_15_0_5 thread_15_0)))
(assert (= exec_15_0_6 (and stmt_15_0_6 thread_15_0)))
(assert (= exec_15_0_7 (and stmt_15_0_7 thread_15_0)))

(assert (= exec_15_1_0 (and stmt_15_1_0 thread_15_1)))
(assert (= exec_15_1_1 (and stmt_15_1_1 thread_15_1)))
(assert (= exec_15_1_2 (and stmt_15_1_2 thread_15_1)))
(assert (= exec_15_1_3 (and stmt_15_1_3 thread_15_1)))
(assert (= exec_15_1_4 (and stmt_15_1_4 thread_15_1)))
(assert (= exec_15_1_5 (and stmt_15_1_5 thread_15_1)))
(assert (= exec_15_1_6 (and stmt_15_1_6 thread_15_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_15_0 () (_ BitVec 16))
(declare-fun accu_15_1 () (_ BitVec 16))

(assert (= accu_15_0 (ite exec_15_0_2 (select heap_14 #x0000) (ite exec_15_0_3 (bvadd accu_14_0 #x0001) accu_14_0))))
(assert (= accu_15_1 (ite exec_15_1_2 (select heap_14 #x0000) (ite exec_15_1_3 (bvadd accu_14_1 #x0001) accu_14_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_15_0 () (_ BitVec 16))
(declare-fun mem_15_1 () (_ BitVec 16))

(assert (= mem_15_0 mem_14_0))
(assert (= mem_15_1 mem_14_1))

; heap states - heap_<step>
(declare-fun heap_15 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_15 (ite exec_15_0_0 (store heap_14 #x0000 accu_14_0) (ite exec_15_0_4 (store heap_14 #x0000 accu_14_0) (ite exec_15_1_4 (store heap_14 #x0000 accu_14_1) heap_14)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 16
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_16 () Bool)

(assert (= exit_16 (or exit_15 exec_15_0_7 exec_15_1_6)))

; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_16_0_0 () Bool)
(declare-fun stmt_16_0_1 () Bool)
(declare-fun stmt_16_0_2 () Bool)
(declare-fun stmt_16_0_3 () Bool)
(declare-fun stmt_16_0_4 () Bool)
(declare-fun stmt_16_0_5 () Bool)
(declare-fun stmt_16_0_6 () Bool)
(declare-fun stmt_16_0_7 () Bool)

(declare-fun stmt_16_1_0 () Bool)
(declare-fun stmt_16_1_1 () Bool)
(declare-fun stmt_16_1_2 () Bool)
(declare-fun stmt_16_1_3 () Bool)
(declare-fun stmt_16_1_4 () Bool)
(declare-fun stmt_16_1_5 () Bool)
(declare-fun stmt_16_1_6 () Bool)

(assert (= stmt_16_0_0 (and stmt_15_0_0 (not exec_15_0_0))))
(assert (= stmt_16_0_1 (ite stmt_15_0_6 (and exec_15_0_6 (not (= accu_15_0 #x0000))) (ite stmt_15_0_0 exec_15_0_0 (and stmt_15_0_1 (not exec_15_0_1))))))
(assert (= stmt_16_0_2 (ite stmt_15_0_1 exec_15_0_1 (and stmt_15_0_2 (not exec_15_0_2)))))
(assert (= stmt_16_0_3 (ite stmt_15_0_2 exec_15_0_2 (and stmt_15_0_3 (not exec_15_0_3)))))
(assert (= stmt_16_0_4 (ite stmt_15_0_3 exec_15_0_3 (and stmt_15_0_4 (not exec_15_0_4)))))
(assert (= stmt_16_0_5 (ite stmt_15_0_4 exec_15_0_4 (and stmt_15_0_5 (not exec_15_0_5)))))
(assert (= stmt_16_0_6 (ite stmt_15_0_5 exec_15_0_5 (and stmt_15_0_6 (not exec_15_0_6)))))
(assert (= stmt_16_0_7 (ite stmt_15_0_6 (and exec_15_0_6 (not (not (= accu_15_0 #x0000)))) (and stmt_15_0_7 (not exec_15_0_7)))))

(assert (= stmt_16_1_0 (ite stmt_15_1_5 (and exec_15_1_5 (not (= accu_15_1 #x0000))) (and stmt_15_1_0 (not exec_15_1_0)))))
(assert (= stmt_16_1_1 (ite stmt_15_1_0 exec_15_1_0 (and stmt_15_1_1 (not exec_15_1_1)))))
(assert (= stmt_16_1_2 (ite stmt_15_1_1 exec_15_1_1 (and stmt_15_1_2 (not exec_15_1_2)))))
(assert (= stmt_16_1_3 (ite stmt_15_1_2 exec_15_1_2 (and stmt_15_1_3 (not exec_15_1_3)))))
(assert (= stmt_16_1_4 (ite stmt_15_1_3 exec_15_1_3 (and stmt_15_1_4 (not exec_15_1_4)))))
(assert (= stmt_16_1_5 (ite stmt_15_1_4 exec_15_1_4 (and stmt_15_1_5 (not exec_15_1_5)))))
(assert (= stmt_16_1_6 (ite stmt_15_1_5 (and exec_15_1_5 (not (not (= accu_15_1 #x0000)))) (and stmt_15_1_6 (not exec_15_1_6)))))

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_16_0 () Bool)
(declare-fun thread_16_1 () Bool)

(assert (or thread_16_0 thread_16_1 exit_16))
(assert (or (not thread_16_0) (not thread_16_1)))
(assert (or (not thread_16_0) (not exit_16)))
(assert (or (not thread_16_1) (not exit_16)))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_16_0_0 () Bool)
(declare-fun block_16_0_1 () Bool)
(declare-fun block_16_1_0 () Bool)
(declare-fun block_16_1_1 () Bool)

(assert (= block_16_0_0 (ite sync_15_0 false (or exec_15_0_1 block_15_0_0))))
(assert (= block_16_0_1 (ite sync_15_0 false (or exec_15_1_0 block_15_0_1))))
(assert (= block_16_1_0 (ite sync_15_1 false (or exec_15_0_5 block_15_1_0))))
(assert (= block_16_1_1 (ite sync_15_1 false (or exec_15_1_1 block_15_1_1))))

; sync variables - sync_<step>_<id>
(declare-fun sync_16_0 () Bool)
(declare-fun sync_16_1 () Bool)

(assert (= sync_16_0 (and block_16_0_0 block_16_0_1)))
(assert (= sync_16_1 (and block_16_1_0 block_16_1_1)))

; prevent scheduling of waiting threads
(assert (=> (and block_16_0_0 (not sync_16_0)) (not thread_16_0))) ; barrier 0: thread 0
(assert (=> (and block_16_0_1 (not sync_16_0)) (not thread_16_1))) ; barrier 0: thread 1
(assert (=> (and block_16_1_0 (not sync_16_1)) (not thread_16_0))) ; barrier 1: thread 0
(assert (=> (and block_16_1_1 (not sync_16_1)) (not thread_16_1))) ; barrier 1: thread 1

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_16_0_0 () Bool)
(declare-fun exec_16_0_1 () Bool)
(declare-fun exec_16_0_2 () Bool)
(declare-fun exec_16_0_3 () Bool)
(declare-fun exec_16_0_4 () Bool)
(declare-fun exec_16_0_5 () Bool)
(declare-fun exec_16_0_6 () Bool)
(declare-fun exec_16_0_7 () Bool)

(declare-fun exec_16_1_0 () Bool)
(declare-fun exec_16_1_1 () Bool)
(declare-fun exec_16_1_2 () Bool)
(declare-fun exec_16_1_3 () Bool)
(declare-fun exec_16_1_4 () Bool)
(declare-fun exec_16_1_5 () Bool)
(declare-fun exec_16_1_6 () Bool)

(assert (= exec_16_0_0 (and stmt_16_0_0 thread_16_0)))
(assert (= exec_16_0_1 (and stmt_16_0_1 thread_16_0)))
(assert (= exec_16_0_2 (and stmt_16_0_2 thread_16_0)))
(assert (= exec_16_0_3 (and stmt_16_0_3 thread_16_0)))
(assert (= exec_16_0_4 (and stmt_16_0_4 thread_16_0)))
(assert (= exec_16_0_5 (and stmt_16_0_5 thread_16_0)))
(assert (= exec_16_0_6 (and stmt_16_0_6 thread_16_0)))
(assert (= exec_16_0_7 (and stmt_16_0_7 thread_16_0)))

(assert (= exec_16_1_0 (and stmt_16_1_0 thread_16_1)))
(assert (= exec_16_1_1 (and stmt_16_1_1 thread_16_1)))
(assert (= exec_16_1_2 (and stmt_16_1_2 thread_16_1)))
(assert (= exec_16_1_3 (and stmt_16_1_3 thread_16_1)))
(assert (= exec_16_1_4 (and stmt_16_1_4 thread_16_1)))
(assert (= exec_16_1_5 (and stmt_16_1_5 thread_16_1)))
(assert (= exec_16_1_6 (and stmt_16_1_6 thread_16_1)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_16_0 () (_ BitVec 16))
(declare-fun accu_16_1 () (_ BitVec 16))

(assert (= accu_16_0 (ite exec_16_0_2 (select heap_15 #x0000) (ite exec_16_0_3 (bvadd accu_15_0 #x0001) accu_15_0))))
(assert (= accu_16_1 (ite exec_16_1_2 (select heap_15 #x0000) (ite exec_16_1_3 (bvadd accu_15_1 #x0001) accu_15_1))))

; mem states - mem_<step>_<thread>
(declare-fun mem_16_0 () (_ BitVec 16))
(declare-fun mem_16_1 () (_ BitVec 16))

(assert (= mem_16_0 mem_15_0))
(assert (= mem_16_1 mem_15_1))

; heap states - heap_<step>
(declare-fun heap_16 () (Array (_ BitVec 16) (_ BitVec 16)))

(assert (= heap_16 (ite exec_16_0_0 (store heap_15 #x0000 accu_15_0) (ite exec_16_0_4 (store heap_15 #x0000 accu_15_0) (ite exec_16_1_4 (store heap_15 #x0000 accu_15_1) heap_15)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; exit code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun exit-code () (_ BitVec 16))

(assert (= exit-code (ite exec_1_0_7 #x0001 (ite exec_1_1_6 #x0001 (ite exec_2_0_7 #x0001 (ite exec_2_1_6 #x0001 (ite exec_3_0_7 #x0001 (ite exec_3_1_6 #x0001 (ite exec_4_0_7 #x0001 (ite exec_4_1_6 #x0001 (ite exec_5_0_7 #x0001 (ite exec_5_1_6 #x0001 (ite exec_6_0_7 #x0001 (ite exec_6_1_6 #x0001 (ite exec_7_0_7 #x0001 (ite exec_7_1_6 #x0001 (ite exec_8_0_7 #x0001 (ite exec_8_1_6 #x0001 (ite exec_9_0_7 #x0001 (ite exec_9_1_6 #x0001 (ite exec_10_0_7 #x0001 (ite exec_10_1_6 #x0001 (ite exec_11_0_7 #x0001 (ite exec_11_1_6 #x0001 (ite exec_12_0_7 #x0001 (ite exec_12_1_6 #x0001 (ite exec_13_0_7 #x0001 (ite exec_13_1_6 #x0001 (ite exec_14_0_7 #x0001 (ite exec_14_1_6 #x0001 (ite exec_15_0_7 #x0001 (ite exec_15_1_6 #x0001 (ite exec_16_0_7 #x0001 (ite exec_16_1_6 #x0001 #x0000))))))))))))))))))))))))))))))))))
