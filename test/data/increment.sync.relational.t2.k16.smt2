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

; exit code
(declare-fun exit-code () (_ BitVec 16))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_1_0 () (_ BitVec 16))
(declare-fun accu_1_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_1_0 () (_ BitVec 16))
(declare-fun mem_1_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_0 (= heap_1 (store heap_0 #x0000 accu_0_0))))
(assert (=> exec_1_0_0 (and (not stmt_2_0_0) stmt_2_0_1 (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4) (not stmt_2_0_5) (not stmt_2_0_6) (not stmt_2_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_1_0_1 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_1 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_1 (= heap_1 heap_0)))
(assert (=> exec_1_0_1 (and (not stmt_2_0_0) (not stmt_2_0_1) stmt_2_0_2 (not stmt_2_0_3) (not stmt_2_0_4) (not stmt_2_0_5) (not stmt_2_0_6) (not stmt_2_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_1_0_2 (= accu_1_0 (select heap_0 #x0000))))
(assert (=> exec_1_0_2 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_2 (= heap_1 heap_0)))
(assert (=> exec_1_0_2 (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) stmt_2_0_3 (not stmt_2_0_4) (not stmt_2_0_5) (not stmt_2_0_6) (not stmt_2_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_1_0_3 (= accu_1_0 (bvadd accu_0_0 #x0001))))
(assert (=> exec_1_0_3 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_3 (= heap_1 heap_0)))
(assert (=> exec_1_0_3 (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) stmt_2_0_4 (not stmt_2_0_5) (not stmt_2_0_6) (not stmt_2_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_1_0_4 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_4 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_4 (= heap_1 (store heap_0 #x0000 accu_0_0))))
(assert (=> exec_1_0_4 (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4) stmt_2_0_5 (not stmt_2_0_6) (not stmt_2_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_1_0_5 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_5 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_5 (= heap_1 heap_0)))
(assert (=> exec_1_0_5 (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4) (not stmt_2_0_5) stmt_2_0_6 (not stmt_2_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_1_0_6 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_6 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_6 (= heap_1 heap_0)))
(assert (=> exec_1_0_6 (ite (not (= accu_1_0 #x0000)) (and (not stmt_2_0_0) stmt_2_0_1 (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4) (not stmt_2_0_5) (not stmt_2_0_6) (not stmt_2_0_7)) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4) (not stmt_2_0_5) (not stmt_2_0_6) stmt_2_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_1_0_7 (= accu_1_0 accu_0_0)))
(assert (=> exec_1_0_7 (= mem_1_0 mem_0_0)))
(assert (=> exec_1_0_7 (= heap_1 heap_0)))
(assert (=> exec_1_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_0 (= heap_1 heap_0)))
(assert (=> exec_1_1_0 (and (not stmt_2_1_0) stmt_2_1_1 (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5) (not stmt_2_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_1_1_1 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_1 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_1 (= heap_1 heap_0)))
(assert (=> exec_1_1_1 (and (not stmt_2_1_0) (not stmt_2_1_1) stmt_2_1_2 (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5) (not stmt_2_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_1_1_2 (= accu_1_1 (select heap_0 #x0000))))
(assert (=> exec_1_1_2 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_2 (= heap_1 heap_0)))
(assert (=> exec_1_1_2 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) stmt_2_1_3 (not stmt_2_1_4) (not stmt_2_1_5) (not stmt_2_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_1_1_3 (= accu_1_1 (bvadd accu_0_1 #x0001))))
(assert (=> exec_1_1_3 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_3 (= heap_1 heap_0)))
(assert (=> exec_1_1_3 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) stmt_2_1_4 (not stmt_2_1_5) (not stmt_2_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_1_1_4 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_4 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_4 (= heap_1 (store heap_0 #x0000 accu_0_1))))
(assert (=> exec_1_1_4 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) stmt_2_1_5 (not stmt_2_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_1_1_5 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_5 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_5 (= heap_1 heap_0)))
(assert (=> exec_1_1_5 (ite (not (= accu_1_1 #x0000)) (and stmt_2_1_0 (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5) (not stmt_2_1_6)) (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5) stmt_2_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_1_1_6 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_6 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_6 (= heap_1 heap_0)))
(assert (=> exec_1_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_1_0 () Bool)
(assert (= preserve_1_0 (not thread_1_0)))

(assert (=> preserve_1_0 (= accu_1_0 accu_0_0)))
(assert (=> preserve_1_0 (= mem_1_0 mem_0_0)))

(assert (=> preserve_1_0 (= stmt_2_0_0 stmt_1_0_0)))
(assert (=> preserve_1_0 (= stmt_2_0_1 stmt_1_0_1)))
(assert (=> preserve_1_0 (= stmt_2_0_2 stmt_1_0_2)))
(assert (=> preserve_1_0 (= stmt_2_0_3 stmt_1_0_3)))
(assert (=> preserve_1_0 (= stmt_2_0_4 stmt_1_0_4)))
(assert (=> preserve_1_0 (= stmt_2_0_5 stmt_1_0_5)))
(assert (=> preserve_1_0 (= stmt_2_0_6 stmt_1_0_6)))
(assert (=> preserve_1_0 (= stmt_2_0_7 stmt_1_0_7)))

(declare-fun preserve_1_1 () Bool)
(assert (= preserve_1_1 (not thread_1_1)))

(assert (=> preserve_1_1 (= accu_1_1 accu_0_1)))
(assert (=> preserve_1_1 (= mem_1_1 mem_0_1)))

(assert (=> preserve_1_1 (= stmt_2_1_0 stmt_1_1_0)))
(assert (=> preserve_1_1 (= stmt_2_1_1 stmt_1_1_1)))
(assert (=> preserve_1_1 (= stmt_2_1_2 stmt_1_1_2)))
(assert (=> preserve_1_1 (= stmt_2_1_3 stmt_1_1_3)))
(assert (=> preserve_1_1 (= stmt_2_1_4 stmt_1_1_4)))
(assert (=> preserve_1_1 (= stmt_2_1_5 stmt_1_1_5)))
(assert (=> preserve_1_1 (= stmt_2_1_6 stmt_1_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_2 () Bool)

(assert (= exit_2 (or exec_1_0_7 exec_1_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_2_0 () (_ BitVec 16))
(declare-fun accu_2_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_2_0 () (_ BitVec 16))
(declare-fun mem_2_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_2_0_0 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_0 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_0 (= heap_2 (store heap_1 #x0000 accu_1_0))))
(assert (=> exec_2_0_0 (and (not stmt_3_0_0) stmt_3_0_1 (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4) (not stmt_3_0_5) (not stmt_3_0_6) (not stmt_3_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_2_0_1 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_1 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_1 (= heap_2 heap_1)))
(assert (=> exec_2_0_1 (and (not stmt_3_0_0) (not stmt_3_0_1) stmt_3_0_2 (not stmt_3_0_3) (not stmt_3_0_4) (not stmt_3_0_5) (not stmt_3_0_6) (not stmt_3_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_2_0_2 (= accu_2_0 (select heap_1 #x0000))))
(assert (=> exec_2_0_2 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_2 (= heap_2 heap_1)))
(assert (=> exec_2_0_2 (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) stmt_3_0_3 (not stmt_3_0_4) (not stmt_3_0_5) (not stmt_3_0_6) (not stmt_3_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_2_0_3 (= accu_2_0 (bvadd accu_1_0 #x0001))))
(assert (=> exec_2_0_3 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_3 (= heap_2 heap_1)))
(assert (=> exec_2_0_3 (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) stmt_3_0_4 (not stmt_3_0_5) (not stmt_3_0_6) (not stmt_3_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_2_0_4 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_4 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_4 (= heap_2 (store heap_1 #x0000 accu_1_0))))
(assert (=> exec_2_0_4 (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4) stmt_3_0_5 (not stmt_3_0_6) (not stmt_3_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_2_0_5 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_5 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_5 (= heap_2 heap_1)))
(assert (=> exec_2_0_5 (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4) (not stmt_3_0_5) stmt_3_0_6 (not stmt_3_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_2_0_6 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_6 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_6 (= heap_2 heap_1)))
(assert (=> exec_2_0_6 (ite (not (= accu_2_0 #x0000)) (and (not stmt_3_0_0) stmt_3_0_1 (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4) (not stmt_3_0_5) (not stmt_3_0_6) (not stmt_3_0_7)) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4) (not stmt_3_0_5) (not stmt_3_0_6) stmt_3_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_2_0_7 (= accu_2_0 accu_1_0)))
(assert (=> exec_2_0_7 (= mem_2_0 mem_1_0)))
(assert (=> exec_2_0_7 (= heap_2 heap_1)))
(assert (=> exec_2_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_2_1_0 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_0 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_0 (= heap_2 heap_1)))
(assert (=> exec_2_1_0 (and (not stmt_3_1_0) stmt_3_1_1 (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5) (not stmt_3_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_2_1_1 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_1 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_1 (= heap_2 heap_1)))
(assert (=> exec_2_1_1 (and (not stmt_3_1_0) (not stmt_3_1_1) stmt_3_1_2 (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5) (not stmt_3_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_2_1_2 (= accu_2_1 (select heap_1 #x0000))))
(assert (=> exec_2_1_2 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_2 (= heap_2 heap_1)))
(assert (=> exec_2_1_2 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) stmt_3_1_3 (not stmt_3_1_4) (not stmt_3_1_5) (not stmt_3_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_2_1_3 (= accu_2_1 (bvadd accu_1_1 #x0001))))
(assert (=> exec_2_1_3 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_3 (= heap_2 heap_1)))
(assert (=> exec_2_1_3 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) stmt_3_1_4 (not stmt_3_1_5) (not stmt_3_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_2_1_4 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_4 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_4 (= heap_2 (store heap_1 #x0000 accu_1_1))))
(assert (=> exec_2_1_4 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) stmt_3_1_5 (not stmt_3_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_2_1_5 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_5 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_5 (= heap_2 heap_1)))
(assert (=> exec_2_1_5 (ite (not (= accu_2_1 #x0000)) (and stmt_3_1_0 (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5) (not stmt_3_1_6)) (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5) stmt_3_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_2_1_6 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_6 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_6 (= heap_2 heap_1)))
(assert (=> exec_2_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_2_0 () Bool)
(assert (= preserve_2_0 (not thread_2_0)))

(assert (=> preserve_2_0 (= accu_2_0 accu_1_0)))
(assert (=> preserve_2_0 (= mem_2_0 mem_1_0)))

(assert (=> preserve_2_0 (= stmt_3_0_0 stmt_2_0_0)))
(assert (=> preserve_2_0 (= stmt_3_0_1 stmt_2_0_1)))
(assert (=> preserve_2_0 (= stmt_3_0_2 stmt_2_0_2)))
(assert (=> preserve_2_0 (= stmt_3_0_3 stmt_2_0_3)))
(assert (=> preserve_2_0 (= stmt_3_0_4 stmt_2_0_4)))
(assert (=> preserve_2_0 (= stmt_3_0_5 stmt_2_0_5)))
(assert (=> preserve_2_0 (= stmt_3_0_6 stmt_2_0_6)))
(assert (=> preserve_2_0 (= stmt_3_0_7 stmt_2_0_7)))

(declare-fun preserve_2_1 () Bool)
(assert (= preserve_2_1 (not thread_2_1)))

(assert (=> preserve_2_1 (= accu_2_1 accu_1_1)))
(assert (=> preserve_2_1 (= mem_2_1 mem_1_1)))

(assert (=> preserve_2_1 (= stmt_3_1_0 stmt_2_1_0)))
(assert (=> preserve_2_1 (= stmt_3_1_1 stmt_2_1_1)))
(assert (=> preserve_2_1 (= stmt_3_1_2 stmt_2_1_2)))
(assert (=> preserve_2_1 (= stmt_3_1_3 stmt_2_1_3)))
(assert (=> preserve_2_1 (= stmt_3_1_4 stmt_2_1_4)))
(assert (=> preserve_2_1 (= stmt_3_1_5 stmt_2_1_5)))
(assert (=> preserve_2_1 (= stmt_3_1_6 stmt_2_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_3 () Bool)

(assert (= exit_3 (or exit_2 exec_2_0_7 exec_2_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_3_0 () (_ BitVec 16))
(declare-fun accu_3_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_3_0 () (_ BitVec 16))
(declare-fun mem_3_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_3_0_0 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_0 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_0 (= heap_3 (store heap_2 #x0000 accu_2_0))))
(assert (=> exec_3_0_0 (and (not stmt_4_0_0) stmt_4_0_1 (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4) (not stmt_4_0_5) (not stmt_4_0_6) (not stmt_4_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_3_0_1 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_1 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_1 (= heap_3 heap_2)))
(assert (=> exec_3_0_1 (and (not stmt_4_0_0) (not stmt_4_0_1) stmt_4_0_2 (not stmt_4_0_3) (not stmt_4_0_4) (not stmt_4_0_5) (not stmt_4_0_6) (not stmt_4_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_3_0_2 (= accu_3_0 (select heap_2 #x0000))))
(assert (=> exec_3_0_2 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_2 (= heap_3 heap_2)))
(assert (=> exec_3_0_2 (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) stmt_4_0_3 (not stmt_4_0_4) (not stmt_4_0_5) (not stmt_4_0_6) (not stmt_4_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_3_0_3 (= accu_3_0 (bvadd accu_2_0 #x0001))))
(assert (=> exec_3_0_3 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_3 (= heap_3 heap_2)))
(assert (=> exec_3_0_3 (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) stmt_4_0_4 (not stmt_4_0_5) (not stmt_4_0_6) (not stmt_4_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_3_0_4 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_4 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_4 (= heap_3 (store heap_2 #x0000 accu_2_0))))
(assert (=> exec_3_0_4 (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4) stmt_4_0_5 (not stmt_4_0_6) (not stmt_4_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_3_0_5 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_5 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_5 (= heap_3 heap_2)))
(assert (=> exec_3_0_5 (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4) (not stmt_4_0_5) stmt_4_0_6 (not stmt_4_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_3_0_6 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_6 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_6 (= heap_3 heap_2)))
(assert (=> exec_3_0_6 (ite (not (= accu_3_0 #x0000)) (and (not stmt_4_0_0) stmt_4_0_1 (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4) (not stmt_4_0_5) (not stmt_4_0_6) (not stmt_4_0_7)) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4) (not stmt_4_0_5) (not stmt_4_0_6) stmt_4_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_3_0_7 (= accu_3_0 accu_2_0)))
(assert (=> exec_3_0_7 (= mem_3_0 mem_2_0)))
(assert (=> exec_3_0_7 (= heap_3 heap_2)))
(assert (=> exec_3_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_3_1_0 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_0 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_0 (= heap_3 heap_2)))
(assert (=> exec_3_1_0 (and (not stmt_4_1_0) stmt_4_1_1 (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5) (not stmt_4_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_3_1_1 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_1 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_1 (= heap_3 heap_2)))
(assert (=> exec_3_1_1 (and (not stmt_4_1_0) (not stmt_4_1_1) stmt_4_1_2 (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5) (not stmt_4_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_3_1_2 (= accu_3_1 (select heap_2 #x0000))))
(assert (=> exec_3_1_2 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_2 (= heap_3 heap_2)))
(assert (=> exec_3_1_2 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) stmt_4_1_3 (not stmt_4_1_4) (not stmt_4_1_5) (not stmt_4_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_3_1_3 (= accu_3_1 (bvadd accu_2_1 #x0001))))
(assert (=> exec_3_1_3 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_3 (= heap_3 heap_2)))
(assert (=> exec_3_1_3 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) stmt_4_1_4 (not stmt_4_1_5) (not stmt_4_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_3_1_4 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_4 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_4 (= heap_3 (store heap_2 #x0000 accu_2_1))))
(assert (=> exec_3_1_4 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) stmt_4_1_5 (not stmt_4_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_3_1_5 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_5 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_5 (= heap_3 heap_2)))
(assert (=> exec_3_1_5 (ite (not (= accu_3_1 #x0000)) (and stmt_4_1_0 (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5) (not stmt_4_1_6)) (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5) stmt_4_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_3_1_6 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_6 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_6 (= heap_3 heap_2)))
(assert (=> exec_3_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_3_0 () Bool)
(assert (= preserve_3_0 (not thread_3_0)))

(assert (=> preserve_3_0 (= accu_3_0 accu_2_0)))
(assert (=> preserve_3_0 (= mem_3_0 mem_2_0)))

(assert (=> preserve_3_0 (= stmt_4_0_0 stmt_3_0_0)))
(assert (=> preserve_3_0 (= stmt_4_0_1 stmt_3_0_1)))
(assert (=> preserve_3_0 (= stmt_4_0_2 stmt_3_0_2)))
(assert (=> preserve_3_0 (= stmt_4_0_3 stmt_3_0_3)))
(assert (=> preserve_3_0 (= stmt_4_0_4 stmt_3_0_4)))
(assert (=> preserve_3_0 (= stmt_4_0_5 stmt_3_0_5)))
(assert (=> preserve_3_0 (= stmt_4_0_6 stmt_3_0_6)))
(assert (=> preserve_3_0 (= stmt_4_0_7 stmt_3_0_7)))

(declare-fun preserve_3_1 () Bool)
(assert (= preserve_3_1 (not thread_3_1)))

(assert (=> preserve_3_1 (= accu_3_1 accu_2_1)))
(assert (=> preserve_3_1 (= mem_3_1 mem_2_1)))

(assert (=> preserve_3_1 (= stmt_4_1_0 stmt_3_1_0)))
(assert (=> preserve_3_1 (= stmt_4_1_1 stmt_3_1_1)))
(assert (=> preserve_3_1 (= stmt_4_1_2 stmt_3_1_2)))
(assert (=> preserve_3_1 (= stmt_4_1_3 stmt_3_1_3)))
(assert (=> preserve_3_1 (= stmt_4_1_4 stmt_3_1_4)))
(assert (=> preserve_3_1 (= stmt_4_1_5 stmt_3_1_5)))
(assert (=> preserve_3_1 (= stmt_4_1_6 stmt_3_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_4 () Bool)

(assert (= exit_4 (or exit_3 exec_3_0_7 exec_3_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_4_0 () (_ BitVec 16))
(declare-fun accu_4_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_4_0 () (_ BitVec 16))
(declare-fun mem_4_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_4_0_0 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_0 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_0 (= heap_4 (store heap_3 #x0000 accu_3_0))))
(assert (=> exec_4_0_0 (and (not stmt_5_0_0) stmt_5_0_1 (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4) (not stmt_5_0_5) (not stmt_5_0_6) (not stmt_5_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_4_0_1 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_1 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_1 (= heap_4 heap_3)))
(assert (=> exec_4_0_1 (and (not stmt_5_0_0) (not stmt_5_0_1) stmt_5_0_2 (not stmt_5_0_3) (not stmt_5_0_4) (not stmt_5_0_5) (not stmt_5_0_6) (not stmt_5_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_4_0_2 (= accu_4_0 (select heap_3 #x0000))))
(assert (=> exec_4_0_2 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_2 (= heap_4 heap_3)))
(assert (=> exec_4_0_2 (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) stmt_5_0_3 (not stmt_5_0_4) (not stmt_5_0_5) (not stmt_5_0_6) (not stmt_5_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_4_0_3 (= accu_4_0 (bvadd accu_3_0 #x0001))))
(assert (=> exec_4_0_3 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_3 (= heap_4 heap_3)))
(assert (=> exec_4_0_3 (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) stmt_5_0_4 (not stmt_5_0_5) (not stmt_5_0_6) (not stmt_5_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_4_0_4 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_4 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_4 (= heap_4 (store heap_3 #x0000 accu_3_0))))
(assert (=> exec_4_0_4 (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4) stmt_5_0_5 (not stmt_5_0_6) (not stmt_5_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_4_0_5 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_5 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_5 (= heap_4 heap_3)))
(assert (=> exec_4_0_5 (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4) (not stmt_5_0_5) stmt_5_0_6 (not stmt_5_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_4_0_6 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_6 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_6 (= heap_4 heap_3)))
(assert (=> exec_4_0_6 (ite (not (= accu_4_0 #x0000)) (and (not stmt_5_0_0) stmt_5_0_1 (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4) (not stmt_5_0_5) (not stmt_5_0_6) (not stmt_5_0_7)) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4) (not stmt_5_0_5) (not stmt_5_0_6) stmt_5_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_4_0_7 (= accu_4_0 accu_3_0)))
(assert (=> exec_4_0_7 (= mem_4_0 mem_3_0)))
(assert (=> exec_4_0_7 (= heap_4 heap_3)))
(assert (=> exec_4_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_4_1_0 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_0 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_0 (= heap_4 heap_3)))
(assert (=> exec_4_1_0 (and (not stmt_5_1_0) stmt_5_1_1 (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5) (not stmt_5_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_4_1_1 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_1 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_1 (= heap_4 heap_3)))
(assert (=> exec_4_1_1 (and (not stmt_5_1_0) (not stmt_5_1_1) stmt_5_1_2 (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5) (not stmt_5_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_4_1_2 (= accu_4_1 (select heap_3 #x0000))))
(assert (=> exec_4_1_2 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_2 (= heap_4 heap_3)))
(assert (=> exec_4_1_2 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) stmt_5_1_3 (not stmt_5_1_4) (not stmt_5_1_5) (not stmt_5_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_4_1_3 (= accu_4_1 (bvadd accu_3_1 #x0001))))
(assert (=> exec_4_1_3 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_3 (= heap_4 heap_3)))
(assert (=> exec_4_1_3 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) stmt_5_1_4 (not stmt_5_1_5) (not stmt_5_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_4_1_4 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_4 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_4 (= heap_4 (store heap_3 #x0000 accu_3_1))))
(assert (=> exec_4_1_4 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) stmt_5_1_5 (not stmt_5_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_4_1_5 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_5 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_5 (= heap_4 heap_3)))
(assert (=> exec_4_1_5 (ite (not (= accu_4_1 #x0000)) (and stmt_5_1_0 (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5) (not stmt_5_1_6)) (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5) stmt_5_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_4_1_6 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_6 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_6 (= heap_4 heap_3)))
(assert (=> exec_4_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_4_0 () Bool)
(assert (= preserve_4_0 (not thread_4_0)))

(assert (=> preserve_4_0 (= accu_4_0 accu_3_0)))
(assert (=> preserve_4_0 (= mem_4_0 mem_3_0)))

(assert (=> preserve_4_0 (= stmt_5_0_0 stmt_4_0_0)))
(assert (=> preserve_4_0 (= stmt_5_0_1 stmt_4_0_1)))
(assert (=> preserve_4_0 (= stmt_5_0_2 stmt_4_0_2)))
(assert (=> preserve_4_0 (= stmt_5_0_3 stmt_4_0_3)))
(assert (=> preserve_4_0 (= stmt_5_0_4 stmt_4_0_4)))
(assert (=> preserve_4_0 (= stmt_5_0_5 stmt_4_0_5)))
(assert (=> preserve_4_0 (= stmt_5_0_6 stmt_4_0_6)))
(assert (=> preserve_4_0 (= stmt_5_0_7 stmt_4_0_7)))

(declare-fun preserve_4_1 () Bool)
(assert (= preserve_4_1 (not thread_4_1)))

(assert (=> preserve_4_1 (= accu_4_1 accu_3_1)))
(assert (=> preserve_4_1 (= mem_4_1 mem_3_1)))

(assert (=> preserve_4_1 (= stmt_5_1_0 stmt_4_1_0)))
(assert (=> preserve_4_1 (= stmt_5_1_1 stmt_4_1_1)))
(assert (=> preserve_4_1 (= stmt_5_1_2 stmt_4_1_2)))
(assert (=> preserve_4_1 (= stmt_5_1_3 stmt_4_1_3)))
(assert (=> preserve_4_1 (= stmt_5_1_4 stmt_4_1_4)))
(assert (=> preserve_4_1 (= stmt_5_1_5 stmt_4_1_5)))
(assert (=> preserve_4_1 (= stmt_5_1_6 stmt_4_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_5 () Bool)

(assert (= exit_5 (or exit_4 exec_4_0_7 exec_4_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_5_0 () (_ BitVec 16))
(declare-fun accu_5_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_5_0 () (_ BitVec 16))
(declare-fun mem_5_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_5_0_0 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_0 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_0 (= heap_5 (store heap_4 #x0000 accu_4_0))))
(assert (=> exec_5_0_0 (and (not stmt_6_0_0) stmt_6_0_1 (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4) (not stmt_6_0_5) (not stmt_6_0_6) (not stmt_6_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_5_0_1 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_1 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_1 (= heap_5 heap_4)))
(assert (=> exec_5_0_1 (and (not stmt_6_0_0) (not stmt_6_0_1) stmt_6_0_2 (not stmt_6_0_3) (not stmt_6_0_4) (not stmt_6_0_5) (not stmt_6_0_6) (not stmt_6_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_5_0_2 (= accu_5_0 (select heap_4 #x0000))))
(assert (=> exec_5_0_2 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_2 (= heap_5 heap_4)))
(assert (=> exec_5_0_2 (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) stmt_6_0_3 (not stmt_6_0_4) (not stmt_6_0_5) (not stmt_6_0_6) (not stmt_6_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_5_0_3 (= accu_5_0 (bvadd accu_4_0 #x0001))))
(assert (=> exec_5_0_3 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_3 (= heap_5 heap_4)))
(assert (=> exec_5_0_3 (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) stmt_6_0_4 (not stmt_6_0_5) (not stmt_6_0_6) (not stmt_6_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_5_0_4 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_4 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_4 (= heap_5 (store heap_4 #x0000 accu_4_0))))
(assert (=> exec_5_0_4 (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4) stmt_6_0_5 (not stmt_6_0_6) (not stmt_6_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_5_0_5 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_5 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_5 (= heap_5 heap_4)))
(assert (=> exec_5_0_5 (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4) (not stmt_6_0_5) stmt_6_0_6 (not stmt_6_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_5_0_6 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_6 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_6 (= heap_5 heap_4)))
(assert (=> exec_5_0_6 (ite (not (= accu_5_0 #x0000)) (and (not stmt_6_0_0) stmt_6_0_1 (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4) (not stmt_6_0_5) (not stmt_6_0_6) (not stmt_6_0_7)) (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4) (not stmt_6_0_5) (not stmt_6_0_6) stmt_6_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_5_0_7 (= accu_5_0 accu_4_0)))
(assert (=> exec_5_0_7 (= mem_5_0 mem_4_0)))
(assert (=> exec_5_0_7 (= heap_5 heap_4)))
(assert (=> exec_5_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_5_1_0 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_0 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_0 (= heap_5 heap_4)))
(assert (=> exec_5_1_0 (and (not stmt_6_1_0) stmt_6_1_1 (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5) (not stmt_6_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_5_1_1 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_1 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_1 (= heap_5 heap_4)))
(assert (=> exec_5_1_1 (and (not stmt_6_1_0) (not stmt_6_1_1) stmt_6_1_2 (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5) (not stmt_6_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_5_1_2 (= accu_5_1 (select heap_4 #x0000))))
(assert (=> exec_5_1_2 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_2 (= heap_5 heap_4)))
(assert (=> exec_5_1_2 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) stmt_6_1_3 (not stmt_6_1_4) (not stmt_6_1_5) (not stmt_6_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_5_1_3 (= accu_5_1 (bvadd accu_4_1 #x0001))))
(assert (=> exec_5_1_3 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_3 (= heap_5 heap_4)))
(assert (=> exec_5_1_3 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) stmt_6_1_4 (not stmt_6_1_5) (not stmt_6_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_5_1_4 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_4 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_4 (= heap_5 (store heap_4 #x0000 accu_4_1))))
(assert (=> exec_5_1_4 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) stmt_6_1_5 (not stmt_6_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_5_1_5 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_5 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_5 (= heap_5 heap_4)))
(assert (=> exec_5_1_5 (ite (not (= accu_5_1 #x0000)) (and stmt_6_1_0 (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5) (not stmt_6_1_6)) (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5) stmt_6_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_5_1_6 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_6 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_6 (= heap_5 heap_4)))
(assert (=> exec_5_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_5_0 () Bool)
(assert (= preserve_5_0 (not thread_5_0)))

(assert (=> preserve_5_0 (= accu_5_0 accu_4_0)))
(assert (=> preserve_5_0 (= mem_5_0 mem_4_0)))

(assert (=> preserve_5_0 (= stmt_6_0_0 stmt_5_0_0)))
(assert (=> preserve_5_0 (= stmt_6_0_1 stmt_5_0_1)))
(assert (=> preserve_5_0 (= stmt_6_0_2 stmt_5_0_2)))
(assert (=> preserve_5_0 (= stmt_6_0_3 stmt_5_0_3)))
(assert (=> preserve_5_0 (= stmt_6_0_4 stmt_5_0_4)))
(assert (=> preserve_5_0 (= stmt_6_0_5 stmt_5_0_5)))
(assert (=> preserve_5_0 (= stmt_6_0_6 stmt_5_0_6)))
(assert (=> preserve_5_0 (= stmt_6_0_7 stmt_5_0_7)))

(declare-fun preserve_5_1 () Bool)
(assert (= preserve_5_1 (not thread_5_1)))

(assert (=> preserve_5_1 (= accu_5_1 accu_4_1)))
(assert (=> preserve_5_1 (= mem_5_1 mem_4_1)))

(assert (=> preserve_5_1 (= stmt_6_1_0 stmt_5_1_0)))
(assert (=> preserve_5_1 (= stmt_6_1_1 stmt_5_1_1)))
(assert (=> preserve_5_1 (= stmt_6_1_2 stmt_5_1_2)))
(assert (=> preserve_5_1 (= stmt_6_1_3 stmt_5_1_3)))
(assert (=> preserve_5_1 (= stmt_6_1_4 stmt_5_1_4)))
(assert (=> preserve_5_1 (= stmt_6_1_5 stmt_5_1_5)))
(assert (=> preserve_5_1 (= stmt_6_1_6 stmt_5_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_6 () Bool)

(assert (= exit_6 (or exit_5 exec_5_0_7 exec_5_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_6_0 () (_ BitVec 16))
(declare-fun accu_6_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_6_0 () (_ BitVec 16))
(declare-fun mem_6_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_6_0_0 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_0 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_0 (= heap_6 (store heap_5 #x0000 accu_5_0))))
(assert (=> exec_6_0_0 (and (not stmt_7_0_0) stmt_7_0_1 (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4) (not stmt_7_0_5) (not stmt_7_0_6) (not stmt_7_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_6_0_1 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_1 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_1 (= heap_6 heap_5)))
(assert (=> exec_6_0_1 (and (not stmt_7_0_0) (not stmt_7_0_1) stmt_7_0_2 (not stmt_7_0_3) (not stmt_7_0_4) (not stmt_7_0_5) (not stmt_7_0_6) (not stmt_7_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_6_0_2 (= accu_6_0 (select heap_5 #x0000))))
(assert (=> exec_6_0_2 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_2 (= heap_6 heap_5)))
(assert (=> exec_6_0_2 (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) stmt_7_0_3 (not stmt_7_0_4) (not stmt_7_0_5) (not stmt_7_0_6) (not stmt_7_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_6_0_3 (= accu_6_0 (bvadd accu_5_0 #x0001))))
(assert (=> exec_6_0_3 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_3 (= heap_6 heap_5)))
(assert (=> exec_6_0_3 (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) stmt_7_0_4 (not stmt_7_0_5) (not stmt_7_0_6) (not stmt_7_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_6_0_4 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_4 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_4 (= heap_6 (store heap_5 #x0000 accu_5_0))))
(assert (=> exec_6_0_4 (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4) stmt_7_0_5 (not stmt_7_0_6) (not stmt_7_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_6_0_5 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_5 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_5 (= heap_6 heap_5)))
(assert (=> exec_6_0_5 (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4) (not stmt_7_0_5) stmt_7_0_6 (not stmt_7_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_6_0_6 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_6 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_6 (= heap_6 heap_5)))
(assert (=> exec_6_0_6 (ite (not (= accu_6_0 #x0000)) (and (not stmt_7_0_0) stmt_7_0_1 (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4) (not stmt_7_0_5) (not stmt_7_0_6) (not stmt_7_0_7)) (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4) (not stmt_7_0_5) (not stmt_7_0_6) stmt_7_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_6_0_7 (= accu_6_0 accu_5_0)))
(assert (=> exec_6_0_7 (= mem_6_0 mem_5_0)))
(assert (=> exec_6_0_7 (= heap_6 heap_5)))
(assert (=> exec_6_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_6_1_0 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_0 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_0 (= heap_6 heap_5)))
(assert (=> exec_6_1_0 (and (not stmt_7_1_0) stmt_7_1_1 (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5) (not stmt_7_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_6_1_1 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_1 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_1 (= heap_6 heap_5)))
(assert (=> exec_6_1_1 (and (not stmt_7_1_0) (not stmt_7_1_1) stmt_7_1_2 (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5) (not stmt_7_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_6_1_2 (= accu_6_1 (select heap_5 #x0000))))
(assert (=> exec_6_1_2 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_2 (= heap_6 heap_5)))
(assert (=> exec_6_1_2 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) stmt_7_1_3 (not stmt_7_1_4) (not stmt_7_1_5) (not stmt_7_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_6_1_3 (= accu_6_1 (bvadd accu_5_1 #x0001))))
(assert (=> exec_6_1_3 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_3 (= heap_6 heap_5)))
(assert (=> exec_6_1_3 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) stmt_7_1_4 (not stmt_7_1_5) (not stmt_7_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_6_1_4 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_4 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_4 (= heap_6 (store heap_5 #x0000 accu_5_1))))
(assert (=> exec_6_1_4 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) stmt_7_1_5 (not stmt_7_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_6_1_5 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_5 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_5 (= heap_6 heap_5)))
(assert (=> exec_6_1_5 (ite (not (= accu_6_1 #x0000)) (and stmt_7_1_0 (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5) (not stmt_7_1_6)) (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5) stmt_7_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_6_1_6 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_6 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_6 (= heap_6 heap_5)))
(assert (=> exec_6_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_6_0 () Bool)
(assert (= preserve_6_0 (not thread_6_0)))

(assert (=> preserve_6_0 (= accu_6_0 accu_5_0)))
(assert (=> preserve_6_0 (= mem_6_0 mem_5_0)))

(assert (=> preserve_6_0 (= stmt_7_0_0 stmt_6_0_0)))
(assert (=> preserve_6_0 (= stmt_7_0_1 stmt_6_0_1)))
(assert (=> preserve_6_0 (= stmt_7_0_2 stmt_6_0_2)))
(assert (=> preserve_6_0 (= stmt_7_0_3 stmt_6_0_3)))
(assert (=> preserve_6_0 (= stmt_7_0_4 stmt_6_0_4)))
(assert (=> preserve_6_0 (= stmt_7_0_5 stmt_6_0_5)))
(assert (=> preserve_6_0 (= stmt_7_0_6 stmt_6_0_6)))
(assert (=> preserve_6_0 (= stmt_7_0_7 stmt_6_0_7)))

(declare-fun preserve_6_1 () Bool)
(assert (= preserve_6_1 (not thread_6_1)))

(assert (=> preserve_6_1 (= accu_6_1 accu_5_1)))
(assert (=> preserve_6_1 (= mem_6_1 mem_5_1)))

(assert (=> preserve_6_1 (= stmt_7_1_0 stmt_6_1_0)))
(assert (=> preserve_6_1 (= stmt_7_1_1 stmt_6_1_1)))
(assert (=> preserve_6_1 (= stmt_7_1_2 stmt_6_1_2)))
(assert (=> preserve_6_1 (= stmt_7_1_3 stmt_6_1_3)))
(assert (=> preserve_6_1 (= stmt_7_1_4 stmt_6_1_4)))
(assert (=> preserve_6_1 (= stmt_7_1_5 stmt_6_1_5)))
(assert (=> preserve_6_1 (= stmt_7_1_6 stmt_6_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_7 () Bool)

(assert (= exit_7 (or exit_6 exec_6_0_7 exec_6_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_7_0 () (_ BitVec 16))
(declare-fun accu_7_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_7_0 () (_ BitVec 16))
(declare-fun mem_7_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_7_0_0 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_0 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_0 (= heap_7 (store heap_6 #x0000 accu_6_0))))
(assert (=> exec_7_0_0 (and (not stmt_8_0_0) stmt_8_0_1 (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4) (not stmt_8_0_5) (not stmt_8_0_6) (not stmt_8_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_7_0_1 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_1 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_1 (= heap_7 heap_6)))
(assert (=> exec_7_0_1 (and (not stmt_8_0_0) (not stmt_8_0_1) stmt_8_0_2 (not stmt_8_0_3) (not stmt_8_0_4) (not stmt_8_0_5) (not stmt_8_0_6) (not stmt_8_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_7_0_2 (= accu_7_0 (select heap_6 #x0000))))
(assert (=> exec_7_0_2 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_2 (= heap_7 heap_6)))
(assert (=> exec_7_0_2 (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) stmt_8_0_3 (not stmt_8_0_4) (not stmt_8_0_5) (not stmt_8_0_6) (not stmt_8_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_7_0_3 (= accu_7_0 (bvadd accu_6_0 #x0001))))
(assert (=> exec_7_0_3 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_3 (= heap_7 heap_6)))
(assert (=> exec_7_0_3 (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) stmt_8_0_4 (not stmt_8_0_5) (not stmt_8_0_6) (not stmt_8_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_7_0_4 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_4 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_4 (= heap_7 (store heap_6 #x0000 accu_6_0))))
(assert (=> exec_7_0_4 (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4) stmt_8_0_5 (not stmt_8_0_6) (not stmt_8_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_7_0_5 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_5 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_5 (= heap_7 heap_6)))
(assert (=> exec_7_0_5 (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4) (not stmt_8_0_5) stmt_8_0_6 (not stmt_8_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_7_0_6 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_6 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_6 (= heap_7 heap_6)))
(assert (=> exec_7_0_6 (ite (not (= accu_7_0 #x0000)) (and (not stmt_8_0_0) stmt_8_0_1 (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4) (not stmt_8_0_5) (not stmt_8_0_6) (not stmt_8_0_7)) (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4) (not stmt_8_0_5) (not stmt_8_0_6) stmt_8_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_7_0_7 (= accu_7_0 accu_6_0)))
(assert (=> exec_7_0_7 (= mem_7_0 mem_6_0)))
(assert (=> exec_7_0_7 (= heap_7 heap_6)))
(assert (=> exec_7_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_7_1_0 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_0 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_0 (= heap_7 heap_6)))
(assert (=> exec_7_1_0 (and (not stmt_8_1_0) stmt_8_1_1 (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5) (not stmt_8_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_7_1_1 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_1 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_1 (= heap_7 heap_6)))
(assert (=> exec_7_1_1 (and (not stmt_8_1_0) (not stmt_8_1_1) stmt_8_1_2 (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5) (not stmt_8_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_7_1_2 (= accu_7_1 (select heap_6 #x0000))))
(assert (=> exec_7_1_2 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_2 (= heap_7 heap_6)))
(assert (=> exec_7_1_2 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) stmt_8_1_3 (not stmt_8_1_4) (not stmt_8_1_5) (not stmt_8_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_7_1_3 (= accu_7_1 (bvadd accu_6_1 #x0001))))
(assert (=> exec_7_1_3 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_3 (= heap_7 heap_6)))
(assert (=> exec_7_1_3 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) stmt_8_1_4 (not stmt_8_1_5) (not stmt_8_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_7_1_4 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_4 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_4 (= heap_7 (store heap_6 #x0000 accu_6_1))))
(assert (=> exec_7_1_4 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) stmt_8_1_5 (not stmt_8_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_7_1_5 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_5 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_5 (= heap_7 heap_6)))
(assert (=> exec_7_1_5 (ite (not (= accu_7_1 #x0000)) (and stmt_8_1_0 (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5) (not stmt_8_1_6)) (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5) stmt_8_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_7_1_6 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_6 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_6 (= heap_7 heap_6)))
(assert (=> exec_7_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_7_0 () Bool)
(assert (= preserve_7_0 (not thread_7_0)))

(assert (=> preserve_7_0 (= accu_7_0 accu_6_0)))
(assert (=> preserve_7_0 (= mem_7_0 mem_6_0)))

(assert (=> preserve_7_0 (= stmt_8_0_0 stmt_7_0_0)))
(assert (=> preserve_7_0 (= stmt_8_0_1 stmt_7_0_1)))
(assert (=> preserve_7_0 (= stmt_8_0_2 stmt_7_0_2)))
(assert (=> preserve_7_0 (= stmt_8_0_3 stmt_7_0_3)))
(assert (=> preserve_7_0 (= stmt_8_0_4 stmt_7_0_4)))
(assert (=> preserve_7_0 (= stmt_8_0_5 stmt_7_0_5)))
(assert (=> preserve_7_0 (= stmt_8_0_6 stmt_7_0_6)))
(assert (=> preserve_7_0 (= stmt_8_0_7 stmt_7_0_7)))

(declare-fun preserve_7_1 () Bool)
(assert (= preserve_7_1 (not thread_7_1)))

(assert (=> preserve_7_1 (= accu_7_1 accu_6_1)))
(assert (=> preserve_7_1 (= mem_7_1 mem_6_1)))

(assert (=> preserve_7_1 (= stmt_8_1_0 stmt_7_1_0)))
(assert (=> preserve_7_1 (= stmt_8_1_1 stmt_7_1_1)))
(assert (=> preserve_7_1 (= stmt_8_1_2 stmt_7_1_2)))
(assert (=> preserve_7_1 (= stmt_8_1_3 stmt_7_1_3)))
(assert (=> preserve_7_1 (= stmt_8_1_4 stmt_7_1_4)))
(assert (=> preserve_7_1 (= stmt_8_1_5 stmt_7_1_5)))
(assert (=> preserve_7_1 (= stmt_8_1_6 stmt_7_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_8 () Bool)

(assert (= exit_8 (or exit_7 exec_7_0_7 exec_7_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_8_0 () (_ BitVec 16))
(declare-fun accu_8_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_8_0 () (_ BitVec 16))
(declare-fun mem_8_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_8_0_0 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_0 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_0 (= heap_8 (store heap_7 #x0000 accu_7_0))))
(assert (=> exec_8_0_0 (and (not stmt_9_0_0) stmt_9_0_1 (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4) (not stmt_9_0_5) (not stmt_9_0_6) (not stmt_9_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_8_0_1 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_1 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_1 (= heap_8 heap_7)))
(assert (=> exec_8_0_1 (and (not stmt_9_0_0) (not stmt_9_0_1) stmt_9_0_2 (not stmt_9_0_3) (not stmt_9_0_4) (not stmt_9_0_5) (not stmt_9_0_6) (not stmt_9_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_8_0_2 (= accu_8_0 (select heap_7 #x0000))))
(assert (=> exec_8_0_2 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_2 (= heap_8 heap_7)))
(assert (=> exec_8_0_2 (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) stmt_9_0_3 (not stmt_9_0_4) (not stmt_9_0_5) (not stmt_9_0_6) (not stmt_9_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_8_0_3 (= accu_8_0 (bvadd accu_7_0 #x0001))))
(assert (=> exec_8_0_3 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_3 (= heap_8 heap_7)))
(assert (=> exec_8_0_3 (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) stmt_9_0_4 (not stmt_9_0_5) (not stmt_9_0_6) (not stmt_9_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_8_0_4 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_4 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_4 (= heap_8 (store heap_7 #x0000 accu_7_0))))
(assert (=> exec_8_0_4 (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4) stmt_9_0_5 (not stmt_9_0_6) (not stmt_9_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_8_0_5 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_5 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_5 (= heap_8 heap_7)))
(assert (=> exec_8_0_5 (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4) (not stmt_9_0_5) stmt_9_0_6 (not stmt_9_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_8_0_6 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_6 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_6 (= heap_8 heap_7)))
(assert (=> exec_8_0_6 (ite (not (= accu_8_0 #x0000)) (and (not stmt_9_0_0) stmt_9_0_1 (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4) (not stmt_9_0_5) (not stmt_9_0_6) (not stmt_9_0_7)) (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4) (not stmt_9_0_5) (not stmt_9_0_6) stmt_9_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_8_0_7 (= accu_8_0 accu_7_0)))
(assert (=> exec_8_0_7 (= mem_8_0 mem_7_0)))
(assert (=> exec_8_0_7 (= heap_8 heap_7)))
(assert (=> exec_8_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_8_1_0 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_0 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_0 (= heap_8 heap_7)))
(assert (=> exec_8_1_0 (and (not stmt_9_1_0) stmt_9_1_1 (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4) (not stmt_9_1_5) (not stmt_9_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_8_1_1 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_1 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_1 (= heap_8 heap_7)))
(assert (=> exec_8_1_1 (and (not stmt_9_1_0) (not stmt_9_1_1) stmt_9_1_2 (not stmt_9_1_3) (not stmt_9_1_4) (not stmt_9_1_5) (not stmt_9_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_8_1_2 (= accu_8_1 (select heap_7 #x0000))))
(assert (=> exec_8_1_2 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_2 (= heap_8 heap_7)))
(assert (=> exec_8_1_2 (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) stmt_9_1_3 (not stmt_9_1_4) (not stmt_9_1_5) (not stmt_9_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_8_1_3 (= accu_8_1 (bvadd accu_7_1 #x0001))))
(assert (=> exec_8_1_3 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_3 (= heap_8 heap_7)))
(assert (=> exec_8_1_3 (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) stmt_9_1_4 (not stmt_9_1_5) (not stmt_9_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_8_1_4 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_4 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_4 (= heap_8 (store heap_7 #x0000 accu_7_1))))
(assert (=> exec_8_1_4 (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4) stmt_9_1_5 (not stmt_9_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_8_1_5 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_5 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_5 (= heap_8 heap_7)))
(assert (=> exec_8_1_5 (ite (not (= accu_8_1 #x0000)) (and stmt_9_1_0 (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4) (not stmt_9_1_5) (not stmt_9_1_6)) (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4) (not stmt_9_1_5) stmt_9_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_8_1_6 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_6 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_6 (= heap_8 heap_7)))
(assert (=> exec_8_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_8_0 () Bool)
(assert (= preserve_8_0 (not thread_8_0)))

(assert (=> preserve_8_0 (= accu_8_0 accu_7_0)))
(assert (=> preserve_8_0 (= mem_8_0 mem_7_0)))

(assert (=> preserve_8_0 (= stmt_9_0_0 stmt_8_0_0)))
(assert (=> preserve_8_0 (= stmt_9_0_1 stmt_8_0_1)))
(assert (=> preserve_8_0 (= stmt_9_0_2 stmt_8_0_2)))
(assert (=> preserve_8_0 (= stmt_9_0_3 stmt_8_0_3)))
(assert (=> preserve_8_0 (= stmt_9_0_4 stmt_8_0_4)))
(assert (=> preserve_8_0 (= stmt_9_0_5 stmt_8_0_5)))
(assert (=> preserve_8_0 (= stmt_9_0_6 stmt_8_0_6)))
(assert (=> preserve_8_0 (= stmt_9_0_7 stmt_8_0_7)))

(declare-fun preserve_8_1 () Bool)
(assert (= preserve_8_1 (not thread_8_1)))

(assert (=> preserve_8_1 (= accu_8_1 accu_7_1)))
(assert (=> preserve_8_1 (= mem_8_1 mem_7_1)))

(assert (=> preserve_8_1 (= stmt_9_1_0 stmt_8_1_0)))
(assert (=> preserve_8_1 (= stmt_9_1_1 stmt_8_1_1)))
(assert (=> preserve_8_1 (= stmt_9_1_2 stmt_8_1_2)))
(assert (=> preserve_8_1 (= stmt_9_1_3 stmt_8_1_3)))
(assert (=> preserve_8_1 (= stmt_9_1_4 stmt_8_1_4)))
(assert (=> preserve_8_1 (= stmt_9_1_5 stmt_8_1_5)))
(assert (=> preserve_8_1 (= stmt_9_1_6 stmt_8_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_9 () Bool)

(assert (= exit_9 (or exit_8 exec_8_0_7 exec_8_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_9_0 () (_ BitVec 16))
(declare-fun accu_9_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_9_0 () (_ BitVec 16))
(declare-fun mem_9_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_9 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_9_0_0 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_0 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_0 (= heap_9 (store heap_8 #x0000 accu_8_0))))
(assert (=> exec_9_0_0 (and (not stmt_10_0_0) stmt_10_0_1 (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4) (not stmt_10_0_5) (not stmt_10_0_6) (not stmt_10_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_9_0_1 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_1 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_1 (= heap_9 heap_8)))
(assert (=> exec_9_0_1 (and (not stmt_10_0_0) (not stmt_10_0_1) stmt_10_0_2 (not stmt_10_0_3) (not stmt_10_0_4) (not stmt_10_0_5) (not stmt_10_0_6) (not stmt_10_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_9_0_2 (= accu_9_0 (select heap_8 #x0000))))
(assert (=> exec_9_0_2 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_2 (= heap_9 heap_8)))
(assert (=> exec_9_0_2 (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) stmt_10_0_3 (not stmt_10_0_4) (not stmt_10_0_5) (not stmt_10_0_6) (not stmt_10_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_9_0_3 (= accu_9_0 (bvadd accu_8_0 #x0001))))
(assert (=> exec_9_0_3 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_3 (= heap_9 heap_8)))
(assert (=> exec_9_0_3 (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) stmt_10_0_4 (not stmt_10_0_5) (not stmt_10_0_6) (not stmt_10_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_9_0_4 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_4 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_4 (= heap_9 (store heap_8 #x0000 accu_8_0))))
(assert (=> exec_9_0_4 (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4) stmt_10_0_5 (not stmt_10_0_6) (not stmt_10_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_9_0_5 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_5 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_5 (= heap_9 heap_8)))
(assert (=> exec_9_0_5 (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4) (not stmt_10_0_5) stmt_10_0_6 (not stmt_10_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_9_0_6 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_6 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_6 (= heap_9 heap_8)))
(assert (=> exec_9_0_6 (ite (not (= accu_9_0 #x0000)) (and (not stmt_10_0_0) stmt_10_0_1 (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4) (not stmt_10_0_5) (not stmt_10_0_6) (not stmt_10_0_7)) (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4) (not stmt_10_0_5) (not stmt_10_0_6) stmt_10_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_9_0_7 (= accu_9_0 accu_8_0)))
(assert (=> exec_9_0_7 (= mem_9_0 mem_8_0)))
(assert (=> exec_9_0_7 (= heap_9 heap_8)))
(assert (=> exec_9_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_9_1_0 (= accu_9_1 accu_8_1)))
(assert (=> exec_9_1_0 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_0 (= heap_9 heap_8)))
(assert (=> exec_9_1_0 (and (not stmt_10_1_0) stmt_10_1_1 (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4) (not stmt_10_1_5) (not stmt_10_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_9_1_1 (= accu_9_1 accu_8_1)))
(assert (=> exec_9_1_1 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_1 (= heap_9 heap_8)))
(assert (=> exec_9_1_1 (and (not stmt_10_1_0) (not stmt_10_1_1) stmt_10_1_2 (not stmt_10_1_3) (not stmt_10_1_4) (not stmt_10_1_5) (not stmt_10_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_9_1_2 (= accu_9_1 (select heap_8 #x0000))))
(assert (=> exec_9_1_2 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_2 (= heap_9 heap_8)))
(assert (=> exec_9_1_2 (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) stmt_10_1_3 (not stmt_10_1_4) (not stmt_10_1_5) (not stmt_10_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_9_1_3 (= accu_9_1 (bvadd accu_8_1 #x0001))))
(assert (=> exec_9_1_3 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_3 (= heap_9 heap_8)))
(assert (=> exec_9_1_3 (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) stmt_10_1_4 (not stmt_10_1_5) (not stmt_10_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_9_1_4 (= accu_9_1 accu_8_1)))
(assert (=> exec_9_1_4 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_4 (= heap_9 (store heap_8 #x0000 accu_8_1))))
(assert (=> exec_9_1_4 (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4) stmt_10_1_5 (not stmt_10_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_9_1_5 (= accu_9_1 accu_8_1)))
(assert (=> exec_9_1_5 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_5 (= heap_9 heap_8)))
(assert (=> exec_9_1_5 (ite (not (= accu_9_1 #x0000)) (and stmt_10_1_0 (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4) (not stmt_10_1_5) (not stmt_10_1_6)) (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4) (not stmt_10_1_5) stmt_10_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_9_1_6 (= accu_9_1 accu_8_1)))
(assert (=> exec_9_1_6 (= mem_9_1 mem_8_1)))
(assert (=> exec_9_1_6 (= heap_9 heap_8)))
(assert (=> exec_9_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_9_0 () Bool)
(assert (= preserve_9_0 (not thread_9_0)))

(assert (=> preserve_9_0 (= accu_9_0 accu_8_0)))
(assert (=> preserve_9_0 (= mem_9_0 mem_8_0)))

(assert (=> preserve_9_0 (= stmt_10_0_0 stmt_9_0_0)))
(assert (=> preserve_9_0 (= stmt_10_0_1 stmt_9_0_1)))
(assert (=> preserve_9_0 (= stmt_10_0_2 stmt_9_0_2)))
(assert (=> preserve_9_0 (= stmt_10_0_3 stmt_9_0_3)))
(assert (=> preserve_9_0 (= stmt_10_0_4 stmt_9_0_4)))
(assert (=> preserve_9_0 (= stmt_10_0_5 stmt_9_0_5)))
(assert (=> preserve_9_0 (= stmt_10_0_6 stmt_9_0_6)))
(assert (=> preserve_9_0 (= stmt_10_0_7 stmt_9_0_7)))

(declare-fun preserve_9_1 () Bool)
(assert (= preserve_9_1 (not thread_9_1)))

(assert (=> preserve_9_1 (= accu_9_1 accu_8_1)))
(assert (=> preserve_9_1 (= mem_9_1 mem_8_1)))

(assert (=> preserve_9_1 (= stmt_10_1_0 stmt_9_1_0)))
(assert (=> preserve_9_1 (= stmt_10_1_1 stmt_9_1_1)))
(assert (=> preserve_9_1 (= stmt_10_1_2 stmt_9_1_2)))
(assert (=> preserve_9_1 (= stmt_10_1_3 stmt_9_1_3)))
(assert (=> preserve_9_1 (= stmt_10_1_4 stmt_9_1_4)))
(assert (=> preserve_9_1 (= stmt_10_1_5 stmt_9_1_5)))
(assert (=> preserve_9_1 (= stmt_10_1_6 stmt_9_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 10
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_10 () Bool)

(assert (= exit_10 (or exit_9 exec_9_0_7 exec_9_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_10_0 () (_ BitVec 16))
(declare-fun accu_10_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_10_0 () (_ BitVec 16))
(declare-fun mem_10_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_10 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_10_0_0 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_0 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_0 (= heap_10 (store heap_9 #x0000 accu_9_0))))
(assert (=> exec_10_0_0 (and (not stmt_11_0_0) stmt_11_0_1 (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4) (not stmt_11_0_5) (not stmt_11_0_6) (not stmt_11_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_10_0_1 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_1 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_1 (= heap_10 heap_9)))
(assert (=> exec_10_0_1 (and (not stmt_11_0_0) (not stmt_11_0_1) stmt_11_0_2 (not stmt_11_0_3) (not stmt_11_0_4) (not stmt_11_0_5) (not stmt_11_0_6) (not stmt_11_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_10_0_2 (= accu_10_0 (select heap_9 #x0000))))
(assert (=> exec_10_0_2 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_2 (= heap_10 heap_9)))
(assert (=> exec_10_0_2 (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) stmt_11_0_3 (not stmt_11_0_4) (not stmt_11_0_5) (not stmt_11_0_6) (not stmt_11_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_10_0_3 (= accu_10_0 (bvadd accu_9_0 #x0001))))
(assert (=> exec_10_0_3 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_3 (= heap_10 heap_9)))
(assert (=> exec_10_0_3 (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) stmt_11_0_4 (not stmt_11_0_5) (not stmt_11_0_6) (not stmt_11_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_10_0_4 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_4 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_4 (= heap_10 (store heap_9 #x0000 accu_9_0))))
(assert (=> exec_10_0_4 (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4) stmt_11_0_5 (not stmt_11_0_6) (not stmt_11_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_10_0_5 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_5 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_5 (= heap_10 heap_9)))
(assert (=> exec_10_0_5 (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4) (not stmt_11_0_5) stmt_11_0_6 (not stmt_11_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_10_0_6 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_6 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_6 (= heap_10 heap_9)))
(assert (=> exec_10_0_6 (ite (not (= accu_10_0 #x0000)) (and (not stmt_11_0_0) stmt_11_0_1 (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4) (not stmt_11_0_5) (not stmt_11_0_6) (not stmt_11_0_7)) (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4) (not stmt_11_0_5) (not stmt_11_0_6) stmt_11_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_10_0_7 (= accu_10_0 accu_9_0)))
(assert (=> exec_10_0_7 (= mem_10_0 mem_9_0)))
(assert (=> exec_10_0_7 (= heap_10 heap_9)))
(assert (=> exec_10_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_10_1_0 (= accu_10_1 accu_9_1)))
(assert (=> exec_10_1_0 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_0 (= heap_10 heap_9)))
(assert (=> exec_10_1_0 (and (not stmt_11_1_0) stmt_11_1_1 (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4) (not stmt_11_1_5) (not stmt_11_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_10_1_1 (= accu_10_1 accu_9_1)))
(assert (=> exec_10_1_1 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_1 (= heap_10 heap_9)))
(assert (=> exec_10_1_1 (and (not stmt_11_1_0) (not stmt_11_1_1) stmt_11_1_2 (not stmt_11_1_3) (not stmt_11_1_4) (not stmt_11_1_5) (not stmt_11_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_10_1_2 (= accu_10_1 (select heap_9 #x0000))))
(assert (=> exec_10_1_2 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_2 (= heap_10 heap_9)))
(assert (=> exec_10_1_2 (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) stmt_11_1_3 (not stmt_11_1_4) (not stmt_11_1_5) (not stmt_11_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_10_1_3 (= accu_10_1 (bvadd accu_9_1 #x0001))))
(assert (=> exec_10_1_3 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_3 (= heap_10 heap_9)))
(assert (=> exec_10_1_3 (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) stmt_11_1_4 (not stmt_11_1_5) (not stmt_11_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_10_1_4 (= accu_10_1 accu_9_1)))
(assert (=> exec_10_1_4 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_4 (= heap_10 (store heap_9 #x0000 accu_9_1))))
(assert (=> exec_10_1_4 (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4) stmt_11_1_5 (not stmt_11_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_10_1_5 (= accu_10_1 accu_9_1)))
(assert (=> exec_10_1_5 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_5 (= heap_10 heap_9)))
(assert (=> exec_10_1_5 (ite (not (= accu_10_1 #x0000)) (and stmt_11_1_0 (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4) (not stmt_11_1_5) (not stmt_11_1_6)) (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4) (not stmt_11_1_5) stmt_11_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_10_1_6 (= accu_10_1 accu_9_1)))
(assert (=> exec_10_1_6 (= mem_10_1 mem_9_1)))
(assert (=> exec_10_1_6 (= heap_10 heap_9)))
(assert (=> exec_10_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_10_0 () Bool)
(assert (= preserve_10_0 (not thread_10_0)))

(assert (=> preserve_10_0 (= accu_10_0 accu_9_0)))
(assert (=> preserve_10_0 (= mem_10_0 mem_9_0)))

(assert (=> preserve_10_0 (= stmt_11_0_0 stmt_10_0_0)))
(assert (=> preserve_10_0 (= stmt_11_0_1 stmt_10_0_1)))
(assert (=> preserve_10_0 (= stmt_11_0_2 stmt_10_0_2)))
(assert (=> preserve_10_0 (= stmt_11_0_3 stmt_10_0_3)))
(assert (=> preserve_10_0 (= stmt_11_0_4 stmt_10_0_4)))
(assert (=> preserve_10_0 (= stmt_11_0_5 stmt_10_0_5)))
(assert (=> preserve_10_0 (= stmt_11_0_6 stmt_10_0_6)))
(assert (=> preserve_10_0 (= stmt_11_0_7 stmt_10_0_7)))

(declare-fun preserve_10_1 () Bool)
(assert (= preserve_10_1 (not thread_10_1)))

(assert (=> preserve_10_1 (= accu_10_1 accu_9_1)))
(assert (=> preserve_10_1 (= mem_10_1 mem_9_1)))

(assert (=> preserve_10_1 (= stmt_11_1_0 stmt_10_1_0)))
(assert (=> preserve_10_1 (= stmt_11_1_1 stmt_10_1_1)))
(assert (=> preserve_10_1 (= stmt_11_1_2 stmt_10_1_2)))
(assert (=> preserve_10_1 (= stmt_11_1_3 stmt_10_1_3)))
(assert (=> preserve_10_1 (= stmt_11_1_4 stmt_10_1_4)))
(assert (=> preserve_10_1 (= stmt_11_1_5 stmt_10_1_5)))
(assert (=> preserve_10_1 (= stmt_11_1_6 stmt_10_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 11
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_11 () Bool)

(assert (= exit_11 (or exit_10 exec_10_0_7 exec_10_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_11_0 () (_ BitVec 16))
(declare-fun accu_11_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_11_0 () (_ BitVec 16))
(declare-fun mem_11_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_11 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_11_0_0 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_0 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_0 (= heap_11 (store heap_10 #x0000 accu_10_0))))
(assert (=> exec_11_0_0 (and (not stmt_12_0_0) stmt_12_0_1 (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4) (not stmt_12_0_5) (not stmt_12_0_6) (not stmt_12_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_11_0_1 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_1 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_1 (= heap_11 heap_10)))
(assert (=> exec_11_0_1 (and (not stmt_12_0_0) (not stmt_12_0_1) stmt_12_0_2 (not stmt_12_0_3) (not stmt_12_0_4) (not stmt_12_0_5) (not stmt_12_0_6) (not stmt_12_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_11_0_2 (= accu_11_0 (select heap_10 #x0000))))
(assert (=> exec_11_0_2 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_2 (= heap_11 heap_10)))
(assert (=> exec_11_0_2 (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) stmt_12_0_3 (not stmt_12_0_4) (not stmt_12_0_5) (not stmt_12_0_6) (not stmt_12_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_11_0_3 (= accu_11_0 (bvadd accu_10_0 #x0001))))
(assert (=> exec_11_0_3 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_3 (= heap_11 heap_10)))
(assert (=> exec_11_0_3 (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) stmt_12_0_4 (not stmt_12_0_5) (not stmt_12_0_6) (not stmt_12_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_11_0_4 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_4 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_4 (= heap_11 (store heap_10 #x0000 accu_10_0))))
(assert (=> exec_11_0_4 (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4) stmt_12_0_5 (not stmt_12_0_6) (not stmt_12_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_11_0_5 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_5 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_5 (= heap_11 heap_10)))
(assert (=> exec_11_0_5 (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4) (not stmt_12_0_5) stmt_12_0_6 (not stmt_12_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_11_0_6 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_6 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_6 (= heap_11 heap_10)))
(assert (=> exec_11_0_6 (ite (not (= accu_11_0 #x0000)) (and (not stmt_12_0_0) stmt_12_0_1 (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4) (not stmt_12_0_5) (not stmt_12_0_6) (not stmt_12_0_7)) (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4) (not stmt_12_0_5) (not stmt_12_0_6) stmt_12_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_11_0_7 (= accu_11_0 accu_10_0)))
(assert (=> exec_11_0_7 (= mem_11_0 mem_10_0)))
(assert (=> exec_11_0_7 (= heap_11 heap_10)))
(assert (=> exec_11_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_11_1_0 (= accu_11_1 accu_10_1)))
(assert (=> exec_11_1_0 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_0 (= heap_11 heap_10)))
(assert (=> exec_11_1_0 (and (not stmt_12_1_0) stmt_12_1_1 (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4) (not stmt_12_1_5) (not stmt_12_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_11_1_1 (= accu_11_1 accu_10_1)))
(assert (=> exec_11_1_1 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_1 (= heap_11 heap_10)))
(assert (=> exec_11_1_1 (and (not stmt_12_1_0) (not stmt_12_1_1) stmt_12_1_2 (not stmt_12_1_3) (not stmt_12_1_4) (not stmt_12_1_5) (not stmt_12_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_11_1_2 (= accu_11_1 (select heap_10 #x0000))))
(assert (=> exec_11_1_2 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_2 (= heap_11 heap_10)))
(assert (=> exec_11_1_2 (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) stmt_12_1_3 (not stmt_12_1_4) (not stmt_12_1_5) (not stmt_12_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_11_1_3 (= accu_11_1 (bvadd accu_10_1 #x0001))))
(assert (=> exec_11_1_3 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_3 (= heap_11 heap_10)))
(assert (=> exec_11_1_3 (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) stmt_12_1_4 (not stmt_12_1_5) (not stmt_12_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_11_1_4 (= accu_11_1 accu_10_1)))
(assert (=> exec_11_1_4 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_4 (= heap_11 (store heap_10 #x0000 accu_10_1))))
(assert (=> exec_11_1_4 (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4) stmt_12_1_5 (not stmt_12_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_11_1_5 (= accu_11_1 accu_10_1)))
(assert (=> exec_11_1_5 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_5 (= heap_11 heap_10)))
(assert (=> exec_11_1_5 (ite (not (= accu_11_1 #x0000)) (and stmt_12_1_0 (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4) (not stmt_12_1_5) (not stmt_12_1_6)) (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4) (not stmt_12_1_5) stmt_12_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_11_1_6 (= accu_11_1 accu_10_1)))
(assert (=> exec_11_1_6 (= mem_11_1 mem_10_1)))
(assert (=> exec_11_1_6 (= heap_11 heap_10)))
(assert (=> exec_11_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_11_0 () Bool)
(assert (= preserve_11_0 (not thread_11_0)))

(assert (=> preserve_11_0 (= accu_11_0 accu_10_0)))
(assert (=> preserve_11_0 (= mem_11_0 mem_10_0)))

(assert (=> preserve_11_0 (= stmt_12_0_0 stmt_11_0_0)))
(assert (=> preserve_11_0 (= stmt_12_0_1 stmt_11_0_1)))
(assert (=> preserve_11_0 (= stmt_12_0_2 stmt_11_0_2)))
(assert (=> preserve_11_0 (= stmt_12_0_3 stmt_11_0_3)))
(assert (=> preserve_11_0 (= stmt_12_0_4 stmt_11_0_4)))
(assert (=> preserve_11_0 (= stmt_12_0_5 stmt_11_0_5)))
(assert (=> preserve_11_0 (= stmt_12_0_6 stmt_11_0_6)))
(assert (=> preserve_11_0 (= stmt_12_0_7 stmt_11_0_7)))

(declare-fun preserve_11_1 () Bool)
(assert (= preserve_11_1 (not thread_11_1)))

(assert (=> preserve_11_1 (= accu_11_1 accu_10_1)))
(assert (=> preserve_11_1 (= mem_11_1 mem_10_1)))

(assert (=> preserve_11_1 (= stmt_12_1_0 stmt_11_1_0)))
(assert (=> preserve_11_1 (= stmt_12_1_1 stmt_11_1_1)))
(assert (=> preserve_11_1 (= stmt_12_1_2 stmt_11_1_2)))
(assert (=> preserve_11_1 (= stmt_12_1_3 stmt_11_1_3)))
(assert (=> preserve_11_1 (= stmt_12_1_4 stmt_11_1_4)))
(assert (=> preserve_11_1 (= stmt_12_1_5 stmt_11_1_5)))
(assert (=> preserve_11_1 (= stmt_12_1_6 stmt_11_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_12 () Bool)

(assert (= exit_12 (or exit_11 exec_11_0_7 exec_11_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_12_0 () (_ BitVec 16))
(declare-fun accu_12_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_12_0 () (_ BitVec 16))
(declare-fun mem_12_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_12 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_12_0_0 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_0 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_0 (= heap_12 (store heap_11 #x0000 accu_11_0))))
(assert (=> exec_12_0_0 (and (not stmt_13_0_0) stmt_13_0_1 (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4) (not stmt_13_0_5) (not stmt_13_0_6) (not stmt_13_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_12_0_1 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_1 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_1 (= heap_12 heap_11)))
(assert (=> exec_12_0_1 (and (not stmt_13_0_0) (not stmt_13_0_1) stmt_13_0_2 (not stmt_13_0_3) (not stmt_13_0_4) (not stmt_13_0_5) (not stmt_13_0_6) (not stmt_13_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_12_0_2 (= accu_12_0 (select heap_11 #x0000))))
(assert (=> exec_12_0_2 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_2 (= heap_12 heap_11)))
(assert (=> exec_12_0_2 (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) stmt_13_0_3 (not stmt_13_0_4) (not stmt_13_0_5) (not stmt_13_0_6) (not stmt_13_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_12_0_3 (= accu_12_0 (bvadd accu_11_0 #x0001))))
(assert (=> exec_12_0_3 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_3 (= heap_12 heap_11)))
(assert (=> exec_12_0_3 (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) stmt_13_0_4 (not stmt_13_0_5) (not stmt_13_0_6) (not stmt_13_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_12_0_4 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_4 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_4 (= heap_12 (store heap_11 #x0000 accu_11_0))))
(assert (=> exec_12_0_4 (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4) stmt_13_0_5 (not stmt_13_0_6) (not stmt_13_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_12_0_5 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_5 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_5 (= heap_12 heap_11)))
(assert (=> exec_12_0_5 (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4) (not stmt_13_0_5) stmt_13_0_6 (not stmt_13_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_12_0_6 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_6 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_6 (= heap_12 heap_11)))
(assert (=> exec_12_0_6 (ite (not (= accu_12_0 #x0000)) (and (not stmt_13_0_0) stmt_13_0_1 (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4) (not stmt_13_0_5) (not stmt_13_0_6) (not stmt_13_0_7)) (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4) (not stmt_13_0_5) (not stmt_13_0_6) stmt_13_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_12_0_7 (= accu_12_0 accu_11_0)))
(assert (=> exec_12_0_7 (= mem_12_0 mem_11_0)))
(assert (=> exec_12_0_7 (= heap_12 heap_11)))
(assert (=> exec_12_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_12_1_0 (= accu_12_1 accu_11_1)))
(assert (=> exec_12_1_0 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_0 (= heap_12 heap_11)))
(assert (=> exec_12_1_0 (and (not stmt_13_1_0) stmt_13_1_1 (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4) (not stmt_13_1_5) (not stmt_13_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_12_1_1 (= accu_12_1 accu_11_1)))
(assert (=> exec_12_1_1 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_1 (= heap_12 heap_11)))
(assert (=> exec_12_1_1 (and (not stmt_13_1_0) (not stmt_13_1_1) stmt_13_1_2 (not stmt_13_1_3) (not stmt_13_1_4) (not stmt_13_1_5) (not stmt_13_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_12_1_2 (= accu_12_1 (select heap_11 #x0000))))
(assert (=> exec_12_1_2 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_2 (= heap_12 heap_11)))
(assert (=> exec_12_1_2 (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) stmt_13_1_3 (not stmt_13_1_4) (not stmt_13_1_5) (not stmt_13_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_12_1_3 (= accu_12_1 (bvadd accu_11_1 #x0001))))
(assert (=> exec_12_1_3 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_3 (= heap_12 heap_11)))
(assert (=> exec_12_1_3 (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) stmt_13_1_4 (not stmt_13_1_5) (not stmt_13_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_12_1_4 (= accu_12_1 accu_11_1)))
(assert (=> exec_12_1_4 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_4 (= heap_12 (store heap_11 #x0000 accu_11_1))))
(assert (=> exec_12_1_4 (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4) stmt_13_1_5 (not stmt_13_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_12_1_5 (= accu_12_1 accu_11_1)))
(assert (=> exec_12_1_5 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_5 (= heap_12 heap_11)))
(assert (=> exec_12_1_5 (ite (not (= accu_12_1 #x0000)) (and stmt_13_1_0 (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4) (not stmt_13_1_5) (not stmt_13_1_6)) (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4) (not stmt_13_1_5) stmt_13_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_12_1_6 (= accu_12_1 accu_11_1)))
(assert (=> exec_12_1_6 (= mem_12_1 mem_11_1)))
(assert (=> exec_12_1_6 (= heap_12 heap_11)))
(assert (=> exec_12_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_12_0 () Bool)
(assert (= preserve_12_0 (not thread_12_0)))

(assert (=> preserve_12_0 (= accu_12_0 accu_11_0)))
(assert (=> preserve_12_0 (= mem_12_0 mem_11_0)))

(assert (=> preserve_12_0 (= stmt_13_0_0 stmt_12_0_0)))
(assert (=> preserve_12_0 (= stmt_13_0_1 stmt_12_0_1)))
(assert (=> preserve_12_0 (= stmt_13_0_2 stmt_12_0_2)))
(assert (=> preserve_12_0 (= stmt_13_0_3 stmt_12_0_3)))
(assert (=> preserve_12_0 (= stmt_13_0_4 stmt_12_0_4)))
(assert (=> preserve_12_0 (= stmt_13_0_5 stmt_12_0_5)))
(assert (=> preserve_12_0 (= stmt_13_0_6 stmt_12_0_6)))
(assert (=> preserve_12_0 (= stmt_13_0_7 stmt_12_0_7)))

(declare-fun preserve_12_1 () Bool)
(assert (= preserve_12_1 (not thread_12_1)))

(assert (=> preserve_12_1 (= accu_12_1 accu_11_1)))
(assert (=> preserve_12_1 (= mem_12_1 mem_11_1)))

(assert (=> preserve_12_1 (= stmt_13_1_0 stmt_12_1_0)))
(assert (=> preserve_12_1 (= stmt_13_1_1 stmt_12_1_1)))
(assert (=> preserve_12_1 (= stmt_13_1_2 stmt_12_1_2)))
(assert (=> preserve_12_1 (= stmt_13_1_3 stmt_12_1_3)))
(assert (=> preserve_12_1 (= stmt_13_1_4 stmt_12_1_4)))
(assert (=> preserve_12_1 (= stmt_13_1_5 stmt_12_1_5)))
(assert (=> preserve_12_1 (= stmt_13_1_6 stmt_12_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 13
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_13 () Bool)

(assert (= exit_13 (or exit_12 exec_12_0_7 exec_12_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_13_0 () (_ BitVec 16))
(declare-fun accu_13_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_13_0 () (_ BitVec 16))
(declare-fun mem_13_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_13 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_13_0_0 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_0 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_0 (= heap_13 (store heap_12 #x0000 accu_12_0))))
(assert (=> exec_13_0_0 (and (not stmt_14_0_0) stmt_14_0_1 (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4) (not stmt_14_0_5) (not stmt_14_0_6) (not stmt_14_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_13_0_1 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_1 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_1 (= heap_13 heap_12)))
(assert (=> exec_13_0_1 (and (not stmt_14_0_0) (not stmt_14_0_1) stmt_14_0_2 (not stmt_14_0_3) (not stmt_14_0_4) (not stmt_14_0_5) (not stmt_14_0_6) (not stmt_14_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_13_0_2 (= accu_13_0 (select heap_12 #x0000))))
(assert (=> exec_13_0_2 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_2 (= heap_13 heap_12)))
(assert (=> exec_13_0_2 (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) stmt_14_0_3 (not stmt_14_0_4) (not stmt_14_0_5) (not stmt_14_0_6) (not stmt_14_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_13_0_3 (= accu_13_0 (bvadd accu_12_0 #x0001))))
(assert (=> exec_13_0_3 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_3 (= heap_13 heap_12)))
(assert (=> exec_13_0_3 (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) stmt_14_0_4 (not stmt_14_0_5) (not stmt_14_0_6) (not stmt_14_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_13_0_4 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_4 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_4 (= heap_13 (store heap_12 #x0000 accu_12_0))))
(assert (=> exec_13_0_4 (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4) stmt_14_0_5 (not stmt_14_0_6) (not stmt_14_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_13_0_5 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_5 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_5 (= heap_13 heap_12)))
(assert (=> exec_13_0_5 (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4) (not stmt_14_0_5) stmt_14_0_6 (not stmt_14_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_13_0_6 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_6 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_6 (= heap_13 heap_12)))
(assert (=> exec_13_0_6 (ite (not (= accu_13_0 #x0000)) (and (not stmt_14_0_0) stmt_14_0_1 (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4) (not stmt_14_0_5) (not stmt_14_0_6) (not stmt_14_0_7)) (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4) (not stmt_14_0_5) (not stmt_14_0_6) stmt_14_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_13_0_7 (= accu_13_0 accu_12_0)))
(assert (=> exec_13_0_7 (= mem_13_0 mem_12_0)))
(assert (=> exec_13_0_7 (= heap_13 heap_12)))
(assert (=> exec_13_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_13_1_0 (= accu_13_1 accu_12_1)))
(assert (=> exec_13_1_0 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_0 (= heap_13 heap_12)))
(assert (=> exec_13_1_0 (and (not stmt_14_1_0) stmt_14_1_1 (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4) (not stmt_14_1_5) (not stmt_14_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_13_1_1 (= accu_13_1 accu_12_1)))
(assert (=> exec_13_1_1 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_1 (= heap_13 heap_12)))
(assert (=> exec_13_1_1 (and (not stmt_14_1_0) (not stmt_14_1_1) stmt_14_1_2 (not stmt_14_1_3) (not stmt_14_1_4) (not stmt_14_1_5) (not stmt_14_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_13_1_2 (= accu_13_1 (select heap_12 #x0000))))
(assert (=> exec_13_1_2 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_2 (= heap_13 heap_12)))
(assert (=> exec_13_1_2 (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) stmt_14_1_3 (not stmt_14_1_4) (not stmt_14_1_5) (not stmt_14_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_13_1_3 (= accu_13_1 (bvadd accu_12_1 #x0001))))
(assert (=> exec_13_1_3 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_3 (= heap_13 heap_12)))
(assert (=> exec_13_1_3 (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) stmt_14_1_4 (not stmt_14_1_5) (not stmt_14_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_13_1_4 (= accu_13_1 accu_12_1)))
(assert (=> exec_13_1_4 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_4 (= heap_13 (store heap_12 #x0000 accu_12_1))))
(assert (=> exec_13_1_4 (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4) stmt_14_1_5 (not stmt_14_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_13_1_5 (= accu_13_1 accu_12_1)))
(assert (=> exec_13_1_5 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_5 (= heap_13 heap_12)))
(assert (=> exec_13_1_5 (ite (not (= accu_13_1 #x0000)) (and stmt_14_1_0 (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4) (not stmt_14_1_5) (not stmt_14_1_6)) (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4) (not stmt_14_1_5) stmt_14_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_13_1_6 (= accu_13_1 accu_12_1)))
(assert (=> exec_13_1_6 (= mem_13_1 mem_12_1)))
(assert (=> exec_13_1_6 (= heap_13 heap_12)))
(assert (=> exec_13_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_13_0 () Bool)
(assert (= preserve_13_0 (not thread_13_0)))

(assert (=> preserve_13_0 (= accu_13_0 accu_12_0)))
(assert (=> preserve_13_0 (= mem_13_0 mem_12_0)))

(assert (=> preserve_13_0 (= stmt_14_0_0 stmt_13_0_0)))
(assert (=> preserve_13_0 (= stmt_14_0_1 stmt_13_0_1)))
(assert (=> preserve_13_0 (= stmt_14_0_2 stmt_13_0_2)))
(assert (=> preserve_13_0 (= stmt_14_0_3 stmt_13_0_3)))
(assert (=> preserve_13_0 (= stmt_14_0_4 stmt_13_0_4)))
(assert (=> preserve_13_0 (= stmt_14_0_5 stmt_13_0_5)))
(assert (=> preserve_13_0 (= stmt_14_0_6 stmt_13_0_6)))
(assert (=> preserve_13_0 (= stmt_14_0_7 stmt_13_0_7)))

(declare-fun preserve_13_1 () Bool)
(assert (= preserve_13_1 (not thread_13_1)))

(assert (=> preserve_13_1 (= accu_13_1 accu_12_1)))
(assert (=> preserve_13_1 (= mem_13_1 mem_12_1)))

(assert (=> preserve_13_1 (= stmt_14_1_0 stmt_13_1_0)))
(assert (=> preserve_13_1 (= stmt_14_1_1 stmt_13_1_1)))
(assert (=> preserve_13_1 (= stmt_14_1_2 stmt_13_1_2)))
(assert (=> preserve_13_1 (= stmt_14_1_3 stmt_13_1_3)))
(assert (=> preserve_13_1 (= stmt_14_1_4 stmt_13_1_4)))
(assert (=> preserve_13_1 (= stmt_14_1_5 stmt_13_1_5)))
(assert (=> preserve_13_1 (= stmt_14_1_6 stmt_13_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 14
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_14 () Bool)

(assert (= exit_14 (or exit_13 exec_13_0_7 exec_13_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_14_0 () (_ BitVec 16))
(declare-fun accu_14_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_14_0 () (_ BitVec 16))
(declare-fun mem_14_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_14 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_14_0_0 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_0 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_0 (= heap_14 (store heap_13 #x0000 accu_13_0))))
(assert (=> exec_14_0_0 (and (not stmt_15_0_0) stmt_15_0_1 (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4) (not stmt_15_0_5) (not stmt_15_0_6) (not stmt_15_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_14_0_1 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_1 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_1 (= heap_14 heap_13)))
(assert (=> exec_14_0_1 (and (not stmt_15_0_0) (not stmt_15_0_1) stmt_15_0_2 (not stmt_15_0_3) (not stmt_15_0_4) (not stmt_15_0_5) (not stmt_15_0_6) (not stmt_15_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_14_0_2 (= accu_14_0 (select heap_13 #x0000))))
(assert (=> exec_14_0_2 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_2 (= heap_14 heap_13)))
(assert (=> exec_14_0_2 (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) stmt_15_0_3 (not stmt_15_0_4) (not stmt_15_0_5) (not stmt_15_0_6) (not stmt_15_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_14_0_3 (= accu_14_0 (bvadd accu_13_0 #x0001))))
(assert (=> exec_14_0_3 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_3 (= heap_14 heap_13)))
(assert (=> exec_14_0_3 (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) stmt_15_0_4 (not stmt_15_0_5) (not stmt_15_0_6) (not stmt_15_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_14_0_4 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_4 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_4 (= heap_14 (store heap_13 #x0000 accu_13_0))))
(assert (=> exec_14_0_4 (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4) stmt_15_0_5 (not stmt_15_0_6) (not stmt_15_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_14_0_5 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_5 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_5 (= heap_14 heap_13)))
(assert (=> exec_14_0_5 (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4) (not stmt_15_0_5) stmt_15_0_6 (not stmt_15_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_14_0_6 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_6 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_6 (= heap_14 heap_13)))
(assert (=> exec_14_0_6 (ite (not (= accu_14_0 #x0000)) (and (not stmt_15_0_0) stmt_15_0_1 (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4) (not stmt_15_0_5) (not stmt_15_0_6) (not stmt_15_0_7)) (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4) (not stmt_15_0_5) (not stmt_15_0_6) stmt_15_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_14_0_7 (= accu_14_0 accu_13_0)))
(assert (=> exec_14_0_7 (= mem_14_0 mem_13_0)))
(assert (=> exec_14_0_7 (= heap_14 heap_13)))
(assert (=> exec_14_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_14_1_0 (= accu_14_1 accu_13_1)))
(assert (=> exec_14_1_0 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_0 (= heap_14 heap_13)))
(assert (=> exec_14_1_0 (and (not stmt_15_1_0) stmt_15_1_1 (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4) (not stmt_15_1_5) (not stmt_15_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_14_1_1 (= accu_14_1 accu_13_1)))
(assert (=> exec_14_1_1 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_1 (= heap_14 heap_13)))
(assert (=> exec_14_1_1 (and (not stmt_15_1_0) (not stmt_15_1_1) stmt_15_1_2 (not stmt_15_1_3) (not stmt_15_1_4) (not stmt_15_1_5) (not stmt_15_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_14_1_2 (= accu_14_1 (select heap_13 #x0000))))
(assert (=> exec_14_1_2 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_2 (= heap_14 heap_13)))
(assert (=> exec_14_1_2 (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) stmt_15_1_3 (not stmt_15_1_4) (not stmt_15_1_5) (not stmt_15_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_14_1_3 (= accu_14_1 (bvadd accu_13_1 #x0001))))
(assert (=> exec_14_1_3 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_3 (= heap_14 heap_13)))
(assert (=> exec_14_1_3 (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) stmt_15_1_4 (not stmt_15_1_5) (not stmt_15_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_14_1_4 (= accu_14_1 accu_13_1)))
(assert (=> exec_14_1_4 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_4 (= heap_14 (store heap_13 #x0000 accu_13_1))))
(assert (=> exec_14_1_4 (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4) stmt_15_1_5 (not stmt_15_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_14_1_5 (= accu_14_1 accu_13_1)))
(assert (=> exec_14_1_5 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_5 (= heap_14 heap_13)))
(assert (=> exec_14_1_5 (ite (not (= accu_14_1 #x0000)) (and stmt_15_1_0 (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4) (not stmt_15_1_5) (not stmt_15_1_6)) (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4) (not stmt_15_1_5) stmt_15_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_14_1_6 (= accu_14_1 accu_13_1)))
(assert (=> exec_14_1_6 (= mem_14_1 mem_13_1)))
(assert (=> exec_14_1_6 (= heap_14 heap_13)))
(assert (=> exec_14_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_14_0 () Bool)
(assert (= preserve_14_0 (not thread_14_0)))

(assert (=> preserve_14_0 (= accu_14_0 accu_13_0)))
(assert (=> preserve_14_0 (= mem_14_0 mem_13_0)))

(assert (=> preserve_14_0 (= stmt_15_0_0 stmt_14_0_0)))
(assert (=> preserve_14_0 (= stmt_15_0_1 stmt_14_0_1)))
(assert (=> preserve_14_0 (= stmt_15_0_2 stmt_14_0_2)))
(assert (=> preserve_14_0 (= stmt_15_0_3 stmt_14_0_3)))
(assert (=> preserve_14_0 (= stmt_15_0_4 stmt_14_0_4)))
(assert (=> preserve_14_0 (= stmt_15_0_5 stmt_14_0_5)))
(assert (=> preserve_14_0 (= stmt_15_0_6 stmt_14_0_6)))
(assert (=> preserve_14_0 (= stmt_15_0_7 stmt_14_0_7)))

(declare-fun preserve_14_1 () Bool)
(assert (= preserve_14_1 (not thread_14_1)))

(assert (=> preserve_14_1 (= accu_14_1 accu_13_1)))
(assert (=> preserve_14_1 (= mem_14_1 mem_13_1)))

(assert (=> preserve_14_1 (= stmt_15_1_0 stmt_14_1_0)))
(assert (=> preserve_14_1 (= stmt_15_1_1 stmt_14_1_1)))
(assert (=> preserve_14_1 (= stmt_15_1_2 stmt_14_1_2)))
(assert (=> preserve_14_1 (= stmt_15_1_3 stmt_14_1_3)))
(assert (=> preserve_14_1 (= stmt_15_1_4 stmt_14_1_4)))
(assert (=> preserve_14_1 (= stmt_15_1_5 stmt_14_1_5)))
(assert (=> preserve_14_1 (= stmt_15_1_6 stmt_14_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 15
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_15 () Bool)

(assert (= exit_15 (or exit_14 exec_14_0_7 exec_14_1_6)))

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

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_15_0 () (_ BitVec 16))
(declare-fun accu_15_1 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_15_0 () (_ BitVec 16))
(declare-fun mem_15_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_15 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_15_0_0 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_0 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_0 (= heap_15 (store heap_14 #x0000 accu_14_0))))
(assert (=> exec_15_0_0 (and (not stmt_16_0_0) stmt_16_0_1 (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4) (not stmt_16_0_5) (not stmt_16_0_6) (not stmt_16_0_7))))

; thread 0@1: SYNC	0
(assert (=> exec_15_0_1 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_1 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_1 (= heap_15 heap_14)))
(assert (=> exec_15_0_1 (and (not stmt_16_0_0) (not stmt_16_0_1) stmt_16_0_2 (not stmt_16_0_3) (not stmt_16_0_4) (not stmt_16_0_5) (not stmt_16_0_6) (not stmt_16_0_7))))

; thread 0@2: LOAD	0
(assert (=> exec_15_0_2 (= accu_15_0 (select heap_14 #x0000))))
(assert (=> exec_15_0_2 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_2 (= heap_15 heap_14)))
(assert (=> exec_15_0_2 (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) stmt_16_0_3 (not stmt_16_0_4) (not stmt_16_0_5) (not stmt_16_0_6) (not stmt_16_0_7))))

; thread 0@3: ADDI	1
(assert (=> exec_15_0_3 (= accu_15_0 (bvadd accu_14_0 #x0001))))
(assert (=> exec_15_0_3 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_3 (= heap_15 heap_14)))
(assert (=> exec_15_0_3 (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) stmt_16_0_4 (not stmt_16_0_5) (not stmt_16_0_6) (not stmt_16_0_7))))

; thread 0@4: STORE	0
(assert (=> exec_15_0_4 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_4 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_4 (= heap_15 (store heap_14 #x0000 accu_14_0))))
(assert (=> exec_15_0_4 (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4) stmt_16_0_5 (not stmt_16_0_6) (not stmt_16_0_7))))

; thread 0@5: SYNC	1
(assert (=> exec_15_0_5 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_5 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_5 (= heap_15 heap_14)))
(assert (=> exec_15_0_5 (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4) (not stmt_16_0_5) stmt_16_0_6 (not stmt_16_0_7))))

; thread 0@6: JNZ	1
(assert (=> exec_15_0_6 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_6 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_6 (= heap_15 heap_14)))
(assert (=> exec_15_0_6 (ite (not (= accu_15_0 #x0000)) (and (not stmt_16_0_0) stmt_16_0_1 (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4) (not stmt_16_0_5) (not stmt_16_0_6) (not stmt_16_0_7)) (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4) (not stmt_16_0_5) (not stmt_16_0_6) stmt_16_0_7))))

; thread 0@7: EXIT	1
(assert (=> exec_15_0_7 (= accu_15_0 accu_14_0)))
(assert (=> exec_15_0_7 (= mem_15_0 mem_14_0)))
(assert (=> exec_15_0_7 (= heap_15 heap_14)))
(assert (=> exec_15_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_15_1_0 (= accu_15_1 accu_14_1)))
(assert (=> exec_15_1_0 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_0 (= heap_15 heap_14)))
(assert (=> exec_15_1_0 (and (not stmt_16_1_0) stmt_16_1_1 (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4) (not stmt_16_1_5) (not stmt_16_1_6))))

; thread 1@1: SYNC	1
(assert (=> exec_15_1_1 (= accu_15_1 accu_14_1)))
(assert (=> exec_15_1_1 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_1 (= heap_15 heap_14)))
(assert (=> exec_15_1_1 (and (not stmt_16_1_0) (not stmt_16_1_1) stmt_16_1_2 (not stmt_16_1_3) (not stmt_16_1_4) (not stmt_16_1_5) (not stmt_16_1_6))))

; thread 1@2: LOAD	0
(assert (=> exec_15_1_2 (= accu_15_1 (select heap_14 #x0000))))
(assert (=> exec_15_1_2 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_2 (= heap_15 heap_14)))
(assert (=> exec_15_1_2 (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) stmt_16_1_3 (not stmt_16_1_4) (not stmt_16_1_5) (not stmt_16_1_6))))

; thread 1@3: ADDI	1
(assert (=> exec_15_1_3 (= accu_15_1 (bvadd accu_14_1 #x0001))))
(assert (=> exec_15_1_3 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_3 (= heap_15 heap_14)))
(assert (=> exec_15_1_3 (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) stmt_16_1_4 (not stmt_16_1_5) (not stmt_16_1_6))))

; thread 1@4: STORE	0
(assert (=> exec_15_1_4 (= accu_15_1 accu_14_1)))
(assert (=> exec_15_1_4 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_4 (= heap_15 (store heap_14 #x0000 accu_14_1))))
(assert (=> exec_15_1_4 (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4) stmt_16_1_5 (not stmt_16_1_6))))

; thread 1@5: JNZ	0
(assert (=> exec_15_1_5 (= accu_15_1 accu_14_1)))
(assert (=> exec_15_1_5 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_5 (= heap_15 heap_14)))
(assert (=> exec_15_1_5 (ite (not (= accu_15_1 #x0000)) (and stmt_16_1_0 (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4) (not stmt_16_1_5) (not stmt_16_1_6)) (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4) (not stmt_16_1_5) stmt_16_1_6))))

; thread 1@6: EXIT	1
(assert (=> exec_15_1_6 (= accu_15_1 accu_14_1)))
(assert (=> exec_15_1_6 (= mem_15_1 mem_14_1)))
(assert (=> exec_15_1_6 (= heap_15 heap_14)))
(assert (=> exec_15_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_15_0 () Bool)
(assert (= preserve_15_0 (not thread_15_0)))

(assert (=> preserve_15_0 (= accu_15_0 accu_14_0)))
(assert (=> preserve_15_0 (= mem_15_0 mem_14_0)))

(assert (=> preserve_15_0 (= stmt_16_0_0 stmt_15_0_0)))
(assert (=> preserve_15_0 (= stmt_16_0_1 stmt_15_0_1)))
(assert (=> preserve_15_0 (= stmt_16_0_2 stmt_15_0_2)))
(assert (=> preserve_15_0 (= stmt_16_0_3 stmt_15_0_3)))
(assert (=> preserve_15_0 (= stmt_16_0_4 stmt_15_0_4)))
(assert (=> preserve_15_0 (= stmt_16_0_5 stmt_15_0_5)))
(assert (=> preserve_15_0 (= stmt_16_0_6 stmt_15_0_6)))
(assert (=> preserve_15_0 (= stmt_16_0_7 stmt_15_0_7)))

(declare-fun preserve_15_1 () Bool)
(assert (= preserve_15_1 (not thread_15_1)))

(assert (=> preserve_15_1 (= accu_15_1 accu_14_1)))
(assert (=> preserve_15_1 (= mem_15_1 mem_14_1)))

(assert (=> preserve_15_1 (= stmt_16_1_0 stmt_15_1_0)))
(assert (=> preserve_15_1 (= stmt_16_1_1 stmt_15_1_1)))
(assert (=> preserve_15_1 (= stmt_16_1_2 stmt_15_1_2)))
(assert (=> preserve_15_1 (= stmt_16_1_3 stmt_15_1_3)))
(assert (=> preserve_15_1 (= stmt_16_1_4 stmt_15_1_4)))
(assert (=> preserve_15_1 (= stmt_16_1_5 stmt_15_1_5)))
(assert (=> preserve_15_1 (= stmt_16_1_6 stmt_15_1_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 16
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exit flag - exit_<step>
(declare-fun exit_16 () Bool)

(assert (= exit_16 (or exit_15 exec_15_0_7 exec_15_1_6)))

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

; mem states - mem_<step>_<thread>
(declare-fun mem_16_0 () (_ BitVec 16))
(declare-fun mem_16_1 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_16 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 0@0: STORE	0
(assert (=> exec_16_0_0 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_0 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_0 (= heap_16 (store heap_15 #x0000 accu_15_0))))

; thread 0@1: SYNC	0
(assert (=> exec_16_0_1 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_1 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_1 (= heap_16 heap_15)))

; thread 0@2: LOAD	0
(assert (=> exec_16_0_2 (= accu_16_0 (select heap_15 #x0000))))
(assert (=> exec_16_0_2 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_2 (= heap_16 heap_15)))

; thread 0@3: ADDI	1
(assert (=> exec_16_0_3 (= accu_16_0 (bvadd accu_15_0 #x0001))))
(assert (=> exec_16_0_3 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_3 (= heap_16 heap_15)))

; thread 0@4: STORE	0
(assert (=> exec_16_0_4 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_4 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_4 (= heap_16 (store heap_15 #x0000 accu_15_0))))

; thread 0@5: SYNC	1
(assert (=> exec_16_0_5 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_5 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_5 (= heap_16 heap_15)))

; thread 0@6: JNZ	1
(assert (=> exec_16_0_6 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_6 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_6 (= heap_16 heap_15)))

; thread 0@7: EXIT	1
(assert (=> exec_16_0_7 (= accu_16_0 accu_15_0)))
(assert (=> exec_16_0_7 (= mem_16_0 mem_15_0)))
(assert (=> exec_16_0_7 (= heap_16 heap_15)))
(assert (=> exec_16_0_7 (= exit-code #x0001)))

; thread 1@0: SYNC	0
(assert (=> exec_16_1_0 (= accu_16_1 accu_15_1)))
(assert (=> exec_16_1_0 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_0 (= heap_16 heap_15)))

; thread 1@1: SYNC	1
(assert (=> exec_16_1_1 (= accu_16_1 accu_15_1)))
(assert (=> exec_16_1_1 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_1 (= heap_16 heap_15)))

; thread 1@2: LOAD	0
(assert (=> exec_16_1_2 (= accu_16_1 (select heap_15 #x0000))))
(assert (=> exec_16_1_2 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_2 (= heap_16 heap_15)))

; thread 1@3: ADDI	1
(assert (=> exec_16_1_3 (= accu_16_1 (bvadd accu_15_1 #x0001))))
(assert (=> exec_16_1_3 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_3 (= heap_16 heap_15)))

; thread 1@4: STORE	0
(assert (=> exec_16_1_4 (= accu_16_1 accu_15_1)))
(assert (=> exec_16_1_4 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_4 (= heap_16 (store heap_15 #x0000 accu_15_1))))

; thread 1@5: JNZ	0
(assert (=> exec_16_1_5 (= accu_16_1 accu_15_1)))
(assert (=> exec_16_1_5 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_5 (= heap_16 heap_15)))

; thread 1@6: EXIT	1
(assert (=> exec_16_1_6 (= accu_16_1 accu_15_1)))
(assert (=> exec_16_1_6 (= mem_16_1 mem_15_1)))
(assert (=> exec_16_1_6 (= heap_16 heap_15)))
(assert (=> exec_16_1_6 (= exit-code #x0001)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun preserve_16_0 () Bool)
(assert (= preserve_16_0 (not thread_16_0)))

(assert (=> preserve_16_0 (= accu_16_0 accu_15_0)))
(assert (=> preserve_16_0 (= mem_16_0 mem_15_0)))

(declare-fun preserve_16_1 () Bool)
(assert (= preserve_16_1 (not thread_16_1)))

(assert (=> preserve_16_1 (= accu_16_1 accu_15_1)))
(assert (=> preserve_16_1 (= mem_16_1 mem_15_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; exit code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not exit_16) (= exit-code #x0000)))
