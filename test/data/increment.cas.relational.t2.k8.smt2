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

; exit code
(declare-fun exit_code () (_ BitVec 16))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_1_0 () Bool)
(declare-fun stmt_1_1_1 () Bool)
(declare-fun stmt_1_1_2 () Bool)
(declare-fun stmt_1_1_3 () Bool)
(declare-fun stmt_1_1_4 () Bool)
(declare-fun stmt_1_1_5 () Bool)

(declare-fun stmt_1_2_0 () Bool)
(declare-fun stmt_1_2_1 () Bool)
(declare-fun stmt_1_2_2 () Bool)
(declare-fun stmt_1_2_3 () Bool)
(declare-fun stmt_1_2_4 () Bool)
(declare-fun stmt_1_2_5 () Bool)

; initial statement activation
(assert stmt_1_1_0)
(assert (not stmt_1_1_1))
(assert (not stmt_1_1_2))
(assert (not stmt_1_1_3))
(assert (not stmt_1_1_4))
(assert (not stmt_1_1_5))

(assert stmt_1_2_0)
(assert (not stmt_1_2_1))
(assert (not stmt_1_2_2))
(assert (not stmt_1_2_3))
(assert (not stmt_1_2_4))
(assert (not stmt_1_2_5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_1 () Bool)
(declare-fun thread_1_2 () Bool)

(assert (xor thread_1_1 thread_1_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_1_0 () Bool)

; all threads synchronized?
(assert (= sync_1_0 (and stmt_1_1_1 stmt_1_2_1 (or thread_1_1 thread_1_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_1_1_1 (not sync_1_0)) (not thread_1_1))) ; barrier 0: thread 1
(assert (=> (and stmt_1_2_1 (not sync_1_0)) (not thread_1_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_1_0 () Bool)
(declare-fun exec_1_1_1 () Bool)
(declare-fun exec_1_1_2 () Bool)
(declare-fun exec_1_1_3 () Bool)
(declare-fun exec_1_1_4 () Bool)
(declare-fun exec_1_1_5 () Bool)

(declare-fun exec_1_2_0 () Bool)
(declare-fun exec_1_2_1 () Bool)
(declare-fun exec_1_2_2 () Bool)
(declare-fun exec_1_2_3 () Bool)
(declare-fun exec_1_2_4 () Bool)
(declare-fun exec_1_2_5 () Bool)

(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))
(assert (= exec_1_1_1 (and stmt_1_1_1 sync_1_0)))
(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))
(assert (= exec_1_1_3 (and stmt_1_1_3 thread_1_1)))
(assert (= exec_1_1_4 (and stmt_1_1_4 thread_1_1)))
(assert (= exec_1_1_5 (and stmt_1_1_5 thread_1_1)))

(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))
(assert (= exec_1_2_1 (and stmt_1_2_1 sync_1_0)))
(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))
(assert (= exec_1_2_3 (and stmt_1_2_3 thread_1_2)))
(assert (= exec_1_2_4 (and stmt_1_2_4 thread_1_2)))
(assert (= exec_1_2_5 (and stmt_1_2_5 thread_1_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_1_0 () Bool)
(declare-fun stmt_2_1_1 () Bool)
(declare-fun stmt_2_1_2 () Bool)
(declare-fun stmt_2_1_3 () Bool)
(declare-fun stmt_2_1_4 () Bool)
(declare-fun stmt_2_1_5 () Bool)

(declare-fun stmt_2_2_0 () Bool)
(declare-fun stmt_2_2_1 () Bool)
(declare-fun stmt_2_2_2 () Bool)
(declare-fun stmt_2_2_3 () Bool)
(declare-fun stmt_2_2_4 () Bool)
(declare-fun stmt_2_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_1_1 () (_ BitVec 16))
(declare-fun accu_1_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_1_1 () (_ BitVec 16))
(declare-fun mem_1_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_0 (= heap_1 (store heap_0 #x0000 accu_0_1))))
(assert (=> exec_1_1_0 (and (not stmt_2_1_0) stmt_2_1_1 (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_1_1_1 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_1 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_1 (= heap_1 heap_0)))
(assert (=> exec_1_1_1 (and (not stmt_2_1_0) (not stmt_2_1_1) stmt_2_1_2 (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_1_1_2 (= accu_1_1 (select heap_0 #x0000))))
(assert (=> exec_1_1_2 (= mem_1_1 accu_1_1)))
(assert (=> exec_1_1_2 (= heap_1 heap_0)))
(assert (=> exec_1_1_2 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) stmt_2_1_3 (not stmt_2_1_4) (not stmt_2_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_1_1_3 (= accu_1_1 (bvadd accu_0_1 #x0001))))
(assert (=> exec_1_1_3 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_3 (= heap_1 heap_0)))
(assert (=> exec_1_1_3 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) stmt_2_1_4 (not stmt_2_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_1_1_4 (= accu_1_1 (ite (= mem_0_1 (select heap_0 #x0000)) #x0001 #x0000))))
(assert (=> exec_1_1_4 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_4 (= heap_1 (ite (= mem_0_1 (select heap_0 #x0000)) (store heap_0 #x0000 accu_0_1) heap_0))))
(assert (=> exec_1_1_4 (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4) stmt_2_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_1_1_5 (= accu_1_1 accu_0_1)))
(assert (=> exec_1_1_5 (= mem_1_1 mem_0_1)))
(assert (=> exec_1_1_5 (= heap_1 heap_0)))
(assert (=> exec_1_1_5 (and (not stmt_2_1_0) (not stmt_2_1_1) stmt_2_1_2 (not stmt_2_1_3) (not stmt_2_1_4) (not stmt_2_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_1_2_0 (= accu_1_2 accu_0_2)))
(assert (=> exec_1_2_0 (= mem_1_2 mem_0_2)))
(assert (=> exec_1_2_0 (= heap_1 (store heap_0 #x0000 accu_0_2))))
(assert (=> exec_1_2_0 (and (not stmt_2_2_0) stmt_2_2_1 (not stmt_2_2_2) (not stmt_2_2_3) (not stmt_2_2_4) (not stmt_2_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_1_2_1 (= accu_1_2 accu_0_2)))
(assert (=> exec_1_2_1 (= mem_1_2 mem_0_2)))
(assert (=> exec_1_2_1 (= heap_1 heap_0)))
(assert (=> exec_1_2_1 (and (not stmt_2_2_0) (not stmt_2_2_1) stmt_2_2_2 (not stmt_2_2_3) (not stmt_2_2_4) (not stmt_2_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_1_2_2 (= accu_1_2 (select heap_0 #x0000))))
(assert (=> exec_1_2_2 (= mem_1_2 accu_1_2)))
(assert (=> exec_1_2_2 (= heap_1 heap_0)))
(assert (=> exec_1_2_2 (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) stmt_2_2_3 (not stmt_2_2_4) (not stmt_2_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_1_2_3 (= accu_1_2 (bvadd accu_0_2 #x0001))))
(assert (=> exec_1_2_3 (= mem_1_2 mem_0_2)))
(assert (=> exec_1_2_3 (= heap_1 heap_0)))
(assert (=> exec_1_2_3 (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) (not stmt_2_2_3) stmt_2_2_4 (not stmt_2_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_1_2_4 (= accu_1_2 (ite (= mem_0_2 (select heap_0 #x0000)) #x0001 #x0000))))
(assert (=> exec_1_2_4 (= mem_1_2 mem_0_2)))
(assert (=> exec_1_2_4 (= heap_1 (ite (= mem_0_2 (select heap_0 #x0000)) (store heap_0 #x0000 accu_0_2) heap_0))))
(assert (=> exec_1_2_4 (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) (not stmt_2_2_3) (not stmt_2_2_4) stmt_2_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_1_2_5 (= accu_1_2 accu_0_2)))
(assert (=> exec_1_2_5 (= mem_1_2 mem_0_2)))
(assert (=> exec_1_2_5 (= heap_1 heap_0)))
(assert (=> exec_1_2_5 (and (not stmt_2_2_0) (not stmt_2_2_1) stmt_2_2_2 (not stmt_2_2_3) (not stmt_2_2_4) (not stmt_2_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_1_1 sync_1_0)) (= accu_1_1 accu_0_1)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= mem_1_1 mem_0_1)))

(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_0 stmt_1_1_0)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_1 stmt_1_1_1)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_2 stmt_1_1_2)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_3 stmt_1_1_3)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_4 stmt_1_1_4)))
(assert (=> (not (or thread_1_1 sync_1_0)) (= stmt_2_1_5 stmt_1_1_5)))

(assert (=> (not (or thread_1_2 sync_1_0)) (= accu_1_2 accu_0_2)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= mem_1_2 mem_0_2)))

(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_0 stmt_1_2_0)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_1 stmt_1_2_1)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_2 stmt_1_2_2)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_3 stmt_1_2_3)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_4 stmt_1_2_4)))
(assert (=> (not (or thread_1_2 sync_1_0)) (= stmt_2_2_5 stmt_1_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_1 () Bool)
(declare-fun thread_2_2 () Bool)

(assert (xor thread_2_1 thread_2_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_2_0 () Bool)

; all threads synchronized?
(assert (= sync_2_0 (and stmt_2_1_1 stmt_2_2_1 (or thread_2_1 thread_2_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_2_1_1 (not sync_2_0)) (not thread_2_1))) ; barrier 0: thread 1
(assert (=> (and stmt_2_2_1 (not sync_2_0)) (not thread_2_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_1_0 () Bool)
(declare-fun exec_2_1_1 () Bool)
(declare-fun exec_2_1_2 () Bool)
(declare-fun exec_2_1_3 () Bool)
(declare-fun exec_2_1_4 () Bool)
(declare-fun exec_2_1_5 () Bool)

(declare-fun exec_2_2_0 () Bool)
(declare-fun exec_2_2_1 () Bool)
(declare-fun exec_2_2_2 () Bool)
(declare-fun exec_2_2_3 () Bool)
(declare-fun exec_2_2_4 () Bool)
(declare-fun exec_2_2_5 () Bool)

(assert (= exec_2_1_0 (and stmt_2_1_0 thread_2_1)))
(assert (= exec_2_1_1 (and stmt_2_1_1 sync_2_0)))
(assert (= exec_2_1_2 (and stmt_2_1_2 thread_2_1)))
(assert (= exec_2_1_3 (and stmt_2_1_3 thread_2_1)))
(assert (= exec_2_1_4 (and stmt_2_1_4 thread_2_1)))
(assert (= exec_2_1_5 (and stmt_2_1_5 thread_2_1)))

(assert (= exec_2_2_0 (and stmt_2_2_0 thread_2_2)))
(assert (= exec_2_2_1 (and stmt_2_2_1 sync_2_0)))
(assert (= exec_2_2_2 (and stmt_2_2_2 thread_2_2)))
(assert (= exec_2_2_3 (and stmt_2_2_3 thread_2_2)))
(assert (= exec_2_2_4 (and stmt_2_2_4 thread_2_2)))
(assert (= exec_2_2_5 (and stmt_2_2_5 thread_2_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_1_0 () Bool)
(declare-fun stmt_3_1_1 () Bool)
(declare-fun stmt_3_1_2 () Bool)
(declare-fun stmt_3_1_3 () Bool)
(declare-fun stmt_3_1_4 () Bool)
(declare-fun stmt_3_1_5 () Bool)

(declare-fun stmt_3_2_0 () Bool)
(declare-fun stmt_3_2_1 () Bool)
(declare-fun stmt_3_2_2 () Bool)
(declare-fun stmt_3_2_3 () Bool)
(declare-fun stmt_3_2_4 () Bool)
(declare-fun stmt_3_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_2_1 () (_ BitVec 16))
(declare-fun accu_2_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_2_1 () (_ BitVec 16))
(declare-fun mem_2_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_2_1_0 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_0 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_0 (= heap_2 (store heap_1 #x0000 accu_1_1))))
(assert (=> exec_2_1_0 (and (not stmt_3_1_0) stmt_3_1_1 (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_2_1_1 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_1 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_1 (= heap_2 heap_1)))
(assert (=> exec_2_1_1 (and (not stmt_3_1_0) (not stmt_3_1_1) stmt_3_1_2 (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_2_1_2 (= accu_2_1 (select heap_1 #x0000))))
(assert (=> exec_2_1_2 (= mem_2_1 accu_2_1)))
(assert (=> exec_2_1_2 (= heap_2 heap_1)))
(assert (=> exec_2_1_2 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) stmt_3_1_3 (not stmt_3_1_4) (not stmt_3_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_2_1_3 (= accu_2_1 (bvadd accu_1_1 #x0001))))
(assert (=> exec_2_1_3 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_3 (= heap_2 heap_1)))
(assert (=> exec_2_1_3 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) stmt_3_1_4 (not stmt_3_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_2_1_4 (= accu_2_1 (ite (= mem_1_1 (select heap_1 #x0000)) #x0001 #x0000))))
(assert (=> exec_2_1_4 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_4 (= heap_2 (ite (= mem_1_1 (select heap_1 #x0000)) (store heap_1 #x0000 accu_1_1) heap_1))))
(assert (=> exec_2_1_4 (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4) stmt_3_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_2_1_5 (= accu_2_1 accu_1_1)))
(assert (=> exec_2_1_5 (= mem_2_1 mem_1_1)))
(assert (=> exec_2_1_5 (= heap_2 heap_1)))
(assert (=> exec_2_1_5 (and (not stmt_3_1_0) (not stmt_3_1_1) stmt_3_1_2 (not stmt_3_1_3) (not stmt_3_1_4) (not stmt_3_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_2_2_0 (= accu_2_2 accu_1_2)))
(assert (=> exec_2_2_0 (= mem_2_2 mem_1_2)))
(assert (=> exec_2_2_0 (= heap_2 (store heap_1 #x0000 accu_1_2))))
(assert (=> exec_2_2_0 (and (not stmt_3_2_0) stmt_3_2_1 (not stmt_3_2_2) (not stmt_3_2_3) (not stmt_3_2_4) (not stmt_3_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_2_2_1 (= accu_2_2 accu_1_2)))
(assert (=> exec_2_2_1 (= mem_2_2 mem_1_2)))
(assert (=> exec_2_2_1 (= heap_2 heap_1)))
(assert (=> exec_2_2_1 (and (not stmt_3_2_0) (not stmt_3_2_1) stmt_3_2_2 (not stmt_3_2_3) (not stmt_3_2_4) (not stmt_3_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_2_2_2 (= accu_2_2 (select heap_1 #x0000))))
(assert (=> exec_2_2_2 (= mem_2_2 accu_2_2)))
(assert (=> exec_2_2_2 (= heap_2 heap_1)))
(assert (=> exec_2_2_2 (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) stmt_3_2_3 (not stmt_3_2_4) (not stmt_3_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_2_2_3 (= accu_2_2 (bvadd accu_1_2 #x0001))))
(assert (=> exec_2_2_3 (= mem_2_2 mem_1_2)))
(assert (=> exec_2_2_3 (= heap_2 heap_1)))
(assert (=> exec_2_2_3 (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) (not stmt_3_2_3) stmt_3_2_4 (not stmt_3_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_2_2_4 (= accu_2_2 (ite (= mem_1_2 (select heap_1 #x0000)) #x0001 #x0000))))
(assert (=> exec_2_2_4 (= mem_2_2 mem_1_2)))
(assert (=> exec_2_2_4 (= heap_2 (ite (= mem_1_2 (select heap_1 #x0000)) (store heap_1 #x0000 accu_1_2) heap_1))))
(assert (=> exec_2_2_4 (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) (not stmt_3_2_3) (not stmt_3_2_4) stmt_3_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_2_2_5 (= accu_2_2 accu_1_2)))
(assert (=> exec_2_2_5 (= mem_2_2 mem_1_2)))
(assert (=> exec_2_2_5 (= heap_2 heap_1)))
(assert (=> exec_2_2_5 (and (not stmt_3_2_0) (not stmt_3_2_1) stmt_3_2_2 (not stmt_3_2_3) (not stmt_3_2_4) (not stmt_3_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_2_1 sync_2_0)) (= accu_2_1 accu_1_1)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= mem_2_1 mem_1_1)))

(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_0 stmt_2_1_0)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_1 stmt_2_1_1)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_2 stmt_2_1_2)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_3 stmt_2_1_3)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_4 stmt_2_1_4)))
(assert (=> (not (or thread_2_1 sync_2_0)) (= stmt_3_1_5 stmt_2_1_5)))

(assert (=> (not (or thread_2_2 sync_2_0)) (= accu_2_2 accu_1_2)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= mem_2_2 mem_1_2)))

(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_0 stmt_2_2_0)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_1 stmt_2_2_1)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_2 stmt_2_2_2)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_3 stmt_2_2_3)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_4 stmt_2_2_4)))
(assert (=> (not (or thread_2_2 sync_2_0)) (= stmt_3_2_5 stmt_2_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_1 () Bool)
(declare-fun thread_3_2 () Bool)

(assert (xor thread_3_1 thread_3_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_3_0 () Bool)

; all threads synchronized?
(assert (= sync_3_0 (and stmt_3_1_1 stmt_3_2_1 (or thread_3_1 thread_3_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_3_1_1 (not sync_3_0)) (not thread_3_1))) ; barrier 0: thread 1
(assert (=> (and stmt_3_2_1 (not sync_3_0)) (not thread_3_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_1_0 () Bool)
(declare-fun exec_3_1_1 () Bool)
(declare-fun exec_3_1_2 () Bool)
(declare-fun exec_3_1_3 () Bool)
(declare-fun exec_3_1_4 () Bool)
(declare-fun exec_3_1_5 () Bool)

(declare-fun exec_3_2_0 () Bool)
(declare-fun exec_3_2_1 () Bool)
(declare-fun exec_3_2_2 () Bool)
(declare-fun exec_3_2_3 () Bool)
(declare-fun exec_3_2_4 () Bool)
(declare-fun exec_3_2_5 () Bool)

(assert (= exec_3_1_0 (and stmt_3_1_0 thread_3_1)))
(assert (= exec_3_1_1 (and stmt_3_1_1 sync_3_0)))
(assert (= exec_3_1_2 (and stmt_3_1_2 thread_3_1)))
(assert (= exec_3_1_3 (and stmt_3_1_3 thread_3_1)))
(assert (= exec_3_1_4 (and stmt_3_1_4 thread_3_1)))
(assert (= exec_3_1_5 (and stmt_3_1_5 thread_3_1)))

(assert (= exec_3_2_0 (and stmt_3_2_0 thread_3_2)))
(assert (= exec_3_2_1 (and stmt_3_2_1 sync_3_0)))
(assert (= exec_3_2_2 (and stmt_3_2_2 thread_3_2)))
(assert (= exec_3_2_3 (and stmt_3_2_3 thread_3_2)))
(assert (= exec_3_2_4 (and stmt_3_2_4 thread_3_2)))
(assert (= exec_3_2_5 (and stmt_3_2_5 thread_3_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_1_0 () Bool)
(declare-fun stmt_4_1_1 () Bool)
(declare-fun stmt_4_1_2 () Bool)
(declare-fun stmt_4_1_3 () Bool)
(declare-fun stmt_4_1_4 () Bool)
(declare-fun stmt_4_1_5 () Bool)

(declare-fun stmt_4_2_0 () Bool)
(declare-fun stmt_4_2_1 () Bool)
(declare-fun stmt_4_2_2 () Bool)
(declare-fun stmt_4_2_3 () Bool)
(declare-fun stmt_4_2_4 () Bool)
(declare-fun stmt_4_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_3_1 () (_ BitVec 16))
(declare-fun accu_3_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_3_1 () (_ BitVec 16))
(declare-fun mem_3_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_3_1_0 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_0 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_0 (= heap_3 (store heap_2 #x0000 accu_2_1))))
(assert (=> exec_3_1_0 (and (not stmt_4_1_0) stmt_4_1_1 (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_3_1_1 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_1 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_1 (= heap_3 heap_2)))
(assert (=> exec_3_1_1 (and (not stmt_4_1_0) (not stmt_4_1_1) stmt_4_1_2 (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_3_1_2 (= accu_3_1 (select heap_2 #x0000))))
(assert (=> exec_3_1_2 (= mem_3_1 accu_3_1)))
(assert (=> exec_3_1_2 (= heap_3 heap_2)))
(assert (=> exec_3_1_2 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) stmt_4_1_3 (not stmt_4_1_4) (not stmt_4_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_3_1_3 (= accu_3_1 (bvadd accu_2_1 #x0001))))
(assert (=> exec_3_1_3 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_3 (= heap_3 heap_2)))
(assert (=> exec_3_1_3 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) stmt_4_1_4 (not stmt_4_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_3_1_4 (= accu_3_1 (ite (= mem_2_1 (select heap_2 #x0000)) #x0001 #x0000))))
(assert (=> exec_3_1_4 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_4 (= heap_3 (ite (= mem_2_1 (select heap_2 #x0000)) (store heap_2 #x0000 accu_2_1) heap_2))))
(assert (=> exec_3_1_4 (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4) stmt_4_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_3_1_5 (= accu_3_1 accu_2_1)))
(assert (=> exec_3_1_5 (= mem_3_1 mem_2_1)))
(assert (=> exec_3_1_5 (= heap_3 heap_2)))
(assert (=> exec_3_1_5 (and (not stmt_4_1_0) (not stmt_4_1_1) stmt_4_1_2 (not stmt_4_1_3) (not stmt_4_1_4) (not stmt_4_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_3_2_0 (= accu_3_2 accu_2_2)))
(assert (=> exec_3_2_0 (= mem_3_2 mem_2_2)))
(assert (=> exec_3_2_0 (= heap_3 (store heap_2 #x0000 accu_2_2))))
(assert (=> exec_3_2_0 (and (not stmt_4_2_0) stmt_4_2_1 (not stmt_4_2_2) (not stmt_4_2_3) (not stmt_4_2_4) (not stmt_4_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_3_2_1 (= accu_3_2 accu_2_2)))
(assert (=> exec_3_2_1 (= mem_3_2 mem_2_2)))
(assert (=> exec_3_2_1 (= heap_3 heap_2)))
(assert (=> exec_3_2_1 (and (not stmt_4_2_0) (not stmt_4_2_1) stmt_4_2_2 (not stmt_4_2_3) (not stmt_4_2_4) (not stmt_4_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_3_2_2 (= accu_3_2 (select heap_2 #x0000))))
(assert (=> exec_3_2_2 (= mem_3_2 accu_3_2)))
(assert (=> exec_3_2_2 (= heap_3 heap_2)))
(assert (=> exec_3_2_2 (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) stmt_4_2_3 (not stmt_4_2_4) (not stmt_4_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_3_2_3 (= accu_3_2 (bvadd accu_2_2 #x0001))))
(assert (=> exec_3_2_3 (= mem_3_2 mem_2_2)))
(assert (=> exec_3_2_3 (= heap_3 heap_2)))
(assert (=> exec_3_2_3 (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) (not stmt_4_2_3) stmt_4_2_4 (not stmt_4_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_3_2_4 (= accu_3_2 (ite (= mem_2_2 (select heap_2 #x0000)) #x0001 #x0000))))
(assert (=> exec_3_2_4 (= mem_3_2 mem_2_2)))
(assert (=> exec_3_2_4 (= heap_3 (ite (= mem_2_2 (select heap_2 #x0000)) (store heap_2 #x0000 accu_2_2) heap_2))))
(assert (=> exec_3_2_4 (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) (not stmt_4_2_3) (not stmt_4_2_4) stmt_4_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_3_2_5 (= accu_3_2 accu_2_2)))
(assert (=> exec_3_2_5 (= mem_3_2 mem_2_2)))
(assert (=> exec_3_2_5 (= heap_3 heap_2)))
(assert (=> exec_3_2_5 (and (not stmt_4_2_0) (not stmt_4_2_1) stmt_4_2_2 (not stmt_4_2_3) (not stmt_4_2_4) (not stmt_4_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_3_1 sync_3_0)) (= accu_3_1 accu_2_1)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= mem_3_1 mem_2_1)))

(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_0 stmt_3_1_0)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_1 stmt_3_1_1)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_2 stmt_3_1_2)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_3 stmt_3_1_3)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_4 stmt_3_1_4)))
(assert (=> (not (or thread_3_1 sync_3_0)) (= stmt_4_1_5 stmt_3_1_5)))

(assert (=> (not (or thread_3_2 sync_3_0)) (= accu_3_2 accu_2_2)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= mem_3_2 mem_2_2)))

(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_0 stmt_3_2_0)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_1 stmt_3_2_1)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_2 stmt_3_2_2)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_3 stmt_3_2_3)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_4 stmt_3_2_4)))
(assert (=> (not (or thread_3_2 sync_3_0)) (= stmt_4_2_5 stmt_3_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_1 () Bool)
(declare-fun thread_4_2 () Bool)

(assert (xor thread_4_1 thread_4_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_4_0 () Bool)

; all threads synchronized?
(assert (= sync_4_0 (and stmt_4_1_1 stmt_4_2_1 (or thread_4_1 thread_4_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_4_1_1 (not sync_4_0)) (not thread_4_1))) ; barrier 0: thread 1
(assert (=> (and stmt_4_2_1 (not sync_4_0)) (not thread_4_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_1_0 () Bool)
(declare-fun exec_4_1_1 () Bool)
(declare-fun exec_4_1_2 () Bool)
(declare-fun exec_4_1_3 () Bool)
(declare-fun exec_4_1_4 () Bool)
(declare-fun exec_4_1_5 () Bool)

(declare-fun exec_4_2_0 () Bool)
(declare-fun exec_4_2_1 () Bool)
(declare-fun exec_4_2_2 () Bool)
(declare-fun exec_4_2_3 () Bool)
(declare-fun exec_4_2_4 () Bool)
(declare-fun exec_4_2_5 () Bool)

(assert (= exec_4_1_0 (and stmt_4_1_0 thread_4_1)))
(assert (= exec_4_1_1 (and stmt_4_1_1 sync_4_0)))
(assert (= exec_4_1_2 (and stmt_4_1_2 thread_4_1)))
(assert (= exec_4_1_3 (and stmt_4_1_3 thread_4_1)))
(assert (= exec_4_1_4 (and stmt_4_1_4 thread_4_1)))
(assert (= exec_4_1_5 (and stmt_4_1_5 thread_4_1)))

(assert (= exec_4_2_0 (and stmt_4_2_0 thread_4_2)))
(assert (= exec_4_2_1 (and stmt_4_2_1 sync_4_0)))
(assert (= exec_4_2_2 (and stmt_4_2_2 thread_4_2)))
(assert (= exec_4_2_3 (and stmt_4_2_3 thread_4_2)))
(assert (= exec_4_2_4 (and stmt_4_2_4 thread_4_2)))
(assert (= exec_4_2_5 (and stmt_4_2_5 thread_4_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_1_0 () Bool)
(declare-fun stmt_5_1_1 () Bool)
(declare-fun stmt_5_1_2 () Bool)
(declare-fun stmt_5_1_3 () Bool)
(declare-fun stmt_5_1_4 () Bool)
(declare-fun stmt_5_1_5 () Bool)

(declare-fun stmt_5_2_0 () Bool)
(declare-fun stmt_5_2_1 () Bool)
(declare-fun stmt_5_2_2 () Bool)
(declare-fun stmt_5_2_3 () Bool)
(declare-fun stmt_5_2_4 () Bool)
(declare-fun stmt_5_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_4_1 () (_ BitVec 16))
(declare-fun accu_4_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_4_1 () (_ BitVec 16))
(declare-fun mem_4_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_4_1_0 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_0 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_0 (= heap_4 (store heap_3 #x0000 accu_3_1))))
(assert (=> exec_4_1_0 (and (not stmt_5_1_0) stmt_5_1_1 (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_4_1_1 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_1 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_1 (= heap_4 heap_3)))
(assert (=> exec_4_1_1 (and (not stmt_5_1_0) (not stmt_5_1_1) stmt_5_1_2 (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_4_1_2 (= accu_4_1 (select heap_3 #x0000))))
(assert (=> exec_4_1_2 (= mem_4_1 accu_4_1)))
(assert (=> exec_4_1_2 (= heap_4 heap_3)))
(assert (=> exec_4_1_2 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) stmt_5_1_3 (not stmt_5_1_4) (not stmt_5_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_4_1_3 (= accu_4_1 (bvadd accu_3_1 #x0001))))
(assert (=> exec_4_1_3 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_3 (= heap_4 heap_3)))
(assert (=> exec_4_1_3 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) stmt_5_1_4 (not stmt_5_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_4_1_4 (= accu_4_1 (ite (= mem_3_1 (select heap_3 #x0000)) #x0001 #x0000))))
(assert (=> exec_4_1_4 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_4 (= heap_4 (ite (= mem_3_1 (select heap_3 #x0000)) (store heap_3 #x0000 accu_3_1) heap_3))))
(assert (=> exec_4_1_4 (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4) stmt_5_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_4_1_5 (= accu_4_1 accu_3_1)))
(assert (=> exec_4_1_5 (= mem_4_1 mem_3_1)))
(assert (=> exec_4_1_5 (= heap_4 heap_3)))
(assert (=> exec_4_1_5 (and (not stmt_5_1_0) (not stmt_5_1_1) stmt_5_1_2 (not stmt_5_1_3) (not stmt_5_1_4) (not stmt_5_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_4_2_0 (= accu_4_2 accu_3_2)))
(assert (=> exec_4_2_0 (= mem_4_2 mem_3_2)))
(assert (=> exec_4_2_0 (= heap_4 (store heap_3 #x0000 accu_3_2))))
(assert (=> exec_4_2_0 (and (not stmt_5_2_0) stmt_5_2_1 (not stmt_5_2_2) (not stmt_5_2_3) (not stmt_5_2_4) (not stmt_5_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_4_2_1 (= accu_4_2 accu_3_2)))
(assert (=> exec_4_2_1 (= mem_4_2 mem_3_2)))
(assert (=> exec_4_2_1 (= heap_4 heap_3)))
(assert (=> exec_4_2_1 (and (not stmt_5_2_0) (not stmt_5_2_1) stmt_5_2_2 (not stmt_5_2_3) (not stmt_5_2_4) (not stmt_5_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_4_2_2 (= accu_4_2 (select heap_3 #x0000))))
(assert (=> exec_4_2_2 (= mem_4_2 accu_4_2)))
(assert (=> exec_4_2_2 (= heap_4 heap_3)))
(assert (=> exec_4_2_2 (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) stmt_5_2_3 (not stmt_5_2_4) (not stmt_5_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_4_2_3 (= accu_4_2 (bvadd accu_3_2 #x0001))))
(assert (=> exec_4_2_3 (= mem_4_2 mem_3_2)))
(assert (=> exec_4_2_3 (= heap_4 heap_3)))
(assert (=> exec_4_2_3 (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) (not stmt_5_2_3) stmt_5_2_4 (not stmt_5_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_4_2_4 (= accu_4_2 (ite (= mem_3_2 (select heap_3 #x0000)) #x0001 #x0000))))
(assert (=> exec_4_2_4 (= mem_4_2 mem_3_2)))
(assert (=> exec_4_2_4 (= heap_4 (ite (= mem_3_2 (select heap_3 #x0000)) (store heap_3 #x0000 accu_3_2) heap_3))))
(assert (=> exec_4_2_4 (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) (not stmt_5_2_3) (not stmt_5_2_4) stmt_5_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_4_2_5 (= accu_4_2 accu_3_2)))
(assert (=> exec_4_2_5 (= mem_4_2 mem_3_2)))
(assert (=> exec_4_2_5 (= heap_4 heap_3)))
(assert (=> exec_4_2_5 (and (not stmt_5_2_0) (not stmt_5_2_1) stmt_5_2_2 (not stmt_5_2_3) (not stmt_5_2_4) (not stmt_5_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_4_1 sync_4_0)) (= accu_4_1 accu_3_1)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= mem_4_1 mem_3_1)))

(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_0 stmt_4_1_0)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_1 stmt_4_1_1)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_2 stmt_4_1_2)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_3 stmt_4_1_3)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_4 stmt_4_1_4)))
(assert (=> (not (or thread_4_1 sync_4_0)) (= stmt_5_1_5 stmt_4_1_5)))

(assert (=> (not (or thread_4_2 sync_4_0)) (= accu_4_2 accu_3_2)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= mem_4_2 mem_3_2)))

(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_0 stmt_4_2_0)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_1 stmt_4_2_1)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_2 stmt_4_2_2)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_3 stmt_4_2_3)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_4 stmt_4_2_4)))
(assert (=> (not (or thread_4_2 sync_4_0)) (= stmt_5_2_5 stmt_4_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_1 () Bool)
(declare-fun thread_5_2 () Bool)

(assert (xor thread_5_1 thread_5_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_5_0 () Bool)

; all threads synchronized?
(assert (= sync_5_0 (and stmt_5_1_1 stmt_5_2_1 (or thread_5_1 thread_5_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_5_1_1 (not sync_5_0)) (not thread_5_1))) ; barrier 0: thread 1
(assert (=> (and stmt_5_2_1 (not sync_5_0)) (not thread_5_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_1_0 () Bool)
(declare-fun exec_5_1_1 () Bool)
(declare-fun exec_5_1_2 () Bool)
(declare-fun exec_5_1_3 () Bool)
(declare-fun exec_5_1_4 () Bool)
(declare-fun exec_5_1_5 () Bool)

(declare-fun exec_5_2_0 () Bool)
(declare-fun exec_5_2_1 () Bool)
(declare-fun exec_5_2_2 () Bool)
(declare-fun exec_5_2_3 () Bool)
(declare-fun exec_5_2_4 () Bool)
(declare-fun exec_5_2_5 () Bool)

(assert (= exec_5_1_0 (and stmt_5_1_0 thread_5_1)))
(assert (= exec_5_1_1 (and stmt_5_1_1 sync_5_0)))
(assert (= exec_5_1_2 (and stmt_5_1_2 thread_5_1)))
(assert (= exec_5_1_3 (and stmt_5_1_3 thread_5_1)))
(assert (= exec_5_1_4 (and stmt_5_1_4 thread_5_1)))
(assert (= exec_5_1_5 (and stmt_5_1_5 thread_5_1)))

(assert (= exec_5_2_0 (and stmt_5_2_0 thread_5_2)))
(assert (= exec_5_2_1 (and stmt_5_2_1 sync_5_0)))
(assert (= exec_5_2_2 (and stmt_5_2_2 thread_5_2)))
(assert (= exec_5_2_3 (and stmt_5_2_3 thread_5_2)))
(assert (= exec_5_2_4 (and stmt_5_2_4 thread_5_2)))
(assert (= exec_5_2_5 (and stmt_5_2_5 thread_5_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_1_0 () Bool)
(declare-fun stmt_6_1_1 () Bool)
(declare-fun stmt_6_1_2 () Bool)
(declare-fun stmt_6_1_3 () Bool)
(declare-fun stmt_6_1_4 () Bool)
(declare-fun stmt_6_1_5 () Bool)

(declare-fun stmt_6_2_0 () Bool)
(declare-fun stmt_6_2_1 () Bool)
(declare-fun stmt_6_2_2 () Bool)
(declare-fun stmt_6_2_3 () Bool)
(declare-fun stmt_6_2_4 () Bool)
(declare-fun stmt_6_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_5_1 () (_ BitVec 16))
(declare-fun accu_5_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_5_1 () (_ BitVec 16))
(declare-fun mem_5_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_5_1_0 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_0 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_0 (= heap_5 (store heap_4 #x0000 accu_4_1))))
(assert (=> exec_5_1_0 (and (not stmt_6_1_0) stmt_6_1_1 (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_5_1_1 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_1 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_1 (= heap_5 heap_4)))
(assert (=> exec_5_1_1 (and (not stmt_6_1_0) (not stmt_6_1_1) stmt_6_1_2 (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_5_1_2 (= accu_5_1 (select heap_4 #x0000))))
(assert (=> exec_5_1_2 (= mem_5_1 accu_5_1)))
(assert (=> exec_5_1_2 (= heap_5 heap_4)))
(assert (=> exec_5_1_2 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) stmt_6_1_3 (not stmt_6_1_4) (not stmt_6_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_5_1_3 (= accu_5_1 (bvadd accu_4_1 #x0001))))
(assert (=> exec_5_1_3 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_3 (= heap_5 heap_4)))
(assert (=> exec_5_1_3 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) stmt_6_1_4 (not stmt_6_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_5_1_4 (= accu_5_1 (ite (= mem_4_1 (select heap_4 #x0000)) #x0001 #x0000))))
(assert (=> exec_5_1_4 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_4 (= heap_5 (ite (= mem_4_1 (select heap_4 #x0000)) (store heap_4 #x0000 accu_4_1) heap_4))))
(assert (=> exec_5_1_4 (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4) stmt_6_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_5_1_5 (= accu_5_1 accu_4_1)))
(assert (=> exec_5_1_5 (= mem_5_1 mem_4_1)))
(assert (=> exec_5_1_5 (= heap_5 heap_4)))
(assert (=> exec_5_1_5 (and (not stmt_6_1_0) (not stmt_6_1_1) stmt_6_1_2 (not stmt_6_1_3) (not stmt_6_1_4) (not stmt_6_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_5_2_0 (= accu_5_2 accu_4_2)))
(assert (=> exec_5_2_0 (= mem_5_2 mem_4_2)))
(assert (=> exec_5_2_0 (= heap_5 (store heap_4 #x0000 accu_4_2))))
(assert (=> exec_5_2_0 (and (not stmt_6_2_0) stmt_6_2_1 (not stmt_6_2_2) (not stmt_6_2_3) (not stmt_6_2_4) (not stmt_6_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_5_2_1 (= accu_5_2 accu_4_2)))
(assert (=> exec_5_2_1 (= mem_5_2 mem_4_2)))
(assert (=> exec_5_2_1 (= heap_5 heap_4)))
(assert (=> exec_5_2_1 (and (not stmt_6_2_0) (not stmt_6_2_1) stmt_6_2_2 (not stmt_6_2_3) (not stmt_6_2_4) (not stmt_6_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_5_2_2 (= accu_5_2 (select heap_4 #x0000))))
(assert (=> exec_5_2_2 (= mem_5_2 accu_5_2)))
(assert (=> exec_5_2_2 (= heap_5 heap_4)))
(assert (=> exec_5_2_2 (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) stmt_6_2_3 (not stmt_6_2_4) (not stmt_6_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_5_2_3 (= accu_5_2 (bvadd accu_4_2 #x0001))))
(assert (=> exec_5_2_3 (= mem_5_2 mem_4_2)))
(assert (=> exec_5_2_3 (= heap_5 heap_4)))
(assert (=> exec_5_2_3 (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) (not stmt_6_2_3) stmt_6_2_4 (not stmt_6_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_5_2_4 (= accu_5_2 (ite (= mem_4_2 (select heap_4 #x0000)) #x0001 #x0000))))
(assert (=> exec_5_2_4 (= mem_5_2 mem_4_2)))
(assert (=> exec_5_2_4 (= heap_5 (ite (= mem_4_2 (select heap_4 #x0000)) (store heap_4 #x0000 accu_4_2) heap_4))))
(assert (=> exec_5_2_4 (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) (not stmt_6_2_3) (not stmt_6_2_4) stmt_6_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_5_2_5 (= accu_5_2 accu_4_2)))
(assert (=> exec_5_2_5 (= mem_5_2 mem_4_2)))
(assert (=> exec_5_2_5 (= heap_5 heap_4)))
(assert (=> exec_5_2_5 (and (not stmt_6_2_0) (not stmt_6_2_1) stmt_6_2_2 (not stmt_6_2_3) (not stmt_6_2_4) (not stmt_6_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_5_1 sync_5_0)) (= accu_5_1 accu_4_1)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= mem_5_1 mem_4_1)))

(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_0 stmt_5_1_0)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_1 stmt_5_1_1)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_2 stmt_5_1_2)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_3 stmt_5_1_3)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_4 stmt_5_1_4)))
(assert (=> (not (or thread_5_1 sync_5_0)) (= stmt_6_1_5 stmt_5_1_5)))

(assert (=> (not (or thread_5_2 sync_5_0)) (= accu_5_2 accu_4_2)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= mem_5_2 mem_4_2)))

(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_0 stmt_5_2_0)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_1 stmt_5_2_1)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_2 stmt_5_2_2)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_3 stmt_5_2_3)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_4 stmt_5_2_4)))
(assert (=> (not (or thread_5_2 sync_5_0)) (= stmt_6_2_5 stmt_5_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_1 () Bool)
(declare-fun thread_6_2 () Bool)

(assert (xor thread_6_1 thread_6_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_6_0 () Bool)

; all threads synchronized?
(assert (= sync_6_0 (and stmt_6_1_1 stmt_6_2_1 (or thread_6_1 thread_6_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_6_1_1 (not sync_6_0)) (not thread_6_1))) ; barrier 0: thread 1
(assert (=> (and stmt_6_2_1 (not sync_6_0)) (not thread_6_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_1_0 () Bool)
(declare-fun exec_6_1_1 () Bool)
(declare-fun exec_6_1_2 () Bool)
(declare-fun exec_6_1_3 () Bool)
(declare-fun exec_6_1_4 () Bool)
(declare-fun exec_6_1_5 () Bool)

(declare-fun exec_6_2_0 () Bool)
(declare-fun exec_6_2_1 () Bool)
(declare-fun exec_6_2_2 () Bool)
(declare-fun exec_6_2_3 () Bool)
(declare-fun exec_6_2_4 () Bool)
(declare-fun exec_6_2_5 () Bool)

(assert (= exec_6_1_0 (and stmt_6_1_0 thread_6_1)))
(assert (= exec_6_1_1 (and stmt_6_1_1 sync_6_0)))
(assert (= exec_6_1_2 (and stmt_6_1_2 thread_6_1)))
(assert (= exec_6_1_3 (and stmt_6_1_3 thread_6_1)))
(assert (= exec_6_1_4 (and stmt_6_1_4 thread_6_1)))
(assert (= exec_6_1_5 (and stmt_6_1_5 thread_6_1)))

(assert (= exec_6_2_0 (and stmt_6_2_0 thread_6_2)))
(assert (= exec_6_2_1 (and stmt_6_2_1 sync_6_0)))
(assert (= exec_6_2_2 (and stmt_6_2_2 thread_6_2)))
(assert (= exec_6_2_3 (and stmt_6_2_3 thread_6_2)))
(assert (= exec_6_2_4 (and stmt_6_2_4 thread_6_2)))
(assert (= exec_6_2_5 (and stmt_6_2_5 thread_6_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_1_0 () Bool)
(declare-fun stmt_7_1_1 () Bool)
(declare-fun stmt_7_1_2 () Bool)
(declare-fun stmt_7_1_3 () Bool)
(declare-fun stmt_7_1_4 () Bool)
(declare-fun stmt_7_1_5 () Bool)

(declare-fun stmt_7_2_0 () Bool)
(declare-fun stmt_7_2_1 () Bool)
(declare-fun stmt_7_2_2 () Bool)
(declare-fun stmt_7_2_3 () Bool)
(declare-fun stmt_7_2_4 () Bool)
(declare-fun stmt_7_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_6_1 () (_ BitVec 16))
(declare-fun accu_6_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_6_1 () (_ BitVec 16))
(declare-fun mem_6_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_6_1_0 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_0 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_0 (= heap_6 (store heap_5 #x0000 accu_5_1))))
(assert (=> exec_6_1_0 (and (not stmt_7_1_0) stmt_7_1_1 (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_6_1_1 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_1 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_1 (= heap_6 heap_5)))
(assert (=> exec_6_1_1 (and (not stmt_7_1_0) (not stmt_7_1_1) stmt_7_1_2 (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_6_1_2 (= accu_6_1 (select heap_5 #x0000))))
(assert (=> exec_6_1_2 (= mem_6_1 accu_6_1)))
(assert (=> exec_6_1_2 (= heap_6 heap_5)))
(assert (=> exec_6_1_2 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) stmt_7_1_3 (not stmt_7_1_4) (not stmt_7_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_6_1_3 (= accu_6_1 (bvadd accu_5_1 #x0001))))
(assert (=> exec_6_1_3 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_3 (= heap_6 heap_5)))
(assert (=> exec_6_1_3 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) stmt_7_1_4 (not stmt_7_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_6_1_4 (= accu_6_1 (ite (= mem_5_1 (select heap_5 #x0000)) #x0001 #x0000))))
(assert (=> exec_6_1_4 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_4 (= heap_6 (ite (= mem_5_1 (select heap_5 #x0000)) (store heap_5 #x0000 accu_5_1) heap_5))))
(assert (=> exec_6_1_4 (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4) stmt_7_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_6_1_5 (= accu_6_1 accu_5_1)))
(assert (=> exec_6_1_5 (= mem_6_1 mem_5_1)))
(assert (=> exec_6_1_5 (= heap_6 heap_5)))
(assert (=> exec_6_1_5 (and (not stmt_7_1_0) (not stmt_7_1_1) stmt_7_1_2 (not stmt_7_1_3) (not stmt_7_1_4) (not stmt_7_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_6_2_0 (= accu_6_2 accu_5_2)))
(assert (=> exec_6_2_0 (= mem_6_2 mem_5_2)))
(assert (=> exec_6_2_0 (= heap_6 (store heap_5 #x0000 accu_5_2))))
(assert (=> exec_6_2_0 (and (not stmt_7_2_0) stmt_7_2_1 (not stmt_7_2_2) (not stmt_7_2_3) (not stmt_7_2_4) (not stmt_7_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_6_2_1 (= accu_6_2 accu_5_2)))
(assert (=> exec_6_2_1 (= mem_6_2 mem_5_2)))
(assert (=> exec_6_2_1 (= heap_6 heap_5)))
(assert (=> exec_6_2_1 (and (not stmt_7_2_0) (not stmt_7_2_1) stmt_7_2_2 (not stmt_7_2_3) (not stmt_7_2_4) (not stmt_7_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_6_2_2 (= accu_6_2 (select heap_5 #x0000))))
(assert (=> exec_6_2_2 (= mem_6_2 accu_6_2)))
(assert (=> exec_6_2_2 (= heap_6 heap_5)))
(assert (=> exec_6_2_2 (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) stmt_7_2_3 (not stmt_7_2_4) (not stmt_7_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_6_2_3 (= accu_6_2 (bvadd accu_5_2 #x0001))))
(assert (=> exec_6_2_3 (= mem_6_2 mem_5_2)))
(assert (=> exec_6_2_3 (= heap_6 heap_5)))
(assert (=> exec_6_2_3 (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) (not stmt_7_2_3) stmt_7_2_4 (not stmt_7_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_6_2_4 (= accu_6_2 (ite (= mem_5_2 (select heap_5 #x0000)) #x0001 #x0000))))
(assert (=> exec_6_2_4 (= mem_6_2 mem_5_2)))
(assert (=> exec_6_2_4 (= heap_6 (ite (= mem_5_2 (select heap_5 #x0000)) (store heap_5 #x0000 accu_5_2) heap_5))))
(assert (=> exec_6_2_4 (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) (not stmt_7_2_3) (not stmt_7_2_4) stmt_7_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_6_2_5 (= accu_6_2 accu_5_2)))
(assert (=> exec_6_2_5 (= mem_6_2 mem_5_2)))
(assert (=> exec_6_2_5 (= heap_6 heap_5)))
(assert (=> exec_6_2_5 (and (not stmt_7_2_0) (not stmt_7_2_1) stmt_7_2_2 (not stmt_7_2_3) (not stmt_7_2_4) (not stmt_7_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_6_1 sync_6_0)) (= accu_6_1 accu_5_1)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= mem_6_1 mem_5_1)))

(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_0 stmt_6_1_0)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_1 stmt_6_1_1)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_2 stmt_6_1_2)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_3 stmt_6_1_3)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_4 stmt_6_1_4)))
(assert (=> (not (or thread_6_1 sync_6_0)) (= stmt_7_1_5 stmt_6_1_5)))

(assert (=> (not (or thread_6_2 sync_6_0)) (= accu_6_2 accu_5_2)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= mem_6_2 mem_5_2)))

(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_0 stmt_6_2_0)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_1 stmt_6_2_1)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_2 stmt_6_2_2)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_3 stmt_6_2_3)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_4 stmt_6_2_4)))
(assert (=> (not (or thread_6_2 sync_6_0)) (= stmt_7_2_5 stmt_6_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_1 () Bool)
(declare-fun thread_7_2 () Bool)

(assert (xor thread_7_1 thread_7_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_7_0 () Bool)

; all threads synchronized?
(assert (= sync_7_0 (and stmt_7_1_1 stmt_7_2_1 (or thread_7_1 thread_7_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_7_1_1 (not sync_7_0)) (not thread_7_1))) ; barrier 0: thread 1
(assert (=> (and stmt_7_2_1 (not sync_7_0)) (not thread_7_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_1_0 () Bool)
(declare-fun exec_7_1_1 () Bool)
(declare-fun exec_7_1_2 () Bool)
(declare-fun exec_7_1_3 () Bool)
(declare-fun exec_7_1_4 () Bool)
(declare-fun exec_7_1_5 () Bool)

(declare-fun exec_7_2_0 () Bool)
(declare-fun exec_7_2_1 () Bool)
(declare-fun exec_7_2_2 () Bool)
(declare-fun exec_7_2_3 () Bool)
(declare-fun exec_7_2_4 () Bool)
(declare-fun exec_7_2_5 () Bool)

(assert (= exec_7_1_0 (and stmt_7_1_0 thread_7_1)))
(assert (= exec_7_1_1 (and stmt_7_1_1 sync_7_0)))
(assert (= exec_7_1_2 (and stmt_7_1_2 thread_7_1)))
(assert (= exec_7_1_3 (and stmt_7_1_3 thread_7_1)))
(assert (= exec_7_1_4 (and stmt_7_1_4 thread_7_1)))
(assert (= exec_7_1_5 (and stmt_7_1_5 thread_7_1)))

(assert (= exec_7_2_0 (and stmt_7_2_0 thread_7_2)))
(assert (= exec_7_2_1 (and stmt_7_2_1 sync_7_0)))
(assert (= exec_7_2_2 (and stmt_7_2_2 thread_7_2)))
(assert (= exec_7_2_3 (and stmt_7_2_3 thread_7_2)))
(assert (= exec_7_2_4 (and stmt_7_2_4 thread_7_2)))
(assert (= exec_7_2_5 (and stmt_7_2_5 thread_7_2)))

; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_1_0 () Bool)
(declare-fun stmt_8_1_1 () Bool)
(declare-fun stmt_8_1_2 () Bool)
(declare-fun stmt_8_1_3 () Bool)
(declare-fun stmt_8_1_4 () Bool)
(declare-fun stmt_8_1_5 () Bool)

(declare-fun stmt_8_2_0 () Bool)
(declare-fun stmt_8_2_1 () Bool)
(declare-fun stmt_8_2_2 () Bool)
(declare-fun stmt_8_2_3 () Bool)
(declare-fun stmt_8_2_4 () Bool)
(declare-fun stmt_8_2_5 () Bool)

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_7_1 () (_ BitVec 16))
(declare-fun accu_7_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_7_1 () (_ BitVec 16))
(declare-fun mem_7_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_7_1_0 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_0 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_0 (= heap_7 (store heap_6 #x0000 accu_6_1))))
(assert (=> exec_7_1_0 (and (not stmt_8_1_0) stmt_8_1_1 (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5))))

; thread 1@1: SYNC	0
(assert (=> exec_7_1_1 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_1 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_1 (= heap_7 heap_6)))
(assert (=> exec_7_1_1 (and (not stmt_8_1_0) (not stmt_8_1_1) stmt_8_1_2 (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5))))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_7_1_2 (= accu_7_1 (select heap_6 #x0000))))
(assert (=> exec_7_1_2 (= mem_7_1 accu_7_1)))
(assert (=> exec_7_1_2 (= heap_7 heap_6)))
(assert (=> exec_7_1_2 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) stmt_8_1_3 (not stmt_8_1_4) (not stmt_8_1_5))))

; thread 1@3: ADDI	1
(assert (=> exec_7_1_3 (= accu_7_1 (bvadd accu_6_1 #x0001))))
(assert (=> exec_7_1_3 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_3 (= heap_7 heap_6)))
(assert (=> exec_7_1_3 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) stmt_8_1_4 (not stmt_8_1_5))))

; thread 1@4: CAS	0
(assert (=> exec_7_1_4 (= accu_7_1 (ite (= mem_6_1 (select heap_6 #x0000)) #x0001 #x0000))))
(assert (=> exec_7_1_4 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_4 (= heap_7 (ite (= mem_6_1 (select heap_6 #x0000)) (store heap_6 #x0000 accu_6_1) heap_6))))
(assert (=> exec_7_1_4 (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4) stmt_8_1_5)))

; thread 1@5: JMP	LOOP
(assert (=> exec_7_1_5 (= accu_7_1 accu_6_1)))
(assert (=> exec_7_1_5 (= mem_7_1 mem_6_1)))
(assert (=> exec_7_1_5 (= heap_7 heap_6)))
(assert (=> exec_7_1_5 (and (not stmt_8_1_0) (not stmt_8_1_1) stmt_8_1_2 (not stmt_8_1_3) (not stmt_8_1_4) (not stmt_8_1_5))))

; thread 2@0: STORE	0
(assert (=> exec_7_2_0 (= accu_7_2 accu_6_2)))
(assert (=> exec_7_2_0 (= mem_7_2 mem_6_2)))
(assert (=> exec_7_2_0 (= heap_7 (store heap_6 #x0000 accu_6_2))))
(assert (=> exec_7_2_0 (and (not stmt_8_2_0) stmt_8_2_1 (not stmt_8_2_2) (not stmt_8_2_3) (not stmt_8_2_4) (not stmt_8_2_5))))

; thread 2@1: SYNC	0
(assert (=> exec_7_2_1 (= accu_7_2 accu_6_2)))
(assert (=> exec_7_2_1 (= mem_7_2 mem_6_2)))
(assert (=> exec_7_2_1 (= heap_7 heap_6)))
(assert (=> exec_7_2_1 (and (not stmt_8_2_0) (not stmt_8_2_1) stmt_8_2_2 (not stmt_8_2_3) (not stmt_8_2_4) (not stmt_8_2_5))))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_7_2_2 (= accu_7_2 (select heap_6 #x0000))))
(assert (=> exec_7_2_2 (= mem_7_2 accu_7_2)))
(assert (=> exec_7_2_2 (= heap_7 heap_6)))
(assert (=> exec_7_2_2 (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) stmt_8_2_3 (not stmt_8_2_4) (not stmt_8_2_5))))

; thread 2@3: ADDI	1
(assert (=> exec_7_2_3 (= accu_7_2 (bvadd accu_6_2 #x0001))))
(assert (=> exec_7_2_3 (= mem_7_2 mem_6_2)))
(assert (=> exec_7_2_3 (= heap_7 heap_6)))
(assert (=> exec_7_2_3 (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) (not stmt_8_2_3) stmt_8_2_4 (not stmt_8_2_5))))

; thread 2@4: CAS	0
(assert (=> exec_7_2_4 (= accu_7_2 (ite (= mem_6_2 (select heap_6 #x0000)) #x0001 #x0000))))
(assert (=> exec_7_2_4 (= mem_7_2 mem_6_2)))
(assert (=> exec_7_2_4 (= heap_7 (ite (= mem_6_2 (select heap_6 #x0000)) (store heap_6 #x0000 accu_6_2) heap_6))))
(assert (=> exec_7_2_4 (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) (not stmt_8_2_3) (not stmt_8_2_4) stmt_8_2_5)))

; thread 2@5: JMP	LOOP
(assert (=> exec_7_2_5 (= accu_7_2 accu_6_2)))
(assert (=> exec_7_2_5 (= mem_7_2 mem_6_2)))
(assert (=> exec_7_2_5 (= heap_7 heap_6)))
(assert (=> exec_7_2_5 (and (not stmt_8_2_0) (not stmt_8_2_1) stmt_8_2_2 (not stmt_8_2_3) (not stmt_8_2_4) (not stmt_8_2_5))))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_7_1 sync_7_0)) (= accu_7_1 accu_6_1)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= mem_7_1 mem_6_1)))

(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_0 stmt_7_1_0)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_1 stmt_7_1_1)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_2 stmt_7_1_2)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_3 stmt_7_1_3)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_4 stmt_7_1_4)))
(assert (=> (not (or thread_7_1 sync_7_0)) (= stmt_8_1_5 stmt_7_1_5)))

(assert (=> (not (or thread_7_2 sync_7_0)) (= accu_7_2 accu_6_2)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= mem_7_2 mem_6_2)))

(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_0 stmt_7_2_0)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_1 stmt_7_2_1)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_2 stmt_7_2_2)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_3 stmt_7_2_3)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_4 stmt_7_2_4)))
(assert (=> (not (or thread_7_2 sync_7_0)) (= stmt_8_2_5 stmt_7_2_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_1 () Bool)
(declare-fun thread_8_2 () Bool)

(assert (xor thread_8_1 thread_8_2))

; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sync variables - sync_<step>_<id>
(declare-fun sync_8_0 () Bool)

; all threads synchronized?
(assert (= sync_8_0 (and stmt_8_1_1 stmt_8_2_1 (or thread_8_1 thread_8_2))))

; prevent scheduling of waiting threads
(assert (=> (and stmt_8_1_1 (not sync_8_0)) (not thread_8_1))) ; barrier 0: thread 1
(assert (=> (and stmt_8_2_1 (not sync_8_0)) (not thread_8_2))) ; barrier 0: thread 2

; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_1_0 () Bool)
(declare-fun exec_8_1_1 () Bool)
(declare-fun exec_8_1_2 () Bool)
(declare-fun exec_8_1_3 () Bool)
(declare-fun exec_8_1_4 () Bool)
(declare-fun exec_8_1_5 () Bool)

(declare-fun exec_8_2_0 () Bool)
(declare-fun exec_8_2_1 () Bool)
(declare-fun exec_8_2_2 () Bool)
(declare-fun exec_8_2_3 () Bool)
(declare-fun exec_8_2_4 () Bool)
(declare-fun exec_8_2_5 () Bool)

(assert (= exec_8_1_0 (and stmt_8_1_0 thread_8_1)))
(assert (= exec_8_1_1 (and stmt_8_1_1 sync_8_0)))
(assert (= exec_8_1_2 (and stmt_8_1_2 thread_8_1)))
(assert (= exec_8_1_3 (and stmt_8_1_3 thread_8_1)))
(assert (= exec_8_1_4 (and stmt_8_1_4 thread_8_1)))
(assert (= exec_8_1_5 (and stmt_8_1_5 thread_8_1)))

(assert (= exec_8_2_0 (and stmt_8_2_0 thread_8_2)))
(assert (= exec_8_2_1 (and stmt_8_2_1 sync_8_0)))
(assert (= exec_8_2_2 (and stmt_8_2_2 thread_8_2)))
(assert (= exec_8_2_3 (and stmt_8_2_3 thread_8_2)))
(assert (= exec_8_2_4 (and stmt_8_2_4 thread_8_2)))
(assert (= exec_8_2_5 (and stmt_8_2_5 thread_8_2)))

; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu states - accu_<step>_<thread>
(declare-fun accu_8_1 () (_ BitVec 16))
(declare-fun accu_8_2 () (_ BitVec 16))

; mem states - mem_<step>_<thread>
(declare-fun mem_8_1 () (_ BitVec 16))
(declare-fun mem_8_2 () (_ BitVec 16))

; heap states - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

; thread 1@0: STORE	0
(assert (=> exec_8_1_0 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_0 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_0 (= heap_8 (store heap_7 #x0000 accu_7_1))))

; thread 1@1: SYNC	0
(assert (=> exec_8_1_1 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_1 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_1 (= heap_8 heap_7)))

; thread 1@2: LOOP: MEM	0
(assert (=> exec_8_1_2 (= accu_8_1 (select heap_7 #x0000))))
(assert (=> exec_8_1_2 (= mem_8_1 accu_8_1)))
(assert (=> exec_8_1_2 (= heap_8 heap_7)))

; thread 1@3: ADDI	1
(assert (=> exec_8_1_3 (= accu_8_1 (bvadd accu_7_1 #x0001))))
(assert (=> exec_8_1_3 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_3 (= heap_8 heap_7)))

; thread 1@4: CAS	0
(assert (=> exec_8_1_4 (= accu_8_1 (ite (= mem_7_1 (select heap_7 #x0000)) #x0001 #x0000))))
(assert (=> exec_8_1_4 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_4 (= heap_8 (ite (= mem_7_1 (select heap_7 #x0000)) (store heap_7 #x0000 accu_7_1) heap_7))))

; thread 1@5: JMP	LOOP
(assert (=> exec_8_1_5 (= accu_8_1 accu_7_1)))
(assert (=> exec_8_1_5 (= mem_8_1 mem_7_1)))
(assert (=> exec_8_1_5 (= heap_8 heap_7)))

; thread 2@0: STORE	0
(assert (=> exec_8_2_0 (= accu_8_2 accu_7_2)))
(assert (=> exec_8_2_0 (= mem_8_2 mem_7_2)))
(assert (=> exec_8_2_0 (= heap_8 (store heap_7 #x0000 accu_7_2))))

; thread 2@1: SYNC	0
(assert (=> exec_8_2_1 (= accu_8_2 accu_7_2)))
(assert (=> exec_8_2_1 (= mem_8_2 mem_7_2)))
(assert (=> exec_8_2_1 (= heap_8 heap_7)))

; thread 2@2: LOOP: MEM	0
(assert (=> exec_8_2_2 (= accu_8_2 (select heap_7 #x0000))))
(assert (=> exec_8_2_2 (= mem_8_2 accu_8_2)))
(assert (=> exec_8_2_2 (= heap_8 heap_7)))

; thread 2@3: ADDI	1
(assert (=> exec_8_2_3 (= accu_8_2 (bvadd accu_7_2 #x0001))))
(assert (=> exec_8_2_3 (= mem_8_2 mem_7_2)))
(assert (=> exec_8_2_3 (= heap_8 heap_7)))

; thread 2@4: CAS	0
(assert (=> exec_8_2_4 (= accu_8_2 (ite (= mem_7_2 (select heap_7 #x0000)) #x0001 #x0000))))
(assert (=> exec_8_2_4 (= mem_8_2 mem_7_2)))
(assert (=> exec_8_2_4 (= heap_8 (ite (= mem_7_2 (select heap_7 #x0000)) (store heap_7 #x0000 accu_7_2) heap_7))))

; thread 2@5: JMP	LOOP
(assert (=> exec_8_2_5 (= accu_8_2 accu_7_2)))
(assert (=> exec_8_2_5 (= mem_8_2 mem_7_2)))
(assert (=> exec_8_2_5 (= heap_8 heap_7)))

; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (not (or thread_8_1 sync_8_0)) (= accu_8_1 accu_7_1)))
(assert (=> (not (or thread_8_1 sync_8_0)) (= mem_8_1 mem_7_1)))

(assert (=> (not (or thread_8_2 sync_8_0)) (= accu_8_2 accu_7_2)))
(assert (=> (not (or thread_8_2 sync_8_0)) (= mem_8_2 mem_7_2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; exit code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (= exit_code #x0000))
