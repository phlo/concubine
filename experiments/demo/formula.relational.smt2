(set-logic QF_AUFBV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_0_0 () (_ BitVec 16))
(declare-fun accu_0_1 () (_ BitVec 16))
(declare-fun accu_0_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_0_0 () (_ BitVec 16))
(declare-fun mem_0_1 () (_ BitVec 16))
(declare-fun mem_0_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_0_0 () (_ BitVec 16))
(declare-fun sb-adr_0_1 () (_ BitVec 16))
(declare-fun sb-adr_0_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_0_0 () (_ BitVec 16))
(declare-fun sb-val_0_1 () (_ BitVec 16))
(declare-fun sb-val_0_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_0_0 () Bool)
(declare-fun sb-full_0_1 () Bool)
(declare-fun sb-full_0_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_0_0_0 () Bool)
(declare-fun stmt_0_0_1 () Bool)
(declare-fun stmt_0_0_2 () Bool)
(declare-fun stmt_0_0_3 () Bool)
(declare-fun stmt_0_0_4 () Bool)

(declare-fun stmt_0_1_0 () Bool)
(declare-fun stmt_0_1_1 () Bool)
(declare-fun stmt_0_1_2 () Bool)
(declare-fun stmt_0_1_3 () Bool)
(declare-fun stmt_0_1_4 () Bool)

(declare-fun stmt_0_2_0 () Bool)
(declare-fun stmt_0_2_1 () Bool)
(declare-fun stmt_0_2_2 () Bool)
(declare-fun stmt_0_2_3 () Bool)
(declare-fun stmt_0_2_4 () Bool)
(declare-fun stmt_0_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_0_0_0 () Bool)
(declare-fun block_0_0_1 () Bool)
(declare-fun block_0_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_0_0 () Bool)
(declare-fun halt_0_1 () Bool)
(declare-fun halt_0_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_0 () Bool)

; exit code variable
(declare-fun exit-code () (_ BitVec 16))

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_0_0 () Bool)
(declare-fun thread_0_1 () Bool)
(declare-fun thread_0_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_0_0_0 () Bool)
(declare-fun exec_0_0_1 () Bool)
(declare-fun exec_0_0_2 () Bool)
(declare-fun exec_0_0_3 () Bool)
(declare-fun exec_0_0_4 () Bool)

(declare-fun exec_0_1_0 () Bool)
(declare-fun exec_0_1_1 () Bool)
(declare-fun exec_0_1_2 () Bool)
(declare-fun exec_0_1_3 () Bool)
(declare-fun exec_0_1_4 () Bool)

(declare-fun exec_0_2_0 () Bool)
(declare-fun exec_0_2_1 () Bool)
(declare-fun exec_0_2_2 () Bool)
(declare-fun exec_0_2_3 () Bool)
(declare-fun exec_0_2_4 () Bool)
(declare-fun exec_0_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_0_0 () Bool)
(declare-fun flush_0_1 () Bool)
(declare-fun flush_0_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_0_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))
(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))
(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))
(assert (= exec_0_0_3 (and stmt_0_0_3 thread_0_0)))
(assert (= exec_0_0_4 (and stmt_0_0_4 thread_0_0)))

(assert (= exec_0_1_0 (and stmt_0_1_0 thread_0_1)))
(assert (= exec_0_1_1 (and stmt_0_1_1 thread_0_1)))
(assert (= exec_0_1_2 (and stmt_0_1_2 thread_0_1)))
(assert (= exec_0_1_3 (and stmt_0_1_3 thread_0_1)))
(assert (= exec_0_1_4 (and stmt_0_1_4 thread_0_1)))

(assert (= exec_0_2_0 (and stmt_0_2_0 thread_0_2)))
(assert (= exec_0_2_1 (and stmt_0_2_1 thread_0_2)))
(assert (= exec_0_2_2 (and stmt_0_2_2 thread_0_2)))
(assert (= exec_0_2_3 (and stmt_0_2_3 thread_0_2)))
(assert (= exec_0_2_4 (and stmt_0_2_4 thread_0_2)))
(assert (= exec_0_2_5 (and stmt_0_2_5 thread_0_2)))

; checkpoint variables - check_<step>_<id>
(assert (not check_0_0))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_0_0 flush_0_0 thread_0_1 flush_0_1 thread_0_2 flush_0_2 exit_0))
(assert (or (not thread_0_0) (not flush_0_0)))
(assert (or (not thread_0_0) (not thread_0_1)))
(assert (or (not thread_0_0) (not flush_0_1)))
(assert (or (not thread_0_0) (not thread_0_2)))
(assert (or (not thread_0_0) (not flush_0_2)))
(assert (or (not thread_0_0) (not exit_0)))
(assert (or (not flush_0_0) (not thread_0_1)))
(assert (or (not flush_0_0) (not flush_0_1)))
(assert (or (not flush_0_0) (not thread_0_2)))
(assert (or (not flush_0_0) (not flush_0_2)))
(assert (or (not flush_0_0) (not exit_0)))
(assert (or (not thread_0_1) (not flush_0_1)))
(assert (or (not thread_0_1) (not thread_0_2)))
(assert (or (not thread_0_1) (not flush_0_2)))
(assert (or (not thread_0_1) (not exit_0)))
(assert (or (not flush_0_1) (not thread_0_2)))
(assert (or (not flush_0_1) (not flush_0_2)))
(assert (or (not flush_0_1) (not exit_0)))
(assert (or (not thread_0_2) (not flush_0_2)))
(assert (or (not thread_0_2) (not exit_0)))
(assert (or (not flush_0_2) (not exit_0)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_0_0 (=> (or stmt_0_0_1 stmt_0_0_4) (not thread_0_0)) (not flush_0_0)))
(assert (ite sb-full_0_1 (=> (or stmt_0_1_1 stmt_0_1_4) (not thread_0_1)) (not flush_0_1)))
(assert (=> (not sb-full_0_2) (not flush_0_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_0_0_0 (not check_0_0)) (not thread_0_0))) ; checkpoint 0: thread 0
(assert (=> (and block_0_0_1 (not check_0_0)) (not thread_0_1))) ; checkpoint 0: thread 1
(assert (=> (and block_0_0_2 (not check_0_0)) (not thread_0_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_0_0 (not thread_0_0)))
(assert (=> halt_0_1 (not thread_0_1)))

; state variable initializations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_0_0 #x0000))
(assert (= accu_0_1 #x0000))
(assert (= accu_0_2 #x0000))

; mem variables - mem_<step>_<thread>
(assert (= mem_0_0 #x0000))
(assert (= mem_0_1 #x0000))
(assert (= mem_0_2 #x0000))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_0_0 #x0000))
(assert (= sb-adr_0_1 #x0000))
(assert (= sb-adr_0_2 #x0000))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_0_0 #x0000))
(assert (= sb-val_0_1 #x0000))
(assert (= sb-val_0_2 #x0000))

; store buffer full variables - sb-full_<step>_<thread>
(assert (not sb-full_0_0))
(assert (not sb-full_0_1))
(assert (not sb-full_0_2))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert stmt_0_0_0)
(assert (not stmt_0_0_1))
(assert (not stmt_0_0_2))
(assert (not stmt_0_0_3))
(assert (not stmt_0_0_4))

(assert stmt_0_1_0)
(assert (not stmt_0_1_1))
(assert (not stmt_0_1_2))
(assert (not stmt_0_1_3))
(assert (not stmt_0_1_4))

(assert stmt_0_2_0)
(assert (not stmt_0_2_1))
(assert (not stmt_0_2_2))
(assert (not stmt_0_2_3))
(assert (not stmt_0_2_4))
(assert (not stmt_0_2_5))

; blocking variables - block_<step>_<id>_<thread>
(assert (not block_0_0_0))
(assert (not block_0_0_1))
(assert (not block_0_0_2))

; halt variables - halt_<step>_<thread>
(assert (not halt_0_0))
(assert (not halt_0_1))
(assert (not halt_0_2))

; heap variable - heap_<step>
(assert (= (select heap_0 #x0000) #x0000))
(assert (= (select heap_0 #x0001) #x0000))

; exit flag variable - exit_<step>
(assert (not exit_0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_1_0 () (_ BitVec 16))
(declare-fun accu_1_1 () (_ BitVec 16))
(declare-fun accu_1_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_1_0 () (_ BitVec 16))
(declare-fun mem_1_1 () (_ BitVec 16))
(declare-fun mem_1_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_1_0 () (_ BitVec 16))
(declare-fun sb-adr_1_1 () (_ BitVec 16))
(declare-fun sb-adr_1_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_1_0 () (_ BitVec 16))
(declare-fun sb-val_1_1 () (_ BitVec 16))
(declare-fun sb-val_1_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_1_0 () Bool)
(declare-fun sb-full_1_1 () Bool)
(declare-fun sb-full_1_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_0_0 () Bool)
(declare-fun stmt_1_0_1 () Bool)
(declare-fun stmt_1_0_2 () Bool)
(declare-fun stmt_1_0_3 () Bool)
(declare-fun stmt_1_0_4 () Bool)

(declare-fun stmt_1_1_0 () Bool)
(declare-fun stmt_1_1_1 () Bool)
(declare-fun stmt_1_1_2 () Bool)
(declare-fun stmt_1_1_3 () Bool)
(declare-fun stmt_1_1_4 () Bool)

(declare-fun stmt_1_2_0 () Bool)
(declare-fun stmt_1_2_1 () Bool)
(declare-fun stmt_1_2_2 () Bool)
(declare-fun stmt_1_2_3 () Bool)
(declare-fun stmt_1_2_4 () Bool)
(declare-fun stmt_1_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_1_0_0 () Bool)
(declare-fun block_1_0_1 () Bool)
(declare-fun block_1_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_1_0 () Bool)
(declare-fun halt_1_1 () Bool)
(declare-fun halt_1_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_1 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_0 () Bool)
(declare-fun thread_1_1 () Bool)
(declare-fun thread_1_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_0_0 () Bool)
(declare-fun exec_1_0_1 () Bool)
(declare-fun exec_1_0_2 () Bool)
(declare-fun exec_1_0_3 () Bool)
(declare-fun exec_1_0_4 () Bool)

(declare-fun exec_1_1_0 () Bool)
(declare-fun exec_1_1_1 () Bool)
(declare-fun exec_1_1_2 () Bool)
(declare-fun exec_1_1_3 () Bool)
(declare-fun exec_1_1_4 () Bool)

(declare-fun exec_1_2_0 () Bool)
(declare-fun exec_1_2_1 () Bool)
(declare-fun exec_1_2_2 () Bool)
(declare-fun exec_1_2_3 () Bool)
(declare-fun exec_1_2_4 () Bool)
(declare-fun exec_1_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_1_0 () Bool)
(declare-fun flush_1_1 () Bool)
(declare-fun flush_1_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_1_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))
(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))
(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))
(assert (= exec_1_0_3 (and stmt_1_0_3 thread_1_0)))
(assert (= exec_1_0_4 (and stmt_1_0_4 thread_1_0)))

(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))
(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))
(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))
(assert (= exec_1_1_3 (and stmt_1_1_3 thread_1_1)))
(assert (= exec_1_1_4 (and stmt_1_1_4 thread_1_1)))

(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))
(assert (= exec_1_2_1 (and stmt_1_2_1 thread_1_2)))
(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))
(assert (= exec_1_2_3 (and stmt_1_2_3 thread_1_2)))
(assert (= exec_1_2_4 (and stmt_1_2_4 thread_1_2)))
(assert (= exec_1_2_5 (and stmt_1_2_5 thread_1_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_1_0 (and block_1_0_0 block_1_0_1 block_1_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1 thread_1_2 flush_1_2 exit_1))
(assert (or (not thread_1_0) (not flush_1_0)))
(assert (or (not thread_1_0) (not thread_1_1)))
(assert (or (not thread_1_0) (not flush_1_1)))
(assert (or (not thread_1_0) (not thread_1_2)))
(assert (or (not thread_1_0) (not flush_1_2)))
(assert (or (not thread_1_0) (not exit_1)))
(assert (or (not flush_1_0) (not thread_1_1)))
(assert (or (not flush_1_0) (not flush_1_1)))
(assert (or (not flush_1_0) (not thread_1_2)))
(assert (or (not flush_1_0) (not flush_1_2)))
(assert (or (not flush_1_0) (not exit_1)))
(assert (or (not thread_1_1) (not flush_1_1)))
(assert (or (not thread_1_1) (not thread_1_2)))
(assert (or (not thread_1_1) (not flush_1_2)))
(assert (or (not thread_1_1) (not exit_1)))
(assert (or (not flush_1_1) (not thread_1_2)))
(assert (or (not flush_1_1) (not flush_1_2)))
(assert (or (not flush_1_1) (not exit_1)))
(assert (or (not thread_1_2) (not flush_1_2)))
(assert (or (not thread_1_2) (not exit_1)))
(assert (or (not flush_1_2) (not exit_1)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_1_0 (=> (or stmt_1_0_1 stmt_1_0_4) (not thread_1_0)) (not flush_1_0)))
(assert (ite sb-full_1_1 (=> (or stmt_1_1_1 stmt_1_1_4) (not thread_1_1)) (not flush_1_1)))
(assert (=> (not sb-full_1_2) (not flush_1_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_1_0_0 (not check_1_0)) (not thread_1_0))) ; checkpoint 0: thread 0
(assert (=> (and block_1_0_1 (not check_1_0)) (not thread_1_1))) ; checkpoint 0: thread 1
(assert (=> (and block_1_0_2 (not check_1_0)) (not thread_1_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_1_0 (not thread_1_0)))
(assert (=> halt_1_1 (not thread_1_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_0_0_0 (and (= accu_1_0 (bvadd accu_0_0 #x0001)) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) stmt_1_0_1 (not stmt_1_0_2) (not stmt_1_0_3) (not stmt_1_0_4)) (= block_1_0_0 (ite check_0_0 false block_0_0_0)) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_1 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 #x0000) (= sb-val_1_0 accu_0_0) sb-full_1_0 (and (not stmt_1_0_0) (not stmt_1_0_1) stmt_1_0_2 (not stmt_1_0_3) (not stmt_1_0_4)) (= block_1_0_0 (ite check_0_0 false block_0_0_0)) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_2 (and (= accu_1_0 (ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) sb-val_0_0 (select heap_0 #x0001))) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) (not stmt_1_0_2) stmt_1_0_3 (not stmt_1_0_4)) (= block_1_0_0 (ite check_0_0 false block_0_0_0)) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_3 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) (not stmt_1_0_2) (not stmt_1_0_3) stmt_1_0_4) block_1_0_0 (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_4 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) (not stmt_1_0_2) (not stmt_1_0_3) (not stmt_1_0_4)) (= block_1_0_0 (ite check_0_0 false block_0_0_0)) (and halt_1_0 (ite (and halt_1_1 halt_1_2) (and exit_1 (= exit-code #x0000)) (not exit_1))) (= heap_1 heap_0))))

(assert (=> (not thread_0_0) (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) (and (= stmt_1_0_0 stmt_0_0_0) (= stmt_1_0_1 stmt_0_0_1) (= stmt_1_0_2 stmt_0_0_2) (= stmt_1_0_3 stmt_0_0_3) (= stmt_1_0_4 stmt_0_0_4)) (= block_1_0_0 (ite check_0_0 false block_0_0_0)) (= halt_1_0 halt_0_0))))

(assert (=> flush_0_0 (and (= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) (not exit_1))))

; thread 1
(assert (=> exec_0_1_0 (and (= accu_1_1 (bvadd accu_0_1 #x0001)) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) stmt_1_1_1 (not stmt_1_1_2) (not stmt_1_1_3) (not stmt_1_1_4)) (= block_1_0_1 (ite check_0_0 false block_0_0_1)) (= halt_1_1 halt_0_1) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_1_1 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 #x0001) (= sb-val_1_1 accu_0_1) sb-full_1_1 (and (not stmt_1_1_0) (not stmt_1_1_1) stmt_1_1_2 (not stmt_1_1_3) (not stmt_1_1_4)) (= block_1_0_1 (ite check_0_0 false block_0_0_1)) (= halt_1_1 halt_0_1) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_1_2 (and (= accu_1_1 (ite (and sb-full_0_1 (= sb-adr_0_1 #x0000)) sb-val_0_1 (select heap_0 #x0000))) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (not stmt_1_1_1) (not stmt_1_1_2) stmt_1_1_3 (not stmt_1_1_4)) (= block_1_0_1 (ite check_0_0 false block_0_0_1)) (= halt_1_1 halt_0_1) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_1_3 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (not stmt_1_1_1) (not stmt_1_1_2) (not stmt_1_1_3) stmt_1_1_4) block_1_0_1 (= halt_1_1 halt_0_1) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_1_4 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (not stmt_1_1_1) (not stmt_1_1_2) (not stmt_1_1_3) (not stmt_1_1_4)) (= block_1_0_1 (ite check_0_0 false block_0_0_1)) (and halt_1_1 (ite (and halt_1_0 halt_1_2) (and exit_1 (= exit-code #x0000)) (not exit_1))) (= heap_1 heap_0))))

(assert (=> (not thread_0_1) (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 (ite flush_0_1 false sb-full_0_1)) (and (= stmt_1_1_0 stmt_0_1_0) (= stmt_1_1_1 stmt_0_1_1) (= stmt_1_1_2 stmt_0_1_2) (= stmt_1_1_3 stmt_0_1_3) (= stmt_1_1_4 stmt_0_1_4)) (= block_1_0_1 (ite check_0_0 false block_0_0_1)) (= halt_1_1 halt_0_1))))

(assert (=> flush_0_1 (and (= heap_1 (store heap_0 sb-adr_0_1 sb-val_0_1)) (not exit_1))))

; thread 2
(assert (=> exec_0_2_0 (and (= accu_1_2 accu_0_2) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) stmt_1_2_1 (not stmt_1_2_2) (not stmt_1_2_3) (not stmt_1_2_4) (not stmt_1_2_5)) block_1_0_2 (= halt_1_2 halt_0_2) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_2_1 (and (= accu_1_2 (bvadd accu_0_2 (ite (and sb-full_0_2 (= sb-adr_0_2 #x0000)) sb-val_0_2 (select heap_0 #x0000)))) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) (not stmt_1_2_1) stmt_1_2_2 (not stmt_1_2_3) (not stmt_1_2_4) (not stmt_1_2_5)) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_2_2 (and (= accu_1_2 (bvadd accu_0_2 (ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) sb-val_0_2 (select heap_0 #x0001)))) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) (not stmt_1_2_1) (not stmt_1_2_2) stmt_1_2_3 (not stmt_1_2_4) (not stmt_1_2_5)) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_2_3 (and (= accu_1_2 accu_0_2) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) (not stmt_1_2_1) (not stmt_1_2_2) (not stmt_1_2_3) (ite (= accu_0_2 #x0000) (not stmt_1_2_4) stmt_1_2_4) (ite (= accu_0_2 #x0000) stmt_1_2_5 (not stmt_1_2_5))) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_2_4 (and (= accu_1_2 accu_0_2) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) (not stmt_1_2_1) (not stmt_1_2_2) (not stmt_1_2_3) stmt_1_2_4 (not stmt_1_2_5)) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2) (= heap_1 heap_0) exit_1 (= exit-code #x0000))))

(assert (=> exec_0_2_5 (and (= accu_1_2 accu_0_2) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 sb-full_0_2) (and (not stmt_1_2_0) (not stmt_1_2_1) (not stmt_1_2_2) (not stmt_1_2_3) (not stmt_1_2_4) stmt_1_2_5) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2) (= heap_1 heap_0) exit_1 (= exit-code #x0001))))

(assert (=> (not thread_0_2) (and (= accu_1_2 accu_0_2) (= mem_1_2 mem_0_2) (= sb-adr_1_2 sb-adr_0_2) (= sb-val_1_2 sb-val_0_2) (= sb-full_1_2 (ite flush_0_2 false sb-full_0_2)) (and (= stmt_1_2_0 stmt_0_2_0) (= stmt_1_2_1 stmt_0_2_1) (= stmt_1_2_2 stmt_0_2_2) (= stmt_1_2_3 stmt_0_2_3) (= stmt_1_2_4 stmt_0_2_4) (= stmt_1_2_5 stmt_0_2_5)) (= block_1_0_2 (ite check_0_0 false block_0_0_2)) (= halt_1_2 halt_0_2))))

(assert (=> flush_0_2 (and (= heap_1 (store heap_0 sb-adr_0_2 sb-val_0_2)) (not exit_1))))

; exited
(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_2_0 () (_ BitVec 16))
(declare-fun accu_2_1 () (_ BitVec 16))
(declare-fun accu_2_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_2_0 () (_ BitVec 16))
(declare-fun mem_2_1 () (_ BitVec 16))
(declare-fun mem_2_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_2_0 () (_ BitVec 16))
(declare-fun sb-adr_2_1 () (_ BitVec 16))
(declare-fun sb-adr_2_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_2_0 () (_ BitVec 16))
(declare-fun sb-val_2_1 () (_ BitVec 16))
(declare-fun sb-val_2_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_2_0 () Bool)
(declare-fun sb-full_2_1 () Bool)
(declare-fun sb-full_2_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_0_0 () Bool)
(declare-fun stmt_2_0_1 () Bool)
(declare-fun stmt_2_0_2 () Bool)
(declare-fun stmt_2_0_3 () Bool)
(declare-fun stmt_2_0_4 () Bool)

(declare-fun stmt_2_1_0 () Bool)
(declare-fun stmt_2_1_1 () Bool)
(declare-fun stmt_2_1_2 () Bool)
(declare-fun stmt_2_1_3 () Bool)
(declare-fun stmt_2_1_4 () Bool)

(declare-fun stmt_2_2_0 () Bool)
(declare-fun stmt_2_2_1 () Bool)
(declare-fun stmt_2_2_2 () Bool)
(declare-fun stmt_2_2_3 () Bool)
(declare-fun stmt_2_2_4 () Bool)
(declare-fun stmt_2_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_2_0_0 () Bool)
(declare-fun block_2_0_1 () Bool)
(declare-fun block_2_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_2_0 () Bool)
(declare-fun halt_2_1 () Bool)
(declare-fun halt_2_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_2 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_0 () Bool)
(declare-fun thread_2_1 () Bool)
(declare-fun thread_2_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_0_0 () Bool)
(declare-fun exec_2_0_1 () Bool)
(declare-fun exec_2_0_2 () Bool)
(declare-fun exec_2_0_3 () Bool)
(declare-fun exec_2_0_4 () Bool)

(declare-fun exec_2_1_0 () Bool)
(declare-fun exec_2_1_1 () Bool)
(declare-fun exec_2_1_2 () Bool)
(declare-fun exec_2_1_3 () Bool)
(declare-fun exec_2_1_4 () Bool)

(declare-fun exec_2_2_0 () Bool)
(declare-fun exec_2_2_1 () Bool)
(declare-fun exec_2_2_2 () Bool)
(declare-fun exec_2_2_3 () Bool)
(declare-fun exec_2_2_4 () Bool)
(declare-fun exec_2_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_2_0 () Bool)
(declare-fun flush_2_1 () Bool)
(declare-fun flush_2_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_2_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_2_0_0 (and stmt_2_0_0 thread_2_0)))
(assert (= exec_2_0_1 (and stmt_2_0_1 thread_2_0)))
(assert (= exec_2_0_2 (and stmt_2_0_2 thread_2_0)))
(assert (= exec_2_0_3 (and stmt_2_0_3 thread_2_0)))
(assert (= exec_2_0_4 (and stmt_2_0_4 thread_2_0)))

(assert (= exec_2_1_0 (and stmt_2_1_0 thread_2_1)))
(assert (= exec_2_1_1 (and stmt_2_1_1 thread_2_1)))
(assert (= exec_2_1_2 (and stmt_2_1_2 thread_2_1)))
(assert (= exec_2_1_3 (and stmt_2_1_3 thread_2_1)))
(assert (= exec_2_1_4 (and stmt_2_1_4 thread_2_1)))

(assert (= exec_2_2_0 (and stmt_2_2_0 thread_2_2)))
(assert (= exec_2_2_1 (and stmt_2_2_1 thread_2_2)))
(assert (= exec_2_2_2 (and stmt_2_2_2 thread_2_2)))
(assert (= exec_2_2_3 (and stmt_2_2_3 thread_2_2)))
(assert (= exec_2_2_4 (and stmt_2_2_4 thread_2_2)))
(assert (= exec_2_2_5 (and stmt_2_2_5 thread_2_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_2_0 (and block_2_0_0 block_2_0_1 block_2_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_2_0 flush_2_0 thread_2_1 flush_2_1 thread_2_2 flush_2_2 exit_2))
(assert (or (not thread_2_0) (not flush_2_0)))
(assert (or (not thread_2_0) (not thread_2_1)))
(assert (or (not thread_2_0) (not flush_2_1)))
(assert (or (not thread_2_0) (not thread_2_2)))
(assert (or (not thread_2_0) (not flush_2_2)))
(assert (or (not thread_2_0) (not exit_2)))
(assert (or (not flush_2_0) (not thread_2_1)))
(assert (or (not flush_2_0) (not flush_2_1)))
(assert (or (not flush_2_0) (not thread_2_2)))
(assert (or (not flush_2_0) (not flush_2_2)))
(assert (or (not flush_2_0) (not exit_2)))
(assert (or (not thread_2_1) (not flush_2_1)))
(assert (or (not thread_2_1) (not thread_2_2)))
(assert (or (not thread_2_1) (not flush_2_2)))
(assert (or (not thread_2_1) (not exit_2)))
(assert (or (not flush_2_1) (not thread_2_2)))
(assert (or (not flush_2_1) (not flush_2_2)))
(assert (or (not flush_2_1) (not exit_2)))
(assert (or (not thread_2_2) (not flush_2_2)))
(assert (or (not thread_2_2) (not exit_2)))
(assert (or (not flush_2_2) (not exit_2)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_2_0 (=> (or stmt_2_0_1 stmt_2_0_4) (not thread_2_0)) (not flush_2_0)))
(assert (ite sb-full_2_1 (=> (or stmt_2_1_1 stmt_2_1_4) (not thread_2_1)) (not flush_2_1)))
(assert (=> (not sb-full_2_2) (not flush_2_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_2_0_0 (not check_2_0)) (not thread_2_0))) ; checkpoint 0: thread 0
(assert (=> (and block_2_0_1 (not check_2_0)) (not thread_2_1))) ; checkpoint 0: thread 1
(assert (=> (and block_2_0_2 (not check_2_0)) (not thread_2_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_2_0 (not thread_2_0)))
(assert (=> halt_2_1 (not thread_2_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_1_0_0 (and (= accu_2_0 (bvadd accu_1_0 #x0001)) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) stmt_2_0_1 (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4)) (= block_2_0_0 (ite check_1_0 false block_1_0_0)) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_1 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 #x0000) (= sb-val_2_0 accu_1_0) sb-full_2_0 (and (not stmt_2_0_0) (not stmt_2_0_1) stmt_2_0_2 (not stmt_2_0_3) (not stmt_2_0_4)) (= block_2_0_0 (ite check_1_0 false block_1_0_0)) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_2 (and (= accu_2_0 (ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) sb-val_1_0 (select heap_1 #x0001))) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) stmt_2_0_3 (not stmt_2_0_4)) (= block_2_0_0 (ite check_1_0 false block_1_0_0)) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_3 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) stmt_2_0_4) block_2_0_0 (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_4 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) (not stmt_2_0_3) (not stmt_2_0_4)) (= block_2_0_0 (ite check_1_0 false block_1_0_0)) (and halt_2_0 (ite (and halt_2_1 halt_2_2) (and exit_2 (= exit-code #x0000)) (not exit_2))) (= heap_2 heap_1))))

(assert (=> (not thread_1_0) (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 (ite flush_1_0 false sb-full_1_0)) (and (= stmt_2_0_0 stmt_1_0_0) (= stmt_2_0_1 stmt_1_0_1) (= stmt_2_0_2 stmt_1_0_2) (= stmt_2_0_3 stmt_1_0_3) (= stmt_2_0_4 stmt_1_0_4)) (= block_2_0_0 (ite check_1_0 false block_1_0_0)) (= halt_2_0 halt_1_0))))

(assert (=> flush_1_0 (and (= heap_2 (store heap_1 sb-adr_1_0 sb-val_1_0)) (not exit_2))))

; thread 1
(assert (=> exec_1_1_0 (and (= accu_2_1 (bvadd accu_1_1 #x0001)) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) stmt_2_1_1 (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4)) (= block_2_0_1 (ite check_1_0 false block_1_0_1)) (= halt_2_1 halt_1_1) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_1_1 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 #x0001) (= sb-val_2_1 accu_1_1) sb-full_2_1 (and (not stmt_2_1_0) (not stmt_2_1_1) stmt_2_1_2 (not stmt_2_1_3) (not stmt_2_1_4)) (= block_2_0_1 (ite check_1_0 false block_1_0_1)) (= halt_2_1 halt_1_1) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_1_2 (and (= accu_2_1 (ite (and sb-full_1_1 (= sb-adr_1_1 #x0000)) sb-val_1_1 (select heap_1 #x0000))) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) stmt_2_1_3 (not stmt_2_1_4)) (= block_2_0_1 (ite check_1_0 false block_1_0_1)) (= halt_2_1 halt_1_1) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_1_3 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) stmt_2_1_4) block_2_0_1 (= halt_2_1 halt_1_1) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_1_4 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2) (not stmt_2_1_3) (not stmt_2_1_4)) (= block_2_0_1 (ite check_1_0 false block_1_0_1)) (and halt_2_1 (ite (and halt_2_0 halt_2_2) (and exit_2 (= exit-code #x0000)) (not exit_2))) (= heap_2 heap_1))))

(assert (=> (not thread_1_1) (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 (ite flush_1_1 false sb-full_1_1)) (and (= stmt_2_1_0 stmt_1_1_0) (= stmt_2_1_1 stmt_1_1_1) (= stmt_2_1_2 stmt_1_1_2) (= stmt_2_1_3 stmt_1_1_3) (= stmt_2_1_4 stmt_1_1_4)) (= block_2_0_1 (ite check_1_0 false block_1_0_1)) (= halt_2_1 halt_1_1))))

(assert (=> flush_1_1 (and (= heap_2 (store heap_1 sb-adr_1_1 sb-val_1_1)) (not exit_2))))

; thread 2
(assert (=> exec_1_2_0 (and (= accu_2_2 accu_1_2) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) stmt_2_2_1 (not stmt_2_2_2) (not stmt_2_2_3) (not stmt_2_2_4) (not stmt_2_2_5)) block_2_0_2 (= halt_2_2 halt_1_2) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_2_1 (and (= accu_2_2 (bvadd accu_1_2 (ite (and sb-full_1_2 (= sb-adr_1_2 #x0000)) sb-val_1_2 (select heap_1 #x0000)))) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) (not stmt_2_2_1) stmt_2_2_2 (not stmt_2_2_3) (not stmt_2_2_4) (not stmt_2_2_5)) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_2_2 (and (= accu_2_2 (bvadd accu_1_2 (ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) sb-val_1_2 (select heap_1 #x0001)))) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) stmt_2_2_3 (not stmt_2_2_4) (not stmt_2_2_5)) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_2_3 (and (= accu_2_2 accu_1_2) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) (not stmt_2_2_3) (ite (= accu_1_2 #x0000) (not stmt_2_2_4) stmt_2_2_4) (ite (= accu_1_2 #x0000) stmt_2_2_5 (not stmt_2_2_5))) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_2_4 (and (= accu_2_2 accu_1_2) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) (not stmt_2_2_3) stmt_2_2_4 (not stmt_2_2_5)) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2) (= heap_2 heap_1) exit_2 (= exit-code #x0000))))

(assert (=> exec_1_2_5 (and (= accu_2_2 accu_1_2) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 sb-full_1_2) (and (not stmt_2_2_0) (not stmt_2_2_1) (not stmt_2_2_2) (not stmt_2_2_3) (not stmt_2_2_4) stmt_2_2_5) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2) (= heap_2 heap_1) exit_2 (= exit-code #x0001))))

(assert (=> (not thread_1_2) (and (= accu_2_2 accu_1_2) (= mem_2_2 mem_1_2) (= sb-adr_2_2 sb-adr_1_2) (= sb-val_2_2 sb-val_1_2) (= sb-full_2_2 (ite flush_1_2 false sb-full_1_2)) (and (= stmt_2_2_0 stmt_1_2_0) (= stmt_2_2_1 stmt_1_2_1) (= stmt_2_2_2 stmt_1_2_2) (= stmt_2_2_3 stmt_1_2_3) (= stmt_2_2_4 stmt_1_2_4) (= stmt_2_2_5 stmt_1_2_5)) (= block_2_0_2 (ite check_1_0 false block_1_0_2)) (= halt_2_2 halt_1_2))))

(assert (=> flush_1_2 (and (= heap_2 (store heap_1 sb-adr_1_2 sb-val_1_2)) (not exit_2))))

; exited
(assert (=> exit_1 (and (= heap_2 heap_1) exit_2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_3_0 () (_ BitVec 16))
(declare-fun accu_3_1 () (_ BitVec 16))
(declare-fun accu_3_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_3_0 () (_ BitVec 16))
(declare-fun mem_3_1 () (_ BitVec 16))
(declare-fun mem_3_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_3_0 () (_ BitVec 16))
(declare-fun sb-adr_3_1 () (_ BitVec 16))
(declare-fun sb-adr_3_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_3_0 () (_ BitVec 16))
(declare-fun sb-val_3_1 () (_ BitVec 16))
(declare-fun sb-val_3_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_3_0 () Bool)
(declare-fun sb-full_3_1 () Bool)
(declare-fun sb-full_3_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_0_0 () Bool)
(declare-fun stmt_3_0_1 () Bool)
(declare-fun stmt_3_0_2 () Bool)
(declare-fun stmt_3_0_3 () Bool)
(declare-fun stmt_3_0_4 () Bool)

(declare-fun stmt_3_1_0 () Bool)
(declare-fun stmt_3_1_1 () Bool)
(declare-fun stmt_3_1_2 () Bool)
(declare-fun stmt_3_1_3 () Bool)
(declare-fun stmt_3_1_4 () Bool)

(declare-fun stmt_3_2_0 () Bool)
(declare-fun stmt_3_2_1 () Bool)
(declare-fun stmt_3_2_2 () Bool)
(declare-fun stmt_3_2_3 () Bool)
(declare-fun stmt_3_2_4 () Bool)
(declare-fun stmt_3_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_3_0_0 () Bool)
(declare-fun block_3_0_1 () Bool)
(declare-fun block_3_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_3_0 () Bool)
(declare-fun halt_3_1 () Bool)
(declare-fun halt_3_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_3 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_0 () Bool)
(declare-fun thread_3_1 () Bool)
(declare-fun thread_3_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_0_0 () Bool)
(declare-fun exec_3_0_1 () Bool)
(declare-fun exec_3_0_2 () Bool)
(declare-fun exec_3_0_3 () Bool)
(declare-fun exec_3_0_4 () Bool)

(declare-fun exec_3_1_0 () Bool)
(declare-fun exec_3_1_1 () Bool)
(declare-fun exec_3_1_2 () Bool)
(declare-fun exec_3_1_3 () Bool)
(declare-fun exec_3_1_4 () Bool)

(declare-fun exec_3_2_0 () Bool)
(declare-fun exec_3_2_1 () Bool)
(declare-fun exec_3_2_2 () Bool)
(declare-fun exec_3_2_3 () Bool)
(declare-fun exec_3_2_4 () Bool)
(declare-fun exec_3_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_3_0 () Bool)
(declare-fun flush_3_1 () Bool)
(declare-fun flush_3_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_3_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_3_0_0 (and stmt_3_0_0 thread_3_0)))
(assert (= exec_3_0_1 (and stmt_3_0_1 thread_3_0)))
(assert (= exec_3_0_2 (and stmt_3_0_2 thread_3_0)))
(assert (= exec_3_0_3 (and stmt_3_0_3 thread_3_0)))
(assert (= exec_3_0_4 (and stmt_3_0_4 thread_3_0)))

(assert (= exec_3_1_0 (and stmt_3_1_0 thread_3_1)))
(assert (= exec_3_1_1 (and stmt_3_1_1 thread_3_1)))
(assert (= exec_3_1_2 (and stmt_3_1_2 thread_3_1)))
(assert (= exec_3_1_3 (and stmt_3_1_3 thread_3_1)))
(assert (= exec_3_1_4 (and stmt_3_1_4 thread_3_1)))

(assert (= exec_3_2_0 (and stmt_3_2_0 thread_3_2)))
(assert (= exec_3_2_1 (and stmt_3_2_1 thread_3_2)))
(assert (= exec_3_2_2 (and stmt_3_2_2 thread_3_2)))
(assert (= exec_3_2_3 (and stmt_3_2_3 thread_3_2)))
(assert (= exec_3_2_4 (and stmt_3_2_4 thread_3_2)))
(assert (= exec_3_2_5 (and stmt_3_2_5 thread_3_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_3_0 (and block_3_0_0 block_3_0_1 block_3_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_3_0 flush_3_0 thread_3_1 flush_3_1 thread_3_2 flush_3_2 exit_3))
(assert (or (not thread_3_0) (not flush_3_0)))
(assert (or (not thread_3_0) (not thread_3_1)))
(assert (or (not thread_3_0) (not flush_3_1)))
(assert (or (not thread_3_0) (not thread_3_2)))
(assert (or (not thread_3_0) (not flush_3_2)))
(assert (or (not thread_3_0) (not exit_3)))
(assert (or (not flush_3_0) (not thread_3_1)))
(assert (or (not flush_3_0) (not flush_3_1)))
(assert (or (not flush_3_0) (not thread_3_2)))
(assert (or (not flush_3_0) (not flush_3_2)))
(assert (or (not flush_3_0) (not exit_3)))
(assert (or (not thread_3_1) (not flush_3_1)))
(assert (or (not thread_3_1) (not thread_3_2)))
(assert (or (not thread_3_1) (not flush_3_2)))
(assert (or (not thread_3_1) (not exit_3)))
(assert (or (not flush_3_1) (not thread_3_2)))
(assert (or (not flush_3_1) (not flush_3_2)))
(assert (or (not flush_3_1) (not exit_3)))
(assert (or (not thread_3_2) (not flush_3_2)))
(assert (or (not thread_3_2) (not exit_3)))
(assert (or (not flush_3_2) (not exit_3)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_3_0 (=> (or stmt_3_0_1 stmt_3_0_4) (not thread_3_0)) (not flush_3_0)))
(assert (ite sb-full_3_1 (=> (or stmt_3_1_1 stmt_3_1_4) (not thread_3_1)) (not flush_3_1)))
(assert (=> (not sb-full_3_2) (not flush_3_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_3_0_0 (not check_3_0)) (not thread_3_0))) ; checkpoint 0: thread 0
(assert (=> (and block_3_0_1 (not check_3_0)) (not thread_3_1))) ; checkpoint 0: thread 1
(assert (=> (and block_3_0_2 (not check_3_0)) (not thread_3_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_3_0 (not thread_3_0)))
(assert (=> halt_3_1 (not thread_3_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_2_0_0 (and (= accu_3_0 (bvadd accu_2_0 #x0001)) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) stmt_3_0_1 (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4)) (= block_3_0_0 (ite check_2_0 false block_2_0_0)) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_1 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 #x0000) (= sb-val_3_0 accu_2_0) sb-full_3_0 (and (not stmt_3_0_0) (not stmt_3_0_1) stmt_3_0_2 (not stmt_3_0_3) (not stmt_3_0_4)) (= block_3_0_0 (ite check_2_0 false block_2_0_0)) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_2 (and (= accu_3_0 (ite (and sb-full_2_0 (= sb-adr_2_0 #x0001)) sb-val_2_0 (select heap_2 #x0001))) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) stmt_3_0_3 (not stmt_3_0_4)) (= block_3_0_0 (ite check_2_0 false block_2_0_0)) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_3 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) stmt_3_0_4) block_3_0_0 (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_4 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) (not stmt_3_0_3) (not stmt_3_0_4)) (= block_3_0_0 (ite check_2_0 false block_2_0_0)) (and halt_3_0 (ite (and halt_3_1 halt_3_2) (and exit_3 (= exit-code #x0000)) (not exit_3))) (= heap_3 heap_2))))

(assert (=> (not thread_2_0) (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 (ite flush_2_0 false sb-full_2_0)) (and (= stmt_3_0_0 stmt_2_0_0) (= stmt_3_0_1 stmt_2_0_1) (= stmt_3_0_2 stmt_2_0_2) (= stmt_3_0_3 stmt_2_0_3) (= stmt_3_0_4 stmt_2_0_4)) (= block_3_0_0 (ite check_2_0 false block_2_0_0)) (= halt_3_0 halt_2_0))))

(assert (=> flush_2_0 (and (= heap_3 (store heap_2 sb-adr_2_0 sb-val_2_0)) (not exit_3))))

; thread 1
(assert (=> exec_2_1_0 (and (= accu_3_1 (bvadd accu_2_1 #x0001)) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) stmt_3_1_1 (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4)) (= block_3_0_1 (ite check_2_0 false block_2_0_1)) (= halt_3_1 halt_2_1) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_1_1 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 #x0001) (= sb-val_3_1 accu_2_1) sb-full_3_1 (and (not stmt_3_1_0) (not stmt_3_1_1) stmt_3_1_2 (not stmt_3_1_3) (not stmt_3_1_4)) (= block_3_0_1 (ite check_2_0 false block_2_0_1)) (= halt_3_1 halt_2_1) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_1_2 (and (= accu_3_1 (ite (and sb-full_2_1 (= sb-adr_2_1 #x0000)) sb-val_2_1 (select heap_2 #x0000))) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) stmt_3_1_3 (not stmt_3_1_4)) (= block_3_0_1 (ite check_2_0 false block_2_0_1)) (= halt_3_1 halt_2_1) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_1_3 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) stmt_3_1_4) block_3_0_1 (= halt_3_1 halt_2_1) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_1_4 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2) (not stmt_3_1_3) (not stmt_3_1_4)) (= block_3_0_1 (ite check_2_0 false block_2_0_1)) (and halt_3_1 (ite (and halt_3_0 halt_3_2) (and exit_3 (= exit-code #x0000)) (not exit_3))) (= heap_3 heap_2))))

(assert (=> (not thread_2_1) (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 (ite flush_2_1 false sb-full_2_1)) (and (= stmt_3_1_0 stmt_2_1_0) (= stmt_3_1_1 stmt_2_1_1) (= stmt_3_1_2 stmt_2_1_2) (= stmt_3_1_3 stmt_2_1_3) (= stmt_3_1_4 stmt_2_1_4)) (= block_3_0_1 (ite check_2_0 false block_2_0_1)) (= halt_3_1 halt_2_1))))

(assert (=> flush_2_1 (and (= heap_3 (store heap_2 sb-adr_2_1 sb-val_2_1)) (not exit_3))))

; thread 2
(assert (=> exec_2_2_0 (and (= accu_3_2 accu_2_2) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) stmt_3_2_1 (not stmt_3_2_2) (not stmt_3_2_3) (not stmt_3_2_4) (not stmt_3_2_5)) block_3_0_2 (= halt_3_2 halt_2_2) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_2_1 (and (= accu_3_2 (bvadd accu_2_2 (ite (and sb-full_2_2 (= sb-adr_2_2 #x0000)) sb-val_2_2 (select heap_2 #x0000)))) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) (not stmt_3_2_1) stmt_3_2_2 (not stmt_3_2_3) (not stmt_3_2_4) (not stmt_3_2_5)) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_2_2 (and (= accu_3_2 (bvadd accu_2_2 (ite (and sb-full_2_2 (= sb-adr_2_2 #x0001)) sb-val_2_2 (select heap_2 #x0001)))) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) stmt_3_2_3 (not stmt_3_2_4) (not stmt_3_2_5)) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_2_3 (and (= accu_3_2 accu_2_2) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) (not stmt_3_2_3) (ite (= accu_2_2 #x0000) (not stmt_3_2_4) stmt_3_2_4) (ite (= accu_2_2 #x0000) stmt_3_2_5 (not stmt_3_2_5))) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_2_4 (and (= accu_3_2 accu_2_2) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) (not stmt_3_2_3) stmt_3_2_4 (not stmt_3_2_5)) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2) (= heap_3 heap_2) exit_3 (= exit-code #x0000))))

(assert (=> exec_2_2_5 (and (= accu_3_2 accu_2_2) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 sb-full_2_2) (and (not stmt_3_2_0) (not stmt_3_2_1) (not stmt_3_2_2) (not stmt_3_2_3) (not stmt_3_2_4) stmt_3_2_5) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2) (= heap_3 heap_2) exit_3 (= exit-code #x0001))))

(assert (=> (not thread_2_2) (and (= accu_3_2 accu_2_2) (= mem_3_2 mem_2_2) (= sb-adr_3_2 sb-adr_2_2) (= sb-val_3_2 sb-val_2_2) (= sb-full_3_2 (ite flush_2_2 false sb-full_2_2)) (and (= stmt_3_2_0 stmt_2_2_0) (= stmt_3_2_1 stmt_2_2_1) (= stmt_3_2_2 stmt_2_2_2) (= stmt_3_2_3 stmt_2_2_3) (= stmt_3_2_4 stmt_2_2_4) (= stmt_3_2_5 stmt_2_2_5)) (= block_3_0_2 (ite check_2_0 false block_2_0_2)) (= halt_3_2 halt_2_2))))

(assert (=> flush_2_2 (and (= heap_3 (store heap_2 sb-adr_2_2 sb-val_2_2)) (not exit_3))))

; exited
(assert (=> exit_2 (and (= heap_3 heap_2) exit_3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_4_0 () (_ BitVec 16))
(declare-fun accu_4_1 () (_ BitVec 16))
(declare-fun accu_4_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_4_0 () (_ BitVec 16))
(declare-fun mem_4_1 () (_ BitVec 16))
(declare-fun mem_4_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_4_0 () (_ BitVec 16))
(declare-fun sb-adr_4_1 () (_ BitVec 16))
(declare-fun sb-adr_4_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_4_0 () (_ BitVec 16))
(declare-fun sb-val_4_1 () (_ BitVec 16))
(declare-fun sb-val_4_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_4_0 () Bool)
(declare-fun sb-full_4_1 () Bool)
(declare-fun sb-full_4_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_0_0 () Bool)
(declare-fun stmt_4_0_1 () Bool)
(declare-fun stmt_4_0_2 () Bool)
(declare-fun stmt_4_0_3 () Bool)
(declare-fun stmt_4_0_4 () Bool)

(declare-fun stmt_4_1_0 () Bool)
(declare-fun stmt_4_1_1 () Bool)
(declare-fun stmt_4_1_2 () Bool)
(declare-fun stmt_4_1_3 () Bool)
(declare-fun stmt_4_1_4 () Bool)

(declare-fun stmt_4_2_0 () Bool)
(declare-fun stmt_4_2_1 () Bool)
(declare-fun stmt_4_2_2 () Bool)
(declare-fun stmt_4_2_3 () Bool)
(declare-fun stmt_4_2_4 () Bool)
(declare-fun stmt_4_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_4_0_0 () Bool)
(declare-fun block_4_0_1 () Bool)
(declare-fun block_4_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_4_0 () Bool)
(declare-fun halt_4_1 () Bool)
(declare-fun halt_4_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_4 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_0 () Bool)
(declare-fun thread_4_1 () Bool)
(declare-fun thread_4_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_0_0 () Bool)
(declare-fun exec_4_0_1 () Bool)
(declare-fun exec_4_0_2 () Bool)
(declare-fun exec_4_0_3 () Bool)
(declare-fun exec_4_0_4 () Bool)

(declare-fun exec_4_1_0 () Bool)
(declare-fun exec_4_1_1 () Bool)
(declare-fun exec_4_1_2 () Bool)
(declare-fun exec_4_1_3 () Bool)
(declare-fun exec_4_1_4 () Bool)

(declare-fun exec_4_2_0 () Bool)
(declare-fun exec_4_2_1 () Bool)
(declare-fun exec_4_2_2 () Bool)
(declare-fun exec_4_2_3 () Bool)
(declare-fun exec_4_2_4 () Bool)
(declare-fun exec_4_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_4_0 () Bool)
(declare-fun flush_4_1 () Bool)
(declare-fun flush_4_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_4_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_4_0_0 (and stmt_4_0_0 thread_4_0)))
(assert (= exec_4_0_1 (and stmt_4_0_1 thread_4_0)))
(assert (= exec_4_0_2 (and stmt_4_0_2 thread_4_0)))
(assert (= exec_4_0_3 (and stmt_4_0_3 thread_4_0)))
(assert (= exec_4_0_4 (and stmt_4_0_4 thread_4_0)))

(assert (= exec_4_1_0 (and stmt_4_1_0 thread_4_1)))
(assert (= exec_4_1_1 (and stmt_4_1_1 thread_4_1)))
(assert (= exec_4_1_2 (and stmt_4_1_2 thread_4_1)))
(assert (= exec_4_1_3 (and stmt_4_1_3 thread_4_1)))
(assert (= exec_4_1_4 (and stmt_4_1_4 thread_4_1)))

(assert (= exec_4_2_0 (and stmt_4_2_0 thread_4_2)))
(assert (= exec_4_2_1 (and stmt_4_2_1 thread_4_2)))
(assert (= exec_4_2_2 (and stmt_4_2_2 thread_4_2)))
(assert (= exec_4_2_3 (and stmt_4_2_3 thread_4_2)))
(assert (= exec_4_2_4 (and stmt_4_2_4 thread_4_2)))
(assert (= exec_4_2_5 (and stmt_4_2_5 thread_4_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_4_0 (and block_4_0_0 block_4_0_1 block_4_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_4_0 flush_4_0 thread_4_1 flush_4_1 thread_4_2 flush_4_2 exit_4))
(assert (or (not thread_4_0) (not flush_4_0)))
(assert (or (not thread_4_0) (not thread_4_1)))
(assert (or (not thread_4_0) (not flush_4_1)))
(assert (or (not thread_4_0) (not thread_4_2)))
(assert (or (not thread_4_0) (not flush_4_2)))
(assert (or (not thread_4_0) (not exit_4)))
(assert (or (not flush_4_0) (not thread_4_1)))
(assert (or (not flush_4_0) (not flush_4_1)))
(assert (or (not flush_4_0) (not thread_4_2)))
(assert (or (not flush_4_0) (not flush_4_2)))
(assert (or (not flush_4_0) (not exit_4)))
(assert (or (not thread_4_1) (not flush_4_1)))
(assert (or (not thread_4_1) (not thread_4_2)))
(assert (or (not thread_4_1) (not flush_4_2)))
(assert (or (not thread_4_1) (not exit_4)))
(assert (or (not flush_4_1) (not thread_4_2)))
(assert (or (not flush_4_1) (not flush_4_2)))
(assert (or (not flush_4_1) (not exit_4)))
(assert (or (not thread_4_2) (not flush_4_2)))
(assert (or (not thread_4_2) (not exit_4)))
(assert (or (not flush_4_2) (not exit_4)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_4_0 (=> (or stmt_4_0_1 stmt_4_0_4) (not thread_4_0)) (not flush_4_0)))
(assert (ite sb-full_4_1 (=> (or stmt_4_1_1 stmt_4_1_4) (not thread_4_1)) (not flush_4_1)))
(assert (=> (not sb-full_4_2) (not flush_4_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_4_0_0 (not check_4_0)) (not thread_4_0))) ; checkpoint 0: thread 0
(assert (=> (and block_4_0_1 (not check_4_0)) (not thread_4_1))) ; checkpoint 0: thread 1
(assert (=> (and block_4_0_2 (not check_4_0)) (not thread_4_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_4_0 (not thread_4_0)))
(assert (=> halt_4_1 (not thread_4_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_3_0_0 (and (= accu_4_0 (bvadd accu_3_0 #x0001)) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) stmt_4_0_1 (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4)) (= block_4_0_0 (ite check_3_0 false block_3_0_0)) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_1 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 #x0000) (= sb-val_4_0 accu_3_0) sb-full_4_0 (and (not stmt_4_0_0) (not stmt_4_0_1) stmt_4_0_2 (not stmt_4_0_3) (not stmt_4_0_4)) (= block_4_0_0 (ite check_3_0 false block_3_0_0)) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_2 (and (= accu_4_0 (ite (and sb-full_3_0 (= sb-adr_3_0 #x0001)) sb-val_3_0 (select heap_3 #x0001))) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) stmt_4_0_3 (not stmt_4_0_4)) (= block_4_0_0 (ite check_3_0 false block_3_0_0)) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_3 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) stmt_4_0_4) block_4_0_0 (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_4 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) (not stmt_4_0_3) (not stmt_4_0_4)) (= block_4_0_0 (ite check_3_0 false block_3_0_0)) (and halt_4_0 (ite (and halt_4_1 halt_4_2) (and exit_4 (= exit-code #x0000)) (not exit_4))) (= heap_4 heap_3))))

(assert (=> (not thread_3_0) (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 (ite flush_3_0 false sb-full_3_0)) (and (= stmt_4_0_0 stmt_3_0_0) (= stmt_4_0_1 stmt_3_0_1) (= stmt_4_0_2 stmt_3_0_2) (= stmt_4_0_3 stmt_3_0_3) (= stmt_4_0_4 stmt_3_0_4)) (= block_4_0_0 (ite check_3_0 false block_3_0_0)) (= halt_4_0 halt_3_0))))

(assert (=> flush_3_0 (and (= heap_4 (store heap_3 sb-adr_3_0 sb-val_3_0)) (not exit_4))))

; thread 1
(assert (=> exec_3_1_0 (and (= accu_4_1 (bvadd accu_3_1 #x0001)) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) stmt_4_1_1 (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4)) (= block_4_0_1 (ite check_3_0 false block_3_0_1)) (= halt_4_1 halt_3_1) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_1_1 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 #x0001) (= sb-val_4_1 accu_3_1) sb-full_4_1 (and (not stmt_4_1_0) (not stmt_4_1_1) stmt_4_1_2 (not stmt_4_1_3) (not stmt_4_1_4)) (= block_4_0_1 (ite check_3_0 false block_3_0_1)) (= halt_4_1 halt_3_1) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_1_2 (and (= accu_4_1 (ite (and sb-full_3_1 (= sb-adr_3_1 #x0000)) sb-val_3_1 (select heap_3 #x0000))) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) stmt_4_1_3 (not stmt_4_1_4)) (= block_4_0_1 (ite check_3_0 false block_3_0_1)) (= halt_4_1 halt_3_1) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_1_3 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) stmt_4_1_4) block_4_0_1 (= halt_4_1 halt_3_1) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_1_4 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2) (not stmt_4_1_3) (not stmt_4_1_4)) (= block_4_0_1 (ite check_3_0 false block_3_0_1)) (and halt_4_1 (ite (and halt_4_0 halt_4_2) (and exit_4 (= exit-code #x0000)) (not exit_4))) (= heap_4 heap_3))))

(assert (=> (not thread_3_1) (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 (ite flush_3_1 false sb-full_3_1)) (and (= stmt_4_1_0 stmt_3_1_0) (= stmt_4_1_1 stmt_3_1_1) (= stmt_4_1_2 stmt_3_1_2) (= stmt_4_1_3 stmt_3_1_3) (= stmt_4_1_4 stmt_3_1_4)) (= block_4_0_1 (ite check_3_0 false block_3_0_1)) (= halt_4_1 halt_3_1))))

(assert (=> flush_3_1 (and (= heap_4 (store heap_3 sb-adr_3_1 sb-val_3_1)) (not exit_4))))

; thread 2
(assert (=> exec_3_2_0 (and (= accu_4_2 accu_3_2) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) stmt_4_2_1 (not stmt_4_2_2) (not stmt_4_2_3) (not stmt_4_2_4) (not stmt_4_2_5)) block_4_0_2 (= halt_4_2 halt_3_2) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_2_1 (and (= accu_4_2 (bvadd accu_3_2 (ite (and sb-full_3_2 (= sb-adr_3_2 #x0000)) sb-val_3_2 (select heap_3 #x0000)))) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) (not stmt_4_2_1) stmt_4_2_2 (not stmt_4_2_3) (not stmt_4_2_4) (not stmt_4_2_5)) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_2_2 (and (= accu_4_2 (bvadd accu_3_2 (ite (and sb-full_3_2 (= sb-adr_3_2 #x0001)) sb-val_3_2 (select heap_3 #x0001)))) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) stmt_4_2_3 (not stmt_4_2_4) (not stmt_4_2_5)) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_2_3 (and (= accu_4_2 accu_3_2) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) (not stmt_4_2_3) (ite (= accu_3_2 #x0000) (not stmt_4_2_4) stmt_4_2_4) (ite (= accu_3_2 #x0000) stmt_4_2_5 (not stmt_4_2_5))) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_2_4 (and (= accu_4_2 accu_3_2) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) (not stmt_4_2_3) stmt_4_2_4 (not stmt_4_2_5)) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2) (= heap_4 heap_3) exit_4 (= exit-code #x0000))))

(assert (=> exec_3_2_5 (and (= accu_4_2 accu_3_2) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 sb-full_3_2) (and (not stmt_4_2_0) (not stmt_4_2_1) (not stmt_4_2_2) (not stmt_4_2_3) (not stmt_4_2_4) stmt_4_2_5) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2) (= heap_4 heap_3) exit_4 (= exit-code #x0001))))

(assert (=> (not thread_3_2) (and (= accu_4_2 accu_3_2) (= mem_4_2 mem_3_2) (= sb-adr_4_2 sb-adr_3_2) (= sb-val_4_2 sb-val_3_2) (= sb-full_4_2 (ite flush_3_2 false sb-full_3_2)) (and (= stmt_4_2_0 stmt_3_2_0) (= stmt_4_2_1 stmt_3_2_1) (= stmt_4_2_2 stmt_3_2_2) (= stmt_4_2_3 stmt_3_2_3) (= stmt_4_2_4 stmt_3_2_4) (= stmt_4_2_5 stmt_3_2_5)) (= block_4_0_2 (ite check_3_0 false block_3_0_2)) (= halt_4_2 halt_3_2))))

(assert (=> flush_3_2 (and (= heap_4 (store heap_3 sb-adr_3_2 sb-val_3_2)) (not exit_4))))

; exited
(assert (=> exit_3 (and (= heap_4 heap_3) exit_4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_5_0 () (_ BitVec 16))
(declare-fun accu_5_1 () (_ BitVec 16))
(declare-fun accu_5_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_5_0 () (_ BitVec 16))
(declare-fun mem_5_1 () (_ BitVec 16))
(declare-fun mem_5_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_5_0 () (_ BitVec 16))
(declare-fun sb-adr_5_1 () (_ BitVec 16))
(declare-fun sb-adr_5_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_5_0 () (_ BitVec 16))
(declare-fun sb-val_5_1 () (_ BitVec 16))
(declare-fun sb-val_5_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_5_0 () Bool)
(declare-fun sb-full_5_1 () Bool)
(declare-fun sb-full_5_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_0_0 () Bool)
(declare-fun stmt_5_0_1 () Bool)
(declare-fun stmt_5_0_2 () Bool)
(declare-fun stmt_5_0_3 () Bool)
(declare-fun stmt_5_0_4 () Bool)

(declare-fun stmt_5_1_0 () Bool)
(declare-fun stmt_5_1_1 () Bool)
(declare-fun stmt_5_1_2 () Bool)
(declare-fun stmt_5_1_3 () Bool)
(declare-fun stmt_5_1_4 () Bool)

(declare-fun stmt_5_2_0 () Bool)
(declare-fun stmt_5_2_1 () Bool)
(declare-fun stmt_5_2_2 () Bool)
(declare-fun stmt_5_2_3 () Bool)
(declare-fun stmt_5_2_4 () Bool)
(declare-fun stmt_5_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_5_0_0 () Bool)
(declare-fun block_5_0_1 () Bool)
(declare-fun block_5_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_5_0 () Bool)
(declare-fun halt_5_1 () Bool)
(declare-fun halt_5_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_5 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_0 () Bool)
(declare-fun thread_5_1 () Bool)
(declare-fun thread_5_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_0_0 () Bool)
(declare-fun exec_5_0_1 () Bool)
(declare-fun exec_5_0_2 () Bool)
(declare-fun exec_5_0_3 () Bool)
(declare-fun exec_5_0_4 () Bool)

(declare-fun exec_5_1_0 () Bool)
(declare-fun exec_5_1_1 () Bool)
(declare-fun exec_5_1_2 () Bool)
(declare-fun exec_5_1_3 () Bool)
(declare-fun exec_5_1_4 () Bool)

(declare-fun exec_5_2_0 () Bool)
(declare-fun exec_5_2_1 () Bool)
(declare-fun exec_5_2_2 () Bool)
(declare-fun exec_5_2_3 () Bool)
(declare-fun exec_5_2_4 () Bool)
(declare-fun exec_5_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_5_0 () Bool)
(declare-fun flush_5_1 () Bool)
(declare-fun flush_5_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_5_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_5_0_0 (and stmt_5_0_0 thread_5_0)))
(assert (= exec_5_0_1 (and stmt_5_0_1 thread_5_0)))
(assert (= exec_5_0_2 (and stmt_5_0_2 thread_5_0)))
(assert (= exec_5_0_3 (and stmt_5_0_3 thread_5_0)))
(assert (= exec_5_0_4 (and stmt_5_0_4 thread_5_0)))

(assert (= exec_5_1_0 (and stmt_5_1_0 thread_5_1)))
(assert (= exec_5_1_1 (and stmt_5_1_1 thread_5_1)))
(assert (= exec_5_1_2 (and stmt_5_1_2 thread_5_1)))
(assert (= exec_5_1_3 (and stmt_5_1_3 thread_5_1)))
(assert (= exec_5_1_4 (and stmt_5_1_4 thread_5_1)))

(assert (= exec_5_2_0 (and stmt_5_2_0 thread_5_2)))
(assert (= exec_5_2_1 (and stmt_5_2_1 thread_5_2)))
(assert (= exec_5_2_2 (and stmt_5_2_2 thread_5_2)))
(assert (= exec_5_2_3 (and stmt_5_2_3 thread_5_2)))
(assert (= exec_5_2_4 (and stmt_5_2_4 thread_5_2)))
(assert (= exec_5_2_5 (and stmt_5_2_5 thread_5_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_5_0 (and block_5_0_0 block_5_0_1 block_5_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_5_0 flush_5_0 thread_5_1 flush_5_1 thread_5_2 flush_5_2 exit_5))
(assert (or (not thread_5_0) (not flush_5_0)))
(assert (or (not thread_5_0) (not thread_5_1)))
(assert (or (not thread_5_0) (not flush_5_1)))
(assert (or (not thread_5_0) (not thread_5_2)))
(assert (or (not thread_5_0) (not flush_5_2)))
(assert (or (not thread_5_0) (not exit_5)))
(assert (or (not flush_5_0) (not thread_5_1)))
(assert (or (not flush_5_0) (not flush_5_1)))
(assert (or (not flush_5_0) (not thread_5_2)))
(assert (or (not flush_5_0) (not flush_5_2)))
(assert (or (not flush_5_0) (not exit_5)))
(assert (or (not thread_5_1) (not flush_5_1)))
(assert (or (not thread_5_1) (not thread_5_2)))
(assert (or (not thread_5_1) (not flush_5_2)))
(assert (or (not thread_5_1) (not exit_5)))
(assert (or (not flush_5_1) (not thread_5_2)))
(assert (or (not flush_5_1) (not flush_5_2)))
(assert (or (not flush_5_1) (not exit_5)))
(assert (or (not thread_5_2) (not flush_5_2)))
(assert (or (not thread_5_2) (not exit_5)))
(assert (or (not flush_5_2) (not exit_5)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_5_0 (=> (or stmt_5_0_1 stmt_5_0_4) (not thread_5_0)) (not flush_5_0)))
(assert (ite sb-full_5_1 (=> (or stmt_5_1_1 stmt_5_1_4) (not thread_5_1)) (not flush_5_1)))
(assert (=> (not sb-full_5_2) (not flush_5_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_5_0_0 (not check_5_0)) (not thread_5_0))) ; checkpoint 0: thread 0
(assert (=> (and block_5_0_1 (not check_5_0)) (not thread_5_1))) ; checkpoint 0: thread 1
(assert (=> (and block_5_0_2 (not check_5_0)) (not thread_5_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_5_0 (not thread_5_0)))
(assert (=> halt_5_1 (not thread_5_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_4_0_0 (and (= accu_5_0 (bvadd accu_4_0 #x0001)) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) stmt_5_0_1 (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4)) (= block_5_0_0 (ite check_4_0 false block_4_0_0)) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_1 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 #x0000) (= sb-val_5_0 accu_4_0) sb-full_5_0 (and (not stmt_5_0_0) (not stmt_5_0_1) stmt_5_0_2 (not stmt_5_0_3) (not stmt_5_0_4)) (= block_5_0_0 (ite check_4_0 false block_4_0_0)) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_2 (and (= accu_5_0 (ite (and sb-full_4_0 (= sb-adr_4_0 #x0001)) sb-val_4_0 (select heap_4 #x0001))) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) stmt_5_0_3 (not stmt_5_0_4)) (= block_5_0_0 (ite check_4_0 false block_4_0_0)) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_3 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) stmt_5_0_4) block_5_0_0 (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_4 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) (not stmt_5_0_3) (not stmt_5_0_4)) (= block_5_0_0 (ite check_4_0 false block_4_0_0)) (and halt_5_0 (ite (and halt_5_1 halt_5_2) (and exit_5 (= exit-code #x0000)) (not exit_5))) (= heap_5 heap_4))))

(assert (=> (not thread_4_0) (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 (ite flush_4_0 false sb-full_4_0)) (and (= stmt_5_0_0 stmt_4_0_0) (= stmt_5_0_1 stmt_4_0_1) (= stmt_5_0_2 stmt_4_0_2) (= stmt_5_0_3 stmt_4_0_3) (= stmt_5_0_4 stmt_4_0_4)) (= block_5_0_0 (ite check_4_0 false block_4_0_0)) (= halt_5_0 halt_4_0))))

(assert (=> flush_4_0 (and (= heap_5 (store heap_4 sb-adr_4_0 sb-val_4_0)) (not exit_5))))

; thread 1
(assert (=> exec_4_1_0 (and (= accu_5_1 (bvadd accu_4_1 #x0001)) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) stmt_5_1_1 (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4)) (= block_5_0_1 (ite check_4_0 false block_4_0_1)) (= halt_5_1 halt_4_1) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_1_1 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 #x0001) (= sb-val_5_1 accu_4_1) sb-full_5_1 (and (not stmt_5_1_0) (not stmt_5_1_1) stmt_5_1_2 (not stmt_5_1_3) (not stmt_5_1_4)) (= block_5_0_1 (ite check_4_0 false block_4_0_1)) (= halt_5_1 halt_4_1) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_1_2 (and (= accu_5_1 (ite (and sb-full_4_1 (= sb-adr_4_1 #x0000)) sb-val_4_1 (select heap_4 #x0000))) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) stmt_5_1_3 (not stmt_5_1_4)) (= block_5_0_1 (ite check_4_0 false block_4_0_1)) (= halt_5_1 halt_4_1) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_1_3 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) stmt_5_1_4) block_5_0_1 (= halt_5_1 halt_4_1) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_1_4 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2) (not stmt_5_1_3) (not stmt_5_1_4)) (= block_5_0_1 (ite check_4_0 false block_4_0_1)) (and halt_5_1 (ite (and halt_5_0 halt_5_2) (and exit_5 (= exit-code #x0000)) (not exit_5))) (= heap_5 heap_4))))

(assert (=> (not thread_4_1) (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 (ite flush_4_1 false sb-full_4_1)) (and (= stmt_5_1_0 stmt_4_1_0) (= stmt_5_1_1 stmt_4_1_1) (= stmt_5_1_2 stmt_4_1_2) (= stmt_5_1_3 stmt_4_1_3) (= stmt_5_1_4 stmt_4_1_4)) (= block_5_0_1 (ite check_4_0 false block_4_0_1)) (= halt_5_1 halt_4_1))))

(assert (=> flush_4_1 (and (= heap_5 (store heap_4 sb-adr_4_1 sb-val_4_1)) (not exit_5))))

; thread 2
(assert (=> exec_4_2_0 (and (= accu_5_2 accu_4_2) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) stmt_5_2_1 (not stmt_5_2_2) (not stmt_5_2_3) (not stmt_5_2_4) (not stmt_5_2_5)) block_5_0_2 (= halt_5_2 halt_4_2) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_2_1 (and (= accu_5_2 (bvadd accu_4_2 (ite (and sb-full_4_2 (= sb-adr_4_2 #x0000)) sb-val_4_2 (select heap_4 #x0000)))) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) (not stmt_5_2_1) stmt_5_2_2 (not stmt_5_2_3) (not stmt_5_2_4) (not stmt_5_2_5)) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_2_2 (and (= accu_5_2 (bvadd accu_4_2 (ite (and sb-full_4_2 (= sb-adr_4_2 #x0001)) sb-val_4_2 (select heap_4 #x0001)))) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) stmt_5_2_3 (not stmt_5_2_4) (not stmt_5_2_5)) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_2_3 (and (= accu_5_2 accu_4_2) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) (not stmt_5_2_3) (ite (= accu_4_2 #x0000) (not stmt_5_2_4) stmt_5_2_4) (ite (= accu_4_2 #x0000) stmt_5_2_5 (not stmt_5_2_5))) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_2_4 (and (= accu_5_2 accu_4_2) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) (not stmt_5_2_3) stmt_5_2_4 (not stmt_5_2_5)) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2) (= heap_5 heap_4) exit_5 (= exit-code #x0000))))

(assert (=> exec_4_2_5 (and (= accu_5_2 accu_4_2) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 sb-full_4_2) (and (not stmt_5_2_0) (not stmt_5_2_1) (not stmt_5_2_2) (not stmt_5_2_3) (not stmt_5_2_4) stmt_5_2_5) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2) (= heap_5 heap_4) exit_5 (= exit-code #x0001))))

(assert (=> (not thread_4_2) (and (= accu_5_2 accu_4_2) (= mem_5_2 mem_4_2) (= sb-adr_5_2 sb-adr_4_2) (= sb-val_5_2 sb-val_4_2) (= sb-full_5_2 (ite flush_4_2 false sb-full_4_2)) (and (= stmt_5_2_0 stmt_4_2_0) (= stmt_5_2_1 stmt_4_2_1) (= stmt_5_2_2 stmt_4_2_2) (= stmt_5_2_3 stmt_4_2_3) (= stmt_5_2_4 stmt_4_2_4) (= stmt_5_2_5 stmt_4_2_5)) (= block_5_0_2 (ite check_4_0 false block_4_0_2)) (= halt_5_2 halt_4_2))))

(assert (=> flush_4_2 (and (= heap_5 (store heap_4 sb-adr_4_2 sb-val_4_2)) (not exit_5))))

; exited
(assert (=> exit_4 (and (= heap_5 heap_4) exit_5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_6_0 () (_ BitVec 16))
(declare-fun accu_6_1 () (_ BitVec 16))
(declare-fun accu_6_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_6_0 () (_ BitVec 16))
(declare-fun mem_6_1 () (_ BitVec 16))
(declare-fun mem_6_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_6_0 () (_ BitVec 16))
(declare-fun sb-adr_6_1 () (_ BitVec 16))
(declare-fun sb-adr_6_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_6_0 () (_ BitVec 16))
(declare-fun sb-val_6_1 () (_ BitVec 16))
(declare-fun sb-val_6_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_6_0 () Bool)
(declare-fun sb-full_6_1 () Bool)
(declare-fun sb-full_6_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_0_0 () Bool)
(declare-fun stmt_6_0_1 () Bool)
(declare-fun stmt_6_0_2 () Bool)
(declare-fun stmt_6_0_3 () Bool)
(declare-fun stmt_6_0_4 () Bool)

(declare-fun stmt_6_1_0 () Bool)
(declare-fun stmt_6_1_1 () Bool)
(declare-fun stmt_6_1_2 () Bool)
(declare-fun stmt_6_1_3 () Bool)
(declare-fun stmt_6_1_4 () Bool)

(declare-fun stmt_6_2_0 () Bool)
(declare-fun stmt_6_2_1 () Bool)
(declare-fun stmt_6_2_2 () Bool)
(declare-fun stmt_6_2_3 () Bool)
(declare-fun stmt_6_2_4 () Bool)
(declare-fun stmt_6_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_6_0_0 () Bool)
(declare-fun block_6_0_1 () Bool)
(declare-fun block_6_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_6_0 () Bool)
(declare-fun halt_6_1 () Bool)
(declare-fun halt_6_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_6 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_0 () Bool)
(declare-fun thread_6_1 () Bool)
(declare-fun thread_6_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_0_0 () Bool)
(declare-fun exec_6_0_1 () Bool)
(declare-fun exec_6_0_2 () Bool)
(declare-fun exec_6_0_3 () Bool)
(declare-fun exec_6_0_4 () Bool)

(declare-fun exec_6_1_0 () Bool)
(declare-fun exec_6_1_1 () Bool)
(declare-fun exec_6_1_2 () Bool)
(declare-fun exec_6_1_3 () Bool)
(declare-fun exec_6_1_4 () Bool)

(declare-fun exec_6_2_0 () Bool)
(declare-fun exec_6_2_1 () Bool)
(declare-fun exec_6_2_2 () Bool)
(declare-fun exec_6_2_3 () Bool)
(declare-fun exec_6_2_4 () Bool)
(declare-fun exec_6_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_6_0 () Bool)
(declare-fun flush_6_1 () Bool)
(declare-fun flush_6_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_6_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_6_0_0 (and stmt_6_0_0 thread_6_0)))
(assert (= exec_6_0_1 (and stmt_6_0_1 thread_6_0)))
(assert (= exec_6_0_2 (and stmt_6_0_2 thread_6_0)))
(assert (= exec_6_0_3 (and stmt_6_0_3 thread_6_0)))
(assert (= exec_6_0_4 (and stmt_6_0_4 thread_6_0)))

(assert (= exec_6_1_0 (and stmt_6_1_0 thread_6_1)))
(assert (= exec_6_1_1 (and stmt_6_1_1 thread_6_1)))
(assert (= exec_6_1_2 (and stmt_6_1_2 thread_6_1)))
(assert (= exec_6_1_3 (and stmt_6_1_3 thread_6_1)))
(assert (= exec_6_1_4 (and stmt_6_1_4 thread_6_1)))

(assert (= exec_6_2_0 (and stmt_6_2_0 thread_6_2)))
(assert (= exec_6_2_1 (and stmt_6_2_1 thread_6_2)))
(assert (= exec_6_2_2 (and stmt_6_2_2 thread_6_2)))
(assert (= exec_6_2_3 (and stmt_6_2_3 thread_6_2)))
(assert (= exec_6_2_4 (and stmt_6_2_4 thread_6_2)))
(assert (= exec_6_2_5 (and stmt_6_2_5 thread_6_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_6_0 (and block_6_0_0 block_6_0_1 block_6_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_6_0 flush_6_0 thread_6_1 flush_6_1 thread_6_2 flush_6_2 exit_6))
(assert (or (not thread_6_0) (not flush_6_0)))
(assert (or (not thread_6_0) (not thread_6_1)))
(assert (or (not thread_6_0) (not flush_6_1)))
(assert (or (not thread_6_0) (not thread_6_2)))
(assert (or (not thread_6_0) (not flush_6_2)))
(assert (or (not thread_6_0) (not exit_6)))
(assert (or (not flush_6_0) (not thread_6_1)))
(assert (or (not flush_6_0) (not flush_6_1)))
(assert (or (not flush_6_0) (not thread_6_2)))
(assert (or (not flush_6_0) (not flush_6_2)))
(assert (or (not flush_6_0) (not exit_6)))
(assert (or (not thread_6_1) (not flush_6_1)))
(assert (or (not thread_6_1) (not thread_6_2)))
(assert (or (not thread_6_1) (not flush_6_2)))
(assert (or (not thread_6_1) (not exit_6)))
(assert (or (not flush_6_1) (not thread_6_2)))
(assert (or (not flush_6_1) (not flush_6_2)))
(assert (or (not flush_6_1) (not exit_6)))
(assert (or (not thread_6_2) (not flush_6_2)))
(assert (or (not thread_6_2) (not exit_6)))
(assert (or (not flush_6_2) (not exit_6)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_6_0 (=> (or stmt_6_0_1 stmt_6_0_4) (not thread_6_0)) (not flush_6_0)))
(assert (ite sb-full_6_1 (=> (or stmt_6_1_1 stmt_6_1_4) (not thread_6_1)) (not flush_6_1)))
(assert (=> (not sb-full_6_2) (not flush_6_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_6_0_0 (not check_6_0)) (not thread_6_0))) ; checkpoint 0: thread 0
(assert (=> (and block_6_0_1 (not check_6_0)) (not thread_6_1))) ; checkpoint 0: thread 1
(assert (=> (and block_6_0_2 (not check_6_0)) (not thread_6_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_6_0 (not thread_6_0)))
(assert (=> halt_6_1 (not thread_6_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_5_0_0 (and (= accu_6_0 (bvadd accu_5_0 #x0001)) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) stmt_6_0_1 (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4)) (= block_6_0_0 (ite check_5_0 false block_5_0_0)) (= halt_6_0 halt_5_0) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_0_1 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 #x0000) (= sb-val_6_0 accu_5_0) sb-full_6_0 (and (not stmt_6_0_0) (not stmt_6_0_1) stmt_6_0_2 (not stmt_6_0_3) (not stmt_6_0_4)) (= block_6_0_0 (ite check_5_0 false block_5_0_0)) (= halt_6_0 halt_5_0) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_0_2 (and (= accu_6_0 (ite (and sb-full_5_0 (= sb-adr_5_0 #x0001)) sb-val_5_0 (select heap_5 #x0001))) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) stmt_6_0_3 (not stmt_6_0_4)) (= block_6_0_0 (ite check_5_0 false block_5_0_0)) (= halt_6_0 halt_5_0) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_0_3 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) stmt_6_0_4) block_6_0_0 (= halt_6_0 halt_5_0) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_0_4 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2) (not stmt_6_0_3) (not stmt_6_0_4)) (= block_6_0_0 (ite check_5_0 false block_5_0_0)) (and halt_6_0 (ite (and halt_6_1 halt_6_2) (and exit_6 (= exit-code #x0000)) (not exit_6))) (= heap_6 heap_5))))

(assert (=> (not thread_5_0) (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 (ite flush_5_0 false sb-full_5_0)) (and (= stmt_6_0_0 stmt_5_0_0) (= stmt_6_0_1 stmt_5_0_1) (= stmt_6_0_2 stmt_5_0_2) (= stmt_6_0_3 stmt_5_0_3) (= stmt_6_0_4 stmt_5_0_4)) (= block_6_0_0 (ite check_5_0 false block_5_0_0)) (= halt_6_0 halt_5_0))))

(assert (=> flush_5_0 (and (= heap_6 (store heap_5 sb-adr_5_0 sb-val_5_0)) (not exit_6))))

; thread 1
(assert (=> exec_5_1_0 (and (= accu_6_1 (bvadd accu_5_1 #x0001)) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) stmt_6_1_1 (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4)) (= block_6_0_1 (ite check_5_0 false block_5_0_1)) (= halt_6_1 halt_5_1) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_1_1 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 #x0001) (= sb-val_6_1 accu_5_1) sb-full_6_1 (and (not stmt_6_1_0) (not stmt_6_1_1) stmt_6_1_2 (not stmt_6_1_3) (not stmt_6_1_4)) (= block_6_0_1 (ite check_5_0 false block_5_0_1)) (= halt_6_1 halt_5_1) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_1_2 (and (= accu_6_1 (ite (and sb-full_5_1 (= sb-adr_5_1 #x0000)) sb-val_5_1 (select heap_5 #x0000))) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) stmt_6_1_3 (not stmt_6_1_4)) (= block_6_0_1 (ite check_5_0 false block_5_0_1)) (= halt_6_1 halt_5_1) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_1_3 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) stmt_6_1_4) block_6_0_1 (= halt_6_1 halt_5_1) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_1_4 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2) (not stmt_6_1_3) (not stmt_6_1_4)) (= block_6_0_1 (ite check_5_0 false block_5_0_1)) (and halt_6_1 (ite (and halt_6_0 halt_6_2) (and exit_6 (= exit-code #x0000)) (not exit_6))) (= heap_6 heap_5))))

(assert (=> (not thread_5_1) (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 (ite flush_5_1 false sb-full_5_1)) (and (= stmt_6_1_0 stmt_5_1_0) (= stmt_6_1_1 stmt_5_1_1) (= stmt_6_1_2 stmt_5_1_2) (= stmt_6_1_3 stmt_5_1_3) (= stmt_6_1_4 stmt_5_1_4)) (= block_6_0_1 (ite check_5_0 false block_5_0_1)) (= halt_6_1 halt_5_1))))

(assert (=> flush_5_1 (and (= heap_6 (store heap_5 sb-adr_5_1 sb-val_5_1)) (not exit_6))))

; thread 2
(assert (=> exec_5_2_0 (and (= accu_6_2 accu_5_2) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) stmt_6_2_1 (not stmt_6_2_2) (not stmt_6_2_3) (not stmt_6_2_4) (not stmt_6_2_5)) block_6_0_2 (= halt_6_2 halt_5_2) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_2_1 (and (= accu_6_2 (bvadd accu_5_2 (ite (and sb-full_5_2 (= sb-adr_5_2 #x0000)) sb-val_5_2 (select heap_5 #x0000)))) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) (not stmt_6_2_1) stmt_6_2_2 (not stmt_6_2_3) (not stmt_6_2_4) (not stmt_6_2_5)) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_2_2 (and (= accu_6_2 (bvadd accu_5_2 (ite (and sb-full_5_2 (= sb-adr_5_2 #x0001)) sb-val_5_2 (select heap_5 #x0001)))) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) stmt_6_2_3 (not stmt_6_2_4) (not stmt_6_2_5)) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_2_3 (and (= accu_6_2 accu_5_2) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) (not stmt_6_2_3) (ite (= accu_5_2 #x0000) (not stmt_6_2_4) stmt_6_2_4) (ite (= accu_5_2 #x0000) stmt_6_2_5 (not stmt_6_2_5))) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_2_4 (and (= accu_6_2 accu_5_2) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) (not stmt_6_2_3) stmt_6_2_4 (not stmt_6_2_5)) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2) (= heap_6 heap_5) exit_6 (= exit-code #x0000))))

(assert (=> exec_5_2_5 (and (= accu_6_2 accu_5_2) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 sb-full_5_2) (and (not stmt_6_2_0) (not stmt_6_2_1) (not stmt_6_2_2) (not stmt_6_2_3) (not stmt_6_2_4) stmt_6_2_5) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2) (= heap_6 heap_5) exit_6 (= exit-code #x0001))))

(assert (=> (not thread_5_2) (and (= accu_6_2 accu_5_2) (= mem_6_2 mem_5_2) (= sb-adr_6_2 sb-adr_5_2) (= sb-val_6_2 sb-val_5_2) (= sb-full_6_2 (ite flush_5_2 false sb-full_5_2)) (and (= stmt_6_2_0 stmt_5_2_0) (= stmt_6_2_1 stmt_5_2_1) (= stmt_6_2_2 stmt_5_2_2) (= stmt_6_2_3 stmt_5_2_3) (= stmt_6_2_4 stmt_5_2_4) (= stmt_6_2_5 stmt_5_2_5)) (= block_6_0_2 (ite check_5_0 false block_5_0_2)) (= halt_6_2 halt_5_2))))

(assert (=> flush_5_2 (and (= heap_6 (store heap_5 sb-adr_5_2 sb-val_5_2)) (not exit_6))))

; exited
(assert (=> exit_5 (and (= heap_6 heap_5) exit_6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_7_0 () (_ BitVec 16))
(declare-fun accu_7_1 () (_ BitVec 16))
(declare-fun accu_7_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_7_0 () (_ BitVec 16))
(declare-fun mem_7_1 () (_ BitVec 16))
(declare-fun mem_7_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_7_0 () (_ BitVec 16))
(declare-fun sb-adr_7_1 () (_ BitVec 16))
(declare-fun sb-adr_7_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_7_0 () (_ BitVec 16))
(declare-fun sb-val_7_1 () (_ BitVec 16))
(declare-fun sb-val_7_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_7_0 () Bool)
(declare-fun sb-full_7_1 () Bool)
(declare-fun sb-full_7_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_0_0 () Bool)
(declare-fun stmt_7_0_1 () Bool)
(declare-fun stmt_7_0_2 () Bool)
(declare-fun stmt_7_0_3 () Bool)
(declare-fun stmt_7_0_4 () Bool)

(declare-fun stmt_7_1_0 () Bool)
(declare-fun stmt_7_1_1 () Bool)
(declare-fun stmt_7_1_2 () Bool)
(declare-fun stmt_7_1_3 () Bool)
(declare-fun stmt_7_1_4 () Bool)

(declare-fun stmt_7_2_0 () Bool)
(declare-fun stmt_7_2_1 () Bool)
(declare-fun stmt_7_2_2 () Bool)
(declare-fun stmt_7_2_3 () Bool)
(declare-fun stmt_7_2_4 () Bool)
(declare-fun stmt_7_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_7_0_0 () Bool)
(declare-fun block_7_0_1 () Bool)
(declare-fun block_7_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_7_0 () Bool)
(declare-fun halt_7_1 () Bool)
(declare-fun halt_7_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_7 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_0 () Bool)
(declare-fun thread_7_1 () Bool)
(declare-fun thread_7_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_0_0 () Bool)
(declare-fun exec_7_0_1 () Bool)
(declare-fun exec_7_0_2 () Bool)
(declare-fun exec_7_0_3 () Bool)
(declare-fun exec_7_0_4 () Bool)

(declare-fun exec_7_1_0 () Bool)
(declare-fun exec_7_1_1 () Bool)
(declare-fun exec_7_1_2 () Bool)
(declare-fun exec_7_1_3 () Bool)
(declare-fun exec_7_1_4 () Bool)

(declare-fun exec_7_2_0 () Bool)
(declare-fun exec_7_2_1 () Bool)
(declare-fun exec_7_2_2 () Bool)
(declare-fun exec_7_2_3 () Bool)
(declare-fun exec_7_2_4 () Bool)
(declare-fun exec_7_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_7_0 () Bool)
(declare-fun flush_7_1 () Bool)
(declare-fun flush_7_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_7_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_7_0_0 (and stmt_7_0_0 thread_7_0)))
(assert (= exec_7_0_1 (and stmt_7_0_1 thread_7_0)))
(assert (= exec_7_0_2 (and stmt_7_0_2 thread_7_0)))
(assert (= exec_7_0_3 (and stmt_7_0_3 thread_7_0)))
(assert (= exec_7_0_4 (and stmt_7_0_4 thread_7_0)))

(assert (= exec_7_1_0 (and stmt_7_1_0 thread_7_1)))
(assert (= exec_7_1_1 (and stmt_7_1_1 thread_7_1)))
(assert (= exec_7_1_2 (and stmt_7_1_2 thread_7_1)))
(assert (= exec_7_1_3 (and stmt_7_1_3 thread_7_1)))
(assert (= exec_7_1_4 (and stmt_7_1_4 thread_7_1)))

(assert (= exec_7_2_0 (and stmt_7_2_0 thread_7_2)))
(assert (= exec_7_2_1 (and stmt_7_2_1 thread_7_2)))
(assert (= exec_7_2_2 (and stmt_7_2_2 thread_7_2)))
(assert (= exec_7_2_3 (and stmt_7_2_3 thread_7_2)))
(assert (= exec_7_2_4 (and stmt_7_2_4 thread_7_2)))
(assert (= exec_7_2_5 (and stmt_7_2_5 thread_7_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_7_0 (and block_7_0_0 block_7_0_1 block_7_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_7_0 flush_7_0 thread_7_1 flush_7_1 thread_7_2 flush_7_2 exit_7))
(assert (or (not thread_7_0) (not flush_7_0)))
(assert (or (not thread_7_0) (not thread_7_1)))
(assert (or (not thread_7_0) (not flush_7_1)))
(assert (or (not thread_7_0) (not thread_7_2)))
(assert (or (not thread_7_0) (not flush_7_2)))
(assert (or (not thread_7_0) (not exit_7)))
(assert (or (not flush_7_0) (not thread_7_1)))
(assert (or (not flush_7_0) (not flush_7_1)))
(assert (or (not flush_7_0) (not thread_7_2)))
(assert (or (not flush_7_0) (not flush_7_2)))
(assert (or (not flush_7_0) (not exit_7)))
(assert (or (not thread_7_1) (not flush_7_1)))
(assert (or (not thread_7_1) (not thread_7_2)))
(assert (or (not thread_7_1) (not flush_7_2)))
(assert (or (not thread_7_1) (not exit_7)))
(assert (or (not flush_7_1) (not thread_7_2)))
(assert (or (not flush_7_1) (not flush_7_2)))
(assert (or (not flush_7_1) (not exit_7)))
(assert (or (not thread_7_2) (not flush_7_2)))
(assert (or (not thread_7_2) (not exit_7)))
(assert (or (not flush_7_2) (not exit_7)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_7_0 (=> (or stmt_7_0_1 stmt_7_0_4) (not thread_7_0)) (not flush_7_0)))
(assert (ite sb-full_7_1 (=> (or stmt_7_1_1 stmt_7_1_4) (not thread_7_1)) (not flush_7_1)))
(assert (=> (not sb-full_7_2) (not flush_7_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_7_0_0 (not check_7_0)) (not thread_7_0))) ; checkpoint 0: thread 0
(assert (=> (and block_7_0_1 (not check_7_0)) (not thread_7_1))) ; checkpoint 0: thread 1
(assert (=> (and block_7_0_2 (not check_7_0)) (not thread_7_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_7_0 (not thread_7_0)))
(assert (=> halt_7_1 (not thread_7_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_6_0_0 (and (= accu_7_0 (bvadd accu_6_0 #x0001)) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) stmt_7_0_1 (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4)) (= block_7_0_0 (ite check_6_0 false block_6_0_0)) (= halt_7_0 halt_6_0) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_0_1 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 #x0000) (= sb-val_7_0 accu_6_0) sb-full_7_0 (and (not stmt_7_0_0) (not stmt_7_0_1) stmt_7_0_2 (not stmt_7_0_3) (not stmt_7_0_4)) (= block_7_0_0 (ite check_6_0 false block_6_0_0)) (= halt_7_0 halt_6_0) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_0_2 (and (= accu_7_0 (ite (and sb-full_6_0 (= sb-adr_6_0 #x0001)) sb-val_6_0 (select heap_6 #x0001))) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) stmt_7_0_3 (not stmt_7_0_4)) (= block_7_0_0 (ite check_6_0 false block_6_0_0)) (= halt_7_0 halt_6_0) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_0_3 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) stmt_7_0_4) block_7_0_0 (= halt_7_0 halt_6_0) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_0_4 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2) (not stmt_7_0_3) (not stmt_7_0_4)) (= block_7_0_0 (ite check_6_0 false block_6_0_0)) (and halt_7_0 (ite (and halt_7_1 halt_7_2) (and exit_7 (= exit-code #x0000)) (not exit_7))) (= heap_7 heap_6))))

(assert (=> (not thread_6_0) (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 (ite flush_6_0 false sb-full_6_0)) (and (= stmt_7_0_0 stmt_6_0_0) (= stmt_7_0_1 stmt_6_0_1) (= stmt_7_0_2 stmt_6_0_2) (= stmt_7_0_3 stmt_6_0_3) (= stmt_7_0_4 stmt_6_0_4)) (= block_7_0_0 (ite check_6_0 false block_6_0_0)) (= halt_7_0 halt_6_0))))

(assert (=> flush_6_0 (and (= heap_7 (store heap_6 sb-adr_6_0 sb-val_6_0)) (not exit_7))))

; thread 1
(assert (=> exec_6_1_0 (and (= accu_7_1 (bvadd accu_6_1 #x0001)) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) stmt_7_1_1 (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4)) (= block_7_0_1 (ite check_6_0 false block_6_0_1)) (= halt_7_1 halt_6_1) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_1_1 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 #x0001) (= sb-val_7_1 accu_6_1) sb-full_7_1 (and (not stmt_7_1_0) (not stmt_7_1_1) stmt_7_1_2 (not stmt_7_1_3) (not stmt_7_1_4)) (= block_7_0_1 (ite check_6_0 false block_6_0_1)) (= halt_7_1 halt_6_1) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_1_2 (and (= accu_7_1 (ite (and sb-full_6_1 (= sb-adr_6_1 #x0000)) sb-val_6_1 (select heap_6 #x0000))) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) stmt_7_1_3 (not stmt_7_1_4)) (= block_7_0_1 (ite check_6_0 false block_6_0_1)) (= halt_7_1 halt_6_1) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_1_3 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) stmt_7_1_4) block_7_0_1 (= halt_7_1 halt_6_1) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_1_4 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2) (not stmt_7_1_3) (not stmt_7_1_4)) (= block_7_0_1 (ite check_6_0 false block_6_0_1)) (and halt_7_1 (ite (and halt_7_0 halt_7_2) (and exit_7 (= exit-code #x0000)) (not exit_7))) (= heap_7 heap_6))))

(assert (=> (not thread_6_1) (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 (ite flush_6_1 false sb-full_6_1)) (and (= stmt_7_1_0 stmt_6_1_0) (= stmt_7_1_1 stmt_6_1_1) (= stmt_7_1_2 stmt_6_1_2) (= stmt_7_1_3 stmt_6_1_3) (= stmt_7_1_4 stmt_6_1_4)) (= block_7_0_1 (ite check_6_0 false block_6_0_1)) (= halt_7_1 halt_6_1))))

(assert (=> flush_6_1 (and (= heap_7 (store heap_6 sb-adr_6_1 sb-val_6_1)) (not exit_7))))

; thread 2
(assert (=> exec_6_2_0 (and (= accu_7_2 accu_6_2) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) stmt_7_2_1 (not stmt_7_2_2) (not stmt_7_2_3) (not stmt_7_2_4) (not stmt_7_2_5)) block_7_0_2 (= halt_7_2 halt_6_2) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_2_1 (and (= accu_7_2 (bvadd accu_6_2 (ite (and sb-full_6_2 (= sb-adr_6_2 #x0000)) sb-val_6_2 (select heap_6 #x0000)))) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) (not stmt_7_2_1) stmt_7_2_2 (not stmt_7_2_3) (not stmt_7_2_4) (not stmt_7_2_5)) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_2_2 (and (= accu_7_2 (bvadd accu_6_2 (ite (and sb-full_6_2 (= sb-adr_6_2 #x0001)) sb-val_6_2 (select heap_6 #x0001)))) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) stmt_7_2_3 (not stmt_7_2_4) (not stmt_7_2_5)) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_2_3 (and (= accu_7_2 accu_6_2) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) (not stmt_7_2_3) (ite (= accu_6_2 #x0000) (not stmt_7_2_4) stmt_7_2_4) (ite (= accu_6_2 #x0000) stmt_7_2_5 (not stmt_7_2_5))) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_2_4 (and (= accu_7_2 accu_6_2) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) (not stmt_7_2_3) stmt_7_2_4 (not stmt_7_2_5)) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2) (= heap_7 heap_6) exit_7 (= exit-code #x0000))))

(assert (=> exec_6_2_5 (and (= accu_7_2 accu_6_2) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 sb-full_6_2) (and (not stmt_7_2_0) (not stmt_7_2_1) (not stmt_7_2_2) (not stmt_7_2_3) (not stmt_7_2_4) stmt_7_2_5) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2) (= heap_7 heap_6) exit_7 (= exit-code #x0001))))

(assert (=> (not thread_6_2) (and (= accu_7_2 accu_6_2) (= mem_7_2 mem_6_2) (= sb-adr_7_2 sb-adr_6_2) (= sb-val_7_2 sb-val_6_2) (= sb-full_7_2 (ite flush_6_2 false sb-full_6_2)) (and (= stmt_7_2_0 stmt_6_2_0) (= stmt_7_2_1 stmt_6_2_1) (= stmt_7_2_2 stmt_6_2_2) (= stmt_7_2_3 stmt_6_2_3) (= stmt_7_2_4 stmt_6_2_4) (= stmt_7_2_5 stmt_6_2_5)) (= block_7_0_2 (ite check_6_0 false block_6_0_2)) (= halt_7_2 halt_6_2))))

(assert (=> flush_6_2 (and (= heap_7 (store heap_6 sb-adr_6_2 sb-val_6_2)) (not exit_7))))

; exited
(assert (=> exit_6 (and (= heap_7 heap_6) exit_7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_8_0 () (_ BitVec 16))
(declare-fun accu_8_1 () (_ BitVec 16))
(declare-fun accu_8_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_8_0 () (_ BitVec 16))
(declare-fun mem_8_1 () (_ BitVec 16))
(declare-fun mem_8_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_8_0 () (_ BitVec 16))
(declare-fun sb-adr_8_1 () (_ BitVec 16))
(declare-fun sb-adr_8_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_8_0 () (_ BitVec 16))
(declare-fun sb-val_8_1 () (_ BitVec 16))
(declare-fun sb-val_8_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_8_0 () Bool)
(declare-fun sb-full_8_1 () Bool)
(declare-fun sb-full_8_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_0_0 () Bool)
(declare-fun stmt_8_0_1 () Bool)
(declare-fun stmt_8_0_2 () Bool)
(declare-fun stmt_8_0_3 () Bool)
(declare-fun stmt_8_0_4 () Bool)

(declare-fun stmt_8_1_0 () Bool)
(declare-fun stmt_8_1_1 () Bool)
(declare-fun stmt_8_1_2 () Bool)
(declare-fun stmt_8_1_3 () Bool)
(declare-fun stmt_8_1_4 () Bool)

(declare-fun stmt_8_2_0 () Bool)
(declare-fun stmt_8_2_1 () Bool)
(declare-fun stmt_8_2_2 () Bool)
(declare-fun stmt_8_2_3 () Bool)
(declare-fun stmt_8_2_4 () Bool)
(declare-fun stmt_8_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_8_0_0 () Bool)
(declare-fun block_8_0_1 () Bool)
(declare-fun block_8_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_8_0 () Bool)
(declare-fun halt_8_1 () Bool)
(declare-fun halt_8_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_8 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_0 () Bool)
(declare-fun thread_8_1 () Bool)
(declare-fun thread_8_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_0_0 () Bool)
(declare-fun exec_8_0_1 () Bool)
(declare-fun exec_8_0_2 () Bool)
(declare-fun exec_8_0_3 () Bool)
(declare-fun exec_8_0_4 () Bool)

(declare-fun exec_8_1_0 () Bool)
(declare-fun exec_8_1_1 () Bool)
(declare-fun exec_8_1_2 () Bool)
(declare-fun exec_8_1_3 () Bool)
(declare-fun exec_8_1_4 () Bool)

(declare-fun exec_8_2_0 () Bool)
(declare-fun exec_8_2_1 () Bool)
(declare-fun exec_8_2_2 () Bool)
(declare-fun exec_8_2_3 () Bool)
(declare-fun exec_8_2_4 () Bool)
(declare-fun exec_8_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_8_0 () Bool)
(declare-fun flush_8_1 () Bool)
(declare-fun flush_8_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_8_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_8_0_0 (and stmt_8_0_0 thread_8_0)))
(assert (= exec_8_0_1 (and stmt_8_0_1 thread_8_0)))
(assert (= exec_8_0_2 (and stmt_8_0_2 thread_8_0)))
(assert (= exec_8_0_3 (and stmt_8_0_3 thread_8_0)))
(assert (= exec_8_0_4 (and stmt_8_0_4 thread_8_0)))

(assert (= exec_8_1_0 (and stmt_8_1_0 thread_8_1)))
(assert (= exec_8_1_1 (and stmt_8_1_1 thread_8_1)))
(assert (= exec_8_1_2 (and stmt_8_1_2 thread_8_1)))
(assert (= exec_8_1_3 (and stmt_8_1_3 thread_8_1)))
(assert (= exec_8_1_4 (and stmt_8_1_4 thread_8_1)))

(assert (= exec_8_2_0 (and stmt_8_2_0 thread_8_2)))
(assert (= exec_8_2_1 (and stmt_8_2_1 thread_8_2)))
(assert (= exec_8_2_2 (and stmt_8_2_2 thread_8_2)))
(assert (= exec_8_2_3 (and stmt_8_2_3 thread_8_2)))
(assert (= exec_8_2_4 (and stmt_8_2_4 thread_8_2)))
(assert (= exec_8_2_5 (and stmt_8_2_5 thread_8_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_8_0 (and block_8_0_0 block_8_0_1 block_8_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_8_0 flush_8_0 thread_8_1 flush_8_1 thread_8_2 flush_8_2 exit_8))
(assert (or (not thread_8_0) (not flush_8_0)))
(assert (or (not thread_8_0) (not thread_8_1)))
(assert (or (not thread_8_0) (not flush_8_1)))
(assert (or (not thread_8_0) (not thread_8_2)))
(assert (or (not thread_8_0) (not flush_8_2)))
(assert (or (not thread_8_0) (not exit_8)))
(assert (or (not flush_8_0) (not thread_8_1)))
(assert (or (not flush_8_0) (not flush_8_1)))
(assert (or (not flush_8_0) (not thread_8_2)))
(assert (or (not flush_8_0) (not flush_8_2)))
(assert (or (not flush_8_0) (not exit_8)))
(assert (or (not thread_8_1) (not flush_8_1)))
(assert (or (not thread_8_1) (not thread_8_2)))
(assert (or (not thread_8_1) (not flush_8_2)))
(assert (or (not thread_8_1) (not exit_8)))
(assert (or (not flush_8_1) (not thread_8_2)))
(assert (or (not flush_8_1) (not flush_8_2)))
(assert (or (not flush_8_1) (not exit_8)))
(assert (or (not thread_8_2) (not flush_8_2)))
(assert (or (not thread_8_2) (not exit_8)))
(assert (or (not flush_8_2) (not exit_8)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_8_0 (=> (or stmt_8_0_1 stmt_8_0_4) (not thread_8_0)) (not flush_8_0)))
(assert (ite sb-full_8_1 (=> (or stmt_8_1_1 stmt_8_1_4) (not thread_8_1)) (not flush_8_1)))
(assert (=> (not sb-full_8_2) (not flush_8_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_8_0_0 (not check_8_0)) (not thread_8_0))) ; checkpoint 0: thread 0
(assert (=> (and block_8_0_1 (not check_8_0)) (not thread_8_1))) ; checkpoint 0: thread 1
(assert (=> (and block_8_0_2 (not check_8_0)) (not thread_8_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_8_0 (not thread_8_0)))
(assert (=> halt_8_1 (not thread_8_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_7_0_0 (and (= accu_8_0 (bvadd accu_7_0 #x0001)) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) stmt_8_0_1 (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4)) (= block_8_0_0 (ite check_7_0 false block_7_0_0)) (= halt_8_0 halt_7_0) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_0_1 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 #x0000) (= sb-val_8_0 accu_7_0) sb-full_8_0 (and (not stmt_8_0_0) (not stmt_8_0_1) stmt_8_0_2 (not stmt_8_0_3) (not stmt_8_0_4)) (= block_8_0_0 (ite check_7_0 false block_7_0_0)) (= halt_8_0 halt_7_0) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_0_2 (and (= accu_8_0 (ite (and sb-full_7_0 (= sb-adr_7_0 #x0001)) sb-val_7_0 (select heap_7 #x0001))) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) stmt_8_0_3 (not stmt_8_0_4)) (= block_8_0_0 (ite check_7_0 false block_7_0_0)) (= halt_8_0 halt_7_0) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_0_3 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) stmt_8_0_4) block_8_0_0 (= halt_8_0 halt_7_0) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_0_4 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2) (not stmt_8_0_3) (not stmt_8_0_4)) (= block_8_0_0 (ite check_7_0 false block_7_0_0)) (and halt_8_0 (ite (and halt_8_1 halt_8_2) (and exit_8 (= exit-code #x0000)) (not exit_8))) (= heap_8 heap_7))))

(assert (=> (not thread_7_0) (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 (ite flush_7_0 false sb-full_7_0)) (and (= stmt_8_0_0 stmt_7_0_0) (= stmt_8_0_1 stmt_7_0_1) (= stmt_8_0_2 stmt_7_0_2) (= stmt_8_0_3 stmt_7_0_3) (= stmt_8_0_4 stmt_7_0_4)) (= block_8_0_0 (ite check_7_0 false block_7_0_0)) (= halt_8_0 halt_7_0))))

(assert (=> flush_7_0 (and (= heap_8 (store heap_7 sb-adr_7_0 sb-val_7_0)) (not exit_8))))

; thread 1
(assert (=> exec_7_1_0 (and (= accu_8_1 (bvadd accu_7_1 #x0001)) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) stmt_8_1_1 (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4)) (= block_8_0_1 (ite check_7_0 false block_7_0_1)) (= halt_8_1 halt_7_1) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_1_1 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 #x0001) (= sb-val_8_1 accu_7_1) sb-full_8_1 (and (not stmt_8_1_0) (not stmt_8_1_1) stmt_8_1_2 (not stmt_8_1_3) (not stmt_8_1_4)) (= block_8_0_1 (ite check_7_0 false block_7_0_1)) (= halt_8_1 halt_7_1) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_1_2 (and (= accu_8_1 (ite (and sb-full_7_1 (= sb-adr_7_1 #x0000)) sb-val_7_1 (select heap_7 #x0000))) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) stmt_8_1_3 (not stmt_8_1_4)) (= block_8_0_1 (ite check_7_0 false block_7_0_1)) (= halt_8_1 halt_7_1) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_1_3 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) stmt_8_1_4) block_8_0_1 (= halt_8_1 halt_7_1) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_1_4 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2) (not stmt_8_1_3) (not stmt_8_1_4)) (= block_8_0_1 (ite check_7_0 false block_7_0_1)) (and halt_8_1 (ite (and halt_8_0 halt_8_2) (and exit_8 (= exit-code #x0000)) (not exit_8))) (= heap_8 heap_7))))

(assert (=> (not thread_7_1) (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 (ite flush_7_1 false sb-full_7_1)) (and (= stmt_8_1_0 stmt_7_1_0) (= stmt_8_1_1 stmt_7_1_1) (= stmt_8_1_2 stmt_7_1_2) (= stmt_8_1_3 stmt_7_1_3) (= stmt_8_1_4 stmt_7_1_4)) (= block_8_0_1 (ite check_7_0 false block_7_0_1)) (= halt_8_1 halt_7_1))))

(assert (=> flush_7_1 (and (= heap_8 (store heap_7 sb-adr_7_1 sb-val_7_1)) (not exit_8))))

; thread 2
(assert (=> exec_7_2_0 (and (= accu_8_2 accu_7_2) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) stmt_8_2_1 (not stmt_8_2_2) (not stmt_8_2_3) (not stmt_8_2_4) (not stmt_8_2_5)) block_8_0_2 (= halt_8_2 halt_7_2) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_2_1 (and (= accu_8_2 (bvadd accu_7_2 (ite (and sb-full_7_2 (= sb-adr_7_2 #x0000)) sb-val_7_2 (select heap_7 #x0000)))) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) (not stmt_8_2_1) stmt_8_2_2 (not stmt_8_2_3) (not stmt_8_2_4) (not stmt_8_2_5)) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_2_2 (and (= accu_8_2 (bvadd accu_7_2 (ite (and sb-full_7_2 (= sb-adr_7_2 #x0001)) sb-val_7_2 (select heap_7 #x0001)))) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) stmt_8_2_3 (not stmt_8_2_4) (not stmt_8_2_5)) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_2_3 (and (= accu_8_2 accu_7_2) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) (not stmt_8_2_3) (ite (= accu_7_2 #x0000) (not stmt_8_2_4) stmt_8_2_4) (ite (= accu_7_2 #x0000) stmt_8_2_5 (not stmt_8_2_5))) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_2_4 (and (= accu_8_2 accu_7_2) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) (not stmt_8_2_3) stmt_8_2_4 (not stmt_8_2_5)) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2) (= heap_8 heap_7) exit_8 (= exit-code #x0000))))

(assert (=> exec_7_2_5 (and (= accu_8_2 accu_7_2) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 sb-full_7_2) (and (not stmt_8_2_0) (not stmt_8_2_1) (not stmt_8_2_2) (not stmt_8_2_3) (not stmt_8_2_4) stmt_8_2_5) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2) (= heap_8 heap_7) exit_8 (= exit-code #x0001))))

(assert (=> (not thread_7_2) (and (= accu_8_2 accu_7_2) (= mem_8_2 mem_7_2) (= sb-adr_8_2 sb-adr_7_2) (= sb-val_8_2 sb-val_7_2) (= sb-full_8_2 (ite flush_7_2 false sb-full_7_2)) (and (= stmt_8_2_0 stmt_7_2_0) (= stmt_8_2_1 stmt_7_2_1) (= stmt_8_2_2 stmt_7_2_2) (= stmt_8_2_3 stmt_7_2_3) (= stmt_8_2_4 stmt_7_2_4) (= stmt_8_2_5 stmt_7_2_5)) (= block_8_0_2 (ite check_7_0 false block_7_0_2)) (= halt_8_2 halt_7_2))))

(assert (=> flush_7_2 (and (= heap_8 (store heap_7 sb-adr_7_2 sb-val_7_2)) (not exit_8))))

; exited
(assert (=> exit_7 (and (= heap_8 heap_7) exit_8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_9_0 () (_ BitVec 16))
(declare-fun accu_9_1 () (_ BitVec 16))
(declare-fun accu_9_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_9_0 () (_ BitVec 16))
(declare-fun mem_9_1 () (_ BitVec 16))
(declare-fun mem_9_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_9_0 () (_ BitVec 16))
(declare-fun sb-adr_9_1 () (_ BitVec 16))
(declare-fun sb-adr_9_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_9_0 () (_ BitVec 16))
(declare-fun sb-val_9_1 () (_ BitVec 16))
(declare-fun sb-val_9_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_9_0 () Bool)
(declare-fun sb-full_9_1 () Bool)
(declare-fun sb-full_9_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_9_0_0 () Bool)
(declare-fun stmt_9_0_1 () Bool)
(declare-fun stmt_9_0_2 () Bool)
(declare-fun stmt_9_0_3 () Bool)
(declare-fun stmt_9_0_4 () Bool)

(declare-fun stmt_9_1_0 () Bool)
(declare-fun stmt_9_1_1 () Bool)
(declare-fun stmt_9_1_2 () Bool)
(declare-fun stmt_9_1_3 () Bool)
(declare-fun stmt_9_1_4 () Bool)

(declare-fun stmt_9_2_0 () Bool)
(declare-fun stmt_9_2_1 () Bool)
(declare-fun stmt_9_2_2 () Bool)
(declare-fun stmt_9_2_3 () Bool)
(declare-fun stmt_9_2_4 () Bool)
(declare-fun stmt_9_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_9_0_0 () Bool)
(declare-fun block_9_0_1 () Bool)
(declare-fun block_9_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_9_0 () Bool)
(declare-fun halt_9_1 () Bool)
(declare-fun halt_9_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_9 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_9 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_9_0 () Bool)
(declare-fun thread_9_1 () Bool)
(declare-fun thread_9_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_9_0_0 () Bool)
(declare-fun exec_9_0_1 () Bool)
(declare-fun exec_9_0_2 () Bool)
(declare-fun exec_9_0_3 () Bool)
(declare-fun exec_9_0_4 () Bool)

(declare-fun exec_9_1_0 () Bool)
(declare-fun exec_9_1_1 () Bool)
(declare-fun exec_9_1_2 () Bool)
(declare-fun exec_9_1_3 () Bool)
(declare-fun exec_9_1_4 () Bool)

(declare-fun exec_9_2_0 () Bool)
(declare-fun exec_9_2_1 () Bool)
(declare-fun exec_9_2_2 () Bool)
(declare-fun exec_9_2_3 () Bool)
(declare-fun exec_9_2_4 () Bool)
(declare-fun exec_9_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_9_0 () Bool)
(declare-fun flush_9_1 () Bool)
(declare-fun flush_9_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_9_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_9_0_0 (and stmt_9_0_0 thread_9_0)))
(assert (= exec_9_0_1 (and stmt_9_0_1 thread_9_0)))
(assert (= exec_9_0_2 (and stmt_9_0_2 thread_9_0)))
(assert (= exec_9_0_3 (and stmt_9_0_3 thread_9_0)))
(assert (= exec_9_0_4 (and stmt_9_0_4 thread_9_0)))

(assert (= exec_9_1_0 (and stmt_9_1_0 thread_9_1)))
(assert (= exec_9_1_1 (and stmt_9_1_1 thread_9_1)))
(assert (= exec_9_1_2 (and stmt_9_1_2 thread_9_1)))
(assert (= exec_9_1_3 (and stmt_9_1_3 thread_9_1)))
(assert (= exec_9_1_4 (and stmt_9_1_4 thread_9_1)))

(assert (= exec_9_2_0 (and stmt_9_2_0 thread_9_2)))
(assert (= exec_9_2_1 (and stmt_9_2_1 thread_9_2)))
(assert (= exec_9_2_2 (and stmt_9_2_2 thread_9_2)))
(assert (= exec_9_2_3 (and stmt_9_2_3 thread_9_2)))
(assert (= exec_9_2_4 (and stmt_9_2_4 thread_9_2)))
(assert (= exec_9_2_5 (and stmt_9_2_5 thread_9_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_9_0 (and block_9_0_0 block_9_0_1 block_9_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_9_0 flush_9_0 thread_9_1 flush_9_1 thread_9_2 flush_9_2 exit_9))
(assert (or (not thread_9_0) (not flush_9_0)))
(assert (or (not thread_9_0) (not thread_9_1)))
(assert (or (not thread_9_0) (not flush_9_1)))
(assert (or (not thread_9_0) (not thread_9_2)))
(assert (or (not thread_9_0) (not flush_9_2)))
(assert (or (not thread_9_0) (not exit_9)))
(assert (or (not flush_9_0) (not thread_9_1)))
(assert (or (not flush_9_0) (not flush_9_1)))
(assert (or (not flush_9_0) (not thread_9_2)))
(assert (or (not flush_9_0) (not flush_9_2)))
(assert (or (not flush_9_0) (not exit_9)))
(assert (or (not thread_9_1) (not flush_9_1)))
(assert (or (not thread_9_1) (not thread_9_2)))
(assert (or (not thread_9_1) (not flush_9_2)))
(assert (or (not thread_9_1) (not exit_9)))
(assert (or (not flush_9_1) (not thread_9_2)))
(assert (or (not flush_9_1) (not flush_9_2)))
(assert (or (not flush_9_1) (not exit_9)))
(assert (or (not thread_9_2) (not flush_9_2)))
(assert (or (not thread_9_2) (not exit_9)))
(assert (or (not flush_9_2) (not exit_9)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_9_0 (=> (or stmt_9_0_1 stmt_9_0_4) (not thread_9_0)) (not flush_9_0)))
(assert (ite sb-full_9_1 (=> (or stmt_9_1_1 stmt_9_1_4) (not thread_9_1)) (not flush_9_1)))
(assert (=> (not sb-full_9_2) (not flush_9_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_9_0_0 (not check_9_0)) (not thread_9_0))) ; checkpoint 0: thread 0
(assert (=> (and block_9_0_1 (not check_9_0)) (not thread_9_1))) ; checkpoint 0: thread 1
(assert (=> (and block_9_0_2 (not check_9_0)) (not thread_9_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_9_0 (not thread_9_0)))
(assert (=> halt_9_1 (not thread_9_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_8_0_0 (and (= accu_9_0 (bvadd accu_8_0 #x0001)) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) stmt_9_0_1 (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4)) (= block_9_0_0 (ite check_8_0 false block_8_0_0)) (= halt_9_0 halt_8_0) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_0_1 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 #x0000) (= sb-val_9_0 accu_8_0) sb-full_9_0 (and (not stmt_9_0_0) (not stmt_9_0_1) stmt_9_0_2 (not stmt_9_0_3) (not stmt_9_0_4)) (= block_9_0_0 (ite check_8_0 false block_8_0_0)) (= halt_9_0 halt_8_0) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_0_2 (and (= accu_9_0 (ite (and sb-full_8_0 (= sb-adr_8_0 #x0001)) sb-val_8_0 (select heap_8 #x0001))) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) stmt_9_0_3 (not stmt_9_0_4)) (= block_9_0_0 (ite check_8_0 false block_8_0_0)) (= halt_9_0 halt_8_0) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_0_3 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) stmt_9_0_4) block_9_0_0 (= halt_9_0 halt_8_0) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_0_4 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2) (not stmt_9_0_3) (not stmt_9_0_4)) (= block_9_0_0 (ite check_8_0 false block_8_0_0)) (and halt_9_0 (ite (and halt_9_1 halt_9_2) (and exit_9 (= exit-code #x0000)) (not exit_9))) (= heap_9 heap_8))))

(assert (=> (not thread_8_0) (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 (ite flush_8_0 false sb-full_8_0)) (and (= stmt_9_0_0 stmt_8_0_0) (= stmt_9_0_1 stmt_8_0_1) (= stmt_9_0_2 stmt_8_0_2) (= stmt_9_0_3 stmt_8_0_3) (= stmt_9_0_4 stmt_8_0_4)) (= block_9_0_0 (ite check_8_0 false block_8_0_0)) (= halt_9_0 halt_8_0))))

(assert (=> flush_8_0 (and (= heap_9 (store heap_8 sb-adr_8_0 sb-val_8_0)) (not exit_9))))

; thread 1
(assert (=> exec_8_1_0 (and (= accu_9_1 (bvadd accu_8_1 #x0001)) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) stmt_9_1_1 (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4)) (= block_9_0_1 (ite check_8_0 false block_8_0_1)) (= halt_9_1 halt_8_1) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_1_1 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 #x0001) (= sb-val_9_1 accu_8_1) sb-full_9_1 (and (not stmt_9_1_0) (not stmt_9_1_1) stmt_9_1_2 (not stmt_9_1_3) (not stmt_9_1_4)) (= block_9_0_1 (ite check_8_0 false block_8_0_1)) (= halt_9_1 halt_8_1) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_1_2 (and (= accu_9_1 (ite (and sb-full_8_1 (= sb-adr_8_1 #x0000)) sb-val_8_1 (select heap_8 #x0000))) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) stmt_9_1_3 (not stmt_9_1_4)) (= block_9_0_1 (ite check_8_0 false block_8_0_1)) (= halt_9_1 halt_8_1) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_1_3 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) stmt_9_1_4) block_9_0_1 (= halt_9_1 halt_8_1) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_1_4 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2) (not stmt_9_1_3) (not stmt_9_1_4)) (= block_9_0_1 (ite check_8_0 false block_8_0_1)) (and halt_9_1 (ite (and halt_9_0 halt_9_2) (and exit_9 (= exit-code #x0000)) (not exit_9))) (= heap_9 heap_8))))

(assert (=> (not thread_8_1) (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 (ite flush_8_1 false sb-full_8_1)) (and (= stmt_9_1_0 stmt_8_1_0) (= stmt_9_1_1 stmt_8_1_1) (= stmt_9_1_2 stmt_8_1_2) (= stmt_9_1_3 stmt_8_1_3) (= stmt_9_1_4 stmt_8_1_4)) (= block_9_0_1 (ite check_8_0 false block_8_0_1)) (= halt_9_1 halt_8_1))))

(assert (=> flush_8_1 (and (= heap_9 (store heap_8 sb-adr_8_1 sb-val_8_1)) (not exit_9))))

; thread 2
(assert (=> exec_8_2_0 (and (= accu_9_2 accu_8_2) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) stmt_9_2_1 (not stmt_9_2_2) (not stmt_9_2_3) (not stmt_9_2_4) (not stmt_9_2_5)) block_9_0_2 (= halt_9_2 halt_8_2) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_2_1 (and (= accu_9_2 (bvadd accu_8_2 (ite (and sb-full_8_2 (= sb-adr_8_2 #x0000)) sb-val_8_2 (select heap_8 #x0000)))) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) (not stmt_9_2_1) stmt_9_2_2 (not stmt_9_2_3) (not stmt_9_2_4) (not stmt_9_2_5)) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_2_2 (and (= accu_9_2 (bvadd accu_8_2 (ite (and sb-full_8_2 (= sb-adr_8_2 #x0001)) sb-val_8_2 (select heap_8 #x0001)))) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) (not stmt_9_2_1) (not stmt_9_2_2) stmt_9_2_3 (not stmt_9_2_4) (not stmt_9_2_5)) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_2_3 (and (= accu_9_2 accu_8_2) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) (not stmt_9_2_1) (not stmt_9_2_2) (not stmt_9_2_3) (ite (= accu_8_2 #x0000) (not stmt_9_2_4) stmt_9_2_4) (ite (= accu_8_2 #x0000) stmt_9_2_5 (not stmt_9_2_5))) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_2_4 (and (= accu_9_2 accu_8_2) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) (not stmt_9_2_1) (not stmt_9_2_2) (not stmt_9_2_3) stmt_9_2_4 (not stmt_9_2_5)) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2) (= heap_9 heap_8) exit_9 (= exit-code #x0000))))

(assert (=> exec_8_2_5 (and (= accu_9_2 accu_8_2) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 sb-full_8_2) (and (not stmt_9_2_0) (not stmt_9_2_1) (not stmt_9_2_2) (not stmt_9_2_3) (not stmt_9_2_4) stmt_9_2_5) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2) (= heap_9 heap_8) exit_9 (= exit-code #x0001))))

(assert (=> (not thread_8_2) (and (= accu_9_2 accu_8_2) (= mem_9_2 mem_8_2) (= sb-adr_9_2 sb-adr_8_2) (= sb-val_9_2 sb-val_8_2) (= sb-full_9_2 (ite flush_8_2 false sb-full_8_2)) (and (= stmt_9_2_0 stmt_8_2_0) (= stmt_9_2_1 stmt_8_2_1) (= stmt_9_2_2 stmt_8_2_2) (= stmt_9_2_3 stmt_8_2_3) (= stmt_9_2_4 stmt_8_2_4) (= stmt_9_2_5 stmt_8_2_5)) (= block_9_0_2 (ite check_8_0 false block_8_0_2)) (= halt_9_2 halt_8_2))))

(assert (=> flush_8_2 (and (= heap_9 (store heap_8 sb-adr_8_2 sb-val_8_2)) (not exit_9))))

; exited
(assert (=> exit_8 (and (= heap_9 heap_8) exit_9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 10
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_10_0 () (_ BitVec 16))
(declare-fun accu_10_1 () (_ BitVec 16))
(declare-fun accu_10_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_10_0 () (_ BitVec 16))
(declare-fun mem_10_1 () (_ BitVec 16))
(declare-fun mem_10_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_10_0 () (_ BitVec 16))
(declare-fun sb-adr_10_1 () (_ BitVec 16))
(declare-fun sb-adr_10_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_10_0 () (_ BitVec 16))
(declare-fun sb-val_10_1 () (_ BitVec 16))
(declare-fun sb-val_10_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_10_0 () Bool)
(declare-fun sb-full_10_1 () Bool)
(declare-fun sb-full_10_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_10_0_0 () Bool)
(declare-fun stmt_10_0_1 () Bool)
(declare-fun stmt_10_0_2 () Bool)
(declare-fun stmt_10_0_3 () Bool)
(declare-fun stmt_10_0_4 () Bool)

(declare-fun stmt_10_1_0 () Bool)
(declare-fun stmt_10_1_1 () Bool)
(declare-fun stmt_10_1_2 () Bool)
(declare-fun stmt_10_1_3 () Bool)
(declare-fun stmt_10_1_4 () Bool)

(declare-fun stmt_10_2_0 () Bool)
(declare-fun stmt_10_2_1 () Bool)
(declare-fun stmt_10_2_2 () Bool)
(declare-fun stmt_10_2_3 () Bool)
(declare-fun stmt_10_2_4 () Bool)
(declare-fun stmt_10_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_10_0_0 () Bool)
(declare-fun block_10_0_1 () Bool)
(declare-fun block_10_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_10_0 () Bool)
(declare-fun halt_10_1 () Bool)
(declare-fun halt_10_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_10 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_10 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_10_0 () Bool)
(declare-fun thread_10_1 () Bool)
(declare-fun thread_10_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_10_0_0 () Bool)
(declare-fun exec_10_0_1 () Bool)
(declare-fun exec_10_0_2 () Bool)
(declare-fun exec_10_0_3 () Bool)
(declare-fun exec_10_0_4 () Bool)

(declare-fun exec_10_1_0 () Bool)
(declare-fun exec_10_1_1 () Bool)
(declare-fun exec_10_1_2 () Bool)
(declare-fun exec_10_1_3 () Bool)
(declare-fun exec_10_1_4 () Bool)

(declare-fun exec_10_2_0 () Bool)
(declare-fun exec_10_2_1 () Bool)
(declare-fun exec_10_2_2 () Bool)
(declare-fun exec_10_2_3 () Bool)
(declare-fun exec_10_2_4 () Bool)
(declare-fun exec_10_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_10_0 () Bool)
(declare-fun flush_10_1 () Bool)
(declare-fun flush_10_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_10_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_10_0_0 (and stmt_10_0_0 thread_10_0)))
(assert (= exec_10_0_1 (and stmt_10_0_1 thread_10_0)))
(assert (= exec_10_0_2 (and stmt_10_0_2 thread_10_0)))
(assert (= exec_10_0_3 (and stmt_10_0_3 thread_10_0)))
(assert (= exec_10_0_4 (and stmt_10_0_4 thread_10_0)))

(assert (= exec_10_1_0 (and stmt_10_1_0 thread_10_1)))
(assert (= exec_10_1_1 (and stmt_10_1_1 thread_10_1)))
(assert (= exec_10_1_2 (and stmt_10_1_2 thread_10_1)))
(assert (= exec_10_1_3 (and stmt_10_1_3 thread_10_1)))
(assert (= exec_10_1_4 (and stmt_10_1_4 thread_10_1)))

(assert (= exec_10_2_0 (and stmt_10_2_0 thread_10_2)))
(assert (= exec_10_2_1 (and stmt_10_2_1 thread_10_2)))
(assert (= exec_10_2_2 (and stmt_10_2_2 thread_10_2)))
(assert (= exec_10_2_3 (and stmt_10_2_3 thread_10_2)))
(assert (= exec_10_2_4 (and stmt_10_2_4 thread_10_2)))
(assert (= exec_10_2_5 (and stmt_10_2_5 thread_10_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_10_0 (and block_10_0_0 block_10_0_1 block_10_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_10_0 flush_10_0 thread_10_1 flush_10_1 thread_10_2 flush_10_2 exit_10))
(assert (or (not thread_10_0) (not flush_10_0)))
(assert (or (not thread_10_0) (not thread_10_1)))
(assert (or (not thread_10_0) (not flush_10_1)))
(assert (or (not thread_10_0) (not thread_10_2)))
(assert (or (not thread_10_0) (not flush_10_2)))
(assert (or (not thread_10_0) (not exit_10)))
(assert (or (not flush_10_0) (not thread_10_1)))
(assert (or (not flush_10_0) (not flush_10_1)))
(assert (or (not flush_10_0) (not thread_10_2)))
(assert (or (not flush_10_0) (not flush_10_2)))
(assert (or (not flush_10_0) (not exit_10)))
(assert (or (not thread_10_1) (not flush_10_1)))
(assert (or (not thread_10_1) (not thread_10_2)))
(assert (or (not thread_10_1) (not flush_10_2)))
(assert (or (not thread_10_1) (not exit_10)))
(assert (or (not flush_10_1) (not thread_10_2)))
(assert (or (not flush_10_1) (not flush_10_2)))
(assert (or (not flush_10_1) (not exit_10)))
(assert (or (not thread_10_2) (not flush_10_2)))
(assert (or (not thread_10_2) (not exit_10)))
(assert (or (not flush_10_2) (not exit_10)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_10_0 (=> (or stmt_10_0_1 stmt_10_0_4) (not thread_10_0)) (not flush_10_0)))
(assert (ite sb-full_10_1 (=> (or stmt_10_1_1 stmt_10_1_4) (not thread_10_1)) (not flush_10_1)))
(assert (=> (not sb-full_10_2) (not flush_10_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_10_0_0 (not check_10_0)) (not thread_10_0))) ; checkpoint 0: thread 0
(assert (=> (and block_10_0_1 (not check_10_0)) (not thread_10_1))) ; checkpoint 0: thread 1
(assert (=> (and block_10_0_2 (not check_10_0)) (not thread_10_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_10_0 (not thread_10_0)))
(assert (=> halt_10_1 (not thread_10_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_9_0_0 (and (= accu_10_0 (bvadd accu_9_0 #x0001)) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) stmt_10_0_1 (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4)) (= block_10_0_0 (ite check_9_0 false block_9_0_0)) (= halt_10_0 halt_9_0) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_0_1 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 #x0000) (= sb-val_10_0 accu_9_0) sb-full_10_0 (and (not stmt_10_0_0) (not stmt_10_0_1) stmt_10_0_2 (not stmt_10_0_3) (not stmt_10_0_4)) (= block_10_0_0 (ite check_9_0 false block_9_0_0)) (= halt_10_0 halt_9_0) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_0_2 (and (= accu_10_0 (ite (and sb-full_9_0 (= sb-adr_9_0 #x0001)) sb-val_9_0 (select heap_9 #x0001))) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) stmt_10_0_3 (not stmt_10_0_4)) (= block_10_0_0 (ite check_9_0 false block_9_0_0)) (= halt_10_0 halt_9_0) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_0_3 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) stmt_10_0_4) block_10_0_0 (= halt_10_0 halt_9_0) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_0_4 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2) (not stmt_10_0_3) (not stmt_10_0_4)) (= block_10_0_0 (ite check_9_0 false block_9_0_0)) (and halt_10_0 (ite (and halt_10_1 halt_10_2) (and exit_10 (= exit-code #x0000)) (not exit_10))) (= heap_10 heap_9))))

(assert (=> (not thread_9_0) (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 (ite flush_9_0 false sb-full_9_0)) (and (= stmt_10_0_0 stmt_9_0_0) (= stmt_10_0_1 stmt_9_0_1) (= stmt_10_0_2 stmt_9_0_2) (= stmt_10_0_3 stmt_9_0_3) (= stmt_10_0_4 stmt_9_0_4)) (= block_10_0_0 (ite check_9_0 false block_9_0_0)) (= halt_10_0 halt_9_0))))

(assert (=> flush_9_0 (and (= heap_10 (store heap_9 sb-adr_9_0 sb-val_9_0)) (not exit_10))))

; thread 1
(assert (=> exec_9_1_0 (and (= accu_10_1 (bvadd accu_9_1 #x0001)) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) stmt_10_1_1 (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4)) (= block_10_0_1 (ite check_9_0 false block_9_0_1)) (= halt_10_1 halt_9_1) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_1_1 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 #x0001) (= sb-val_10_1 accu_9_1) sb-full_10_1 (and (not stmt_10_1_0) (not stmt_10_1_1) stmt_10_1_2 (not stmt_10_1_3) (not stmt_10_1_4)) (= block_10_0_1 (ite check_9_0 false block_9_0_1)) (= halt_10_1 halt_9_1) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_1_2 (and (= accu_10_1 (ite (and sb-full_9_1 (= sb-adr_9_1 #x0000)) sb-val_9_1 (select heap_9 #x0000))) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) stmt_10_1_3 (not stmt_10_1_4)) (= block_10_0_1 (ite check_9_0 false block_9_0_1)) (= halt_10_1 halt_9_1) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_1_3 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) stmt_10_1_4) block_10_0_1 (= halt_10_1 halt_9_1) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_1_4 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2) (not stmt_10_1_3) (not stmt_10_1_4)) (= block_10_0_1 (ite check_9_0 false block_9_0_1)) (and halt_10_1 (ite (and halt_10_0 halt_10_2) (and exit_10 (= exit-code #x0000)) (not exit_10))) (= heap_10 heap_9))))

(assert (=> (not thread_9_1) (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 (ite flush_9_1 false sb-full_9_1)) (and (= stmt_10_1_0 stmt_9_1_0) (= stmt_10_1_1 stmt_9_1_1) (= stmt_10_1_2 stmt_9_1_2) (= stmt_10_1_3 stmt_9_1_3) (= stmt_10_1_4 stmt_9_1_4)) (= block_10_0_1 (ite check_9_0 false block_9_0_1)) (= halt_10_1 halt_9_1))))

(assert (=> flush_9_1 (and (= heap_10 (store heap_9 sb-adr_9_1 sb-val_9_1)) (not exit_10))))

; thread 2
(assert (=> exec_9_2_0 (and (= accu_10_2 accu_9_2) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) stmt_10_2_1 (not stmt_10_2_2) (not stmt_10_2_3) (not stmt_10_2_4) (not stmt_10_2_5)) block_10_0_2 (= halt_10_2 halt_9_2) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_2_1 (and (= accu_10_2 (bvadd accu_9_2 (ite (and sb-full_9_2 (= sb-adr_9_2 #x0000)) sb-val_9_2 (select heap_9 #x0000)))) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) (not stmt_10_2_1) stmt_10_2_2 (not stmt_10_2_3) (not stmt_10_2_4) (not stmt_10_2_5)) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_2_2 (and (= accu_10_2 (bvadd accu_9_2 (ite (and sb-full_9_2 (= sb-adr_9_2 #x0001)) sb-val_9_2 (select heap_9 #x0001)))) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) (not stmt_10_2_1) (not stmt_10_2_2) stmt_10_2_3 (not stmt_10_2_4) (not stmt_10_2_5)) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_2_3 (and (= accu_10_2 accu_9_2) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) (not stmt_10_2_1) (not stmt_10_2_2) (not stmt_10_2_3) (ite (= accu_9_2 #x0000) (not stmt_10_2_4) stmt_10_2_4) (ite (= accu_9_2 #x0000) stmt_10_2_5 (not stmt_10_2_5))) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_2_4 (and (= accu_10_2 accu_9_2) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) (not stmt_10_2_1) (not stmt_10_2_2) (not stmt_10_2_3) stmt_10_2_4 (not stmt_10_2_5)) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2) (= heap_10 heap_9) exit_10 (= exit-code #x0000))))

(assert (=> exec_9_2_5 (and (= accu_10_2 accu_9_2) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 sb-full_9_2) (and (not stmt_10_2_0) (not stmt_10_2_1) (not stmt_10_2_2) (not stmt_10_2_3) (not stmt_10_2_4) stmt_10_2_5) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2) (= heap_10 heap_9) exit_10 (= exit-code #x0001))))

(assert (=> (not thread_9_2) (and (= accu_10_2 accu_9_2) (= mem_10_2 mem_9_2) (= sb-adr_10_2 sb-adr_9_2) (= sb-val_10_2 sb-val_9_2) (= sb-full_10_2 (ite flush_9_2 false sb-full_9_2)) (and (= stmt_10_2_0 stmt_9_2_0) (= stmt_10_2_1 stmt_9_2_1) (= stmt_10_2_2 stmt_9_2_2) (= stmt_10_2_3 stmt_9_2_3) (= stmt_10_2_4 stmt_9_2_4) (= stmt_10_2_5 stmt_9_2_5)) (= block_10_0_2 (ite check_9_0 false block_9_0_2)) (= halt_10_2 halt_9_2))))

(assert (=> flush_9_2 (and (= heap_10 (store heap_9 sb-adr_9_2 sb-val_9_2)) (not exit_10))))

; exited
(assert (=> exit_9 (and (= heap_10 heap_9) exit_10)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 11
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_11_0 () (_ BitVec 16))
(declare-fun accu_11_1 () (_ BitVec 16))
(declare-fun accu_11_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_11_0 () (_ BitVec 16))
(declare-fun mem_11_1 () (_ BitVec 16))
(declare-fun mem_11_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_11_0 () (_ BitVec 16))
(declare-fun sb-adr_11_1 () (_ BitVec 16))
(declare-fun sb-adr_11_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_11_0 () (_ BitVec 16))
(declare-fun sb-val_11_1 () (_ BitVec 16))
(declare-fun sb-val_11_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_11_0 () Bool)
(declare-fun sb-full_11_1 () Bool)
(declare-fun sb-full_11_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_11_0_0 () Bool)
(declare-fun stmt_11_0_1 () Bool)
(declare-fun stmt_11_0_2 () Bool)
(declare-fun stmt_11_0_3 () Bool)
(declare-fun stmt_11_0_4 () Bool)

(declare-fun stmt_11_1_0 () Bool)
(declare-fun stmt_11_1_1 () Bool)
(declare-fun stmt_11_1_2 () Bool)
(declare-fun stmt_11_1_3 () Bool)
(declare-fun stmt_11_1_4 () Bool)

(declare-fun stmt_11_2_0 () Bool)
(declare-fun stmt_11_2_1 () Bool)
(declare-fun stmt_11_2_2 () Bool)
(declare-fun stmt_11_2_3 () Bool)
(declare-fun stmt_11_2_4 () Bool)
(declare-fun stmt_11_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_11_0_0 () Bool)
(declare-fun block_11_0_1 () Bool)
(declare-fun block_11_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_11_0 () Bool)
(declare-fun halt_11_1 () Bool)
(declare-fun halt_11_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_11 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_11 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_11_0 () Bool)
(declare-fun thread_11_1 () Bool)
(declare-fun thread_11_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_11_0_0 () Bool)
(declare-fun exec_11_0_1 () Bool)
(declare-fun exec_11_0_2 () Bool)
(declare-fun exec_11_0_3 () Bool)
(declare-fun exec_11_0_4 () Bool)

(declare-fun exec_11_1_0 () Bool)
(declare-fun exec_11_1_1 () Bool)
(declare-fun exec_11_1_2 () Bool)
(declare-fun exec_11_1_3 () Bool)
(declare-fun exec_11_1_4 () Bool)

(declare-fun exec_11_2_0 () Bool)
(declare-fun exec_11_2_1 () Bool)
(declare-fun exec_11_2_2 () Bool)
(declare-fun exec_11_2_3 () Bool)
(declare-fun exec_11_2_4 () Bool)
(declare-fun exec_11_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_11_0 () Bool)
(declare-fun flush_11_1 () Bool)
(declare-fun flush_11_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_11_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_11_0_0 (and stmt_11_0_0 thread_11_0)))
(assert (= exec_11_0_1 (and stmt_11_0_1 thread_11_0)))
(assert (= exec_11_0_2 (and stmt_11_0_2 thread_11_0)))
(assert (= exec_11_0_3 (and stmt_11_0_3 thread_11_0)))
(assert (= exec_11_0_4 (and stmt_11_0_4 thread_11_0)))

(assert (= exec_11_1_0 (and stmt_11_1_0 thread_11_1)))
(assert (= exec_11_1_1 (and stmt_11_1_1 thread_11_1)))
(assert (= exec_11_1_2 (and stmt_11_1_2 thread_11_1)))
(assert (= exec_11_1_3 (and stmt_11_1_3 thread_11_1)))
(assert (= exec_11_1_4 (and stmt_11_1_4 thread_11_1)))

(assert (= exec_11_2_0 (and stmt_11_2_0 thread_11_2)))
(assert (= exec_11_2_1 (and stmt_11_2_1 thread_11_2)))
(assert (= exec_11_2_2 (and stmt_11_2_2 thread_11_2)))
(assert (= exec_11_2_3 (and stmt_11_2_3 thread_11_2)))
(assert (= exec_11_2_4 (and stmt_11_2_4 thread_11_2)))
(assert (= exec_11_2_5 (and stmt_11_2_5 thread_11_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_11_0 (and block_11_0_0 block_11_0_1 block_11_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_11_0 flush_11_0 thread_11_1 flush_11_1 thread_11_2 flush_11_2 exit_11))
(assert (or (not thread_11_0) (not flush_11_0)))
(assert (or (not thread_11_0) (not thread_11_1)))
(assert (or (not thread_11_0) (not flush_11_1)))
(assert (or (not thread_11_0) (not thread_11_2)))
(assert (or (not thread_11_0) (not flush_11_2)))
(assert (or (not thread_11_0) (not exit_11)))
(assert (or (not flush_11_0) (not thread_11_1)))
(assert (or (not flush_11_0) (not flush_11_1)))
(assert (or (not flush_11_0) (not thread_11_2)))
(assert (or (not flush_11_0) (not flush_11_2)))
(assert (or (not flush_11_0) (not exit_11)))
(assert (or (not thread_11_1) (not flush_11_1)))
(assert (or (not thread_11_1) (not thread_11_2)))
(assert (or (not thread_11_1) (not flush_11_2)))
(assert (or (not thread_11_1) (not exit_11)))
(assert (or (not flush_11_1) (not thread_11_2)))
(assert (or (not flush_11_1) (not flush_11_2)))
(assert (or (not flush_11_1) (not exit_11)))
(assert (or (not thread_11_2) (not flush_11_2)))
(assert (or (not thread_11_2) (not exit_11)))
(assert (or (not flush_11_2) (not exit_11)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_11_0 (=> (or stmt_11_0_1 stmt_11_0_4) (not thread_11_0)) (not flush_11_0)))
(assert (ite sb-full_11_1 (=> (or stmt_11_1_1 stmt_11_1_4) (not thread_11_1)) (not flush_11_1)))
(assert (=> (not sb-full_11_2) (not flush_11_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_11_0_0 (not check_11_0)) (not thread_11_0))) ; checkpoint 0: thread 0
(assert (=> (and block_11_0_1 (not check_11_0)) (not thread_11_1))) ; checkpoint 0: thread 1
(assert (=> (and block_11_0_2 (not check_11_0)) (not thread_11_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_11_0 (not thread_11_0)))
(assert (=> halt_11_1 (not thread_11_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_10_0_0 (and (= accu_11_0 (bvadd accu_10_0 #x0001)) (= mem_11_0 mem_10_0) (= sb-adr_11_0 sb-adr_10_0) (= sb-val_11_0 sb-val_10_0) (= sb-full_11_0 sb-full_10_0) (and (not stmt_11_0_0) stmt_11_0_1 (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4)) (= block_11_0_0 (ite check_10_0 false block_10_0_0)) (= halt_11_0 halt_10_0) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_0_1 (and (= accu_11_0 accu_10_0) (= mem_11_0 mem_10_0) (= sb-adr_11_0 #x0000) (= sb-val_11_0 accu_10_0) sb-full_11_0 (and (not stmt_11_0_0) (not stmt_11_0_1) stmt_11_0_2 (not stmt_11_0_3) (not stmt_11_0_4)) (= block_11_0_0 (ite check_10_0 false block_10_0_0)) (= halt_11_0 halt_10_0) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_0_2 (and (= accu_11_0 (ite (and sb-full_10_0 (= sb-adr_10_0 #x0001)) sb-val_10_0 (select heap_10 #x0001))) (= mem_11_0 mem_10_0) (= sb-adr_11_0 sb-adr_10_0) (= sb-val_11_0 sb-val_10_0) (= sb-full_11_0 sb-full_10_0) (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) stmt_11_0_3 (not stmt_11_0_4)) (= block_11_0_0 (ite check_10_0 false block_10_0_0)) (= halt_11_0 halt_10_0) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_0_3 (and (= accu_11_0 accu_10_0) (= mem_11_0 mem_10_0) (= sb-adr_11_0 sb-adr_10_0) (= sb-val_11_0 sb-val_10_0) (= sb-full_11_0 sb-full_10_0) (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) stmt_11_0_4) block_11_0_0 (= halt_11_0 halt_10_0) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_0_4 (and (= accu_11_0 accu_10_0) (= mem_11_0 mem_10_0) (= sb-adr_11_0 sb-adr_10_0) (= sb-val_11_0 sb-val_10_0) (= sb-full_11_0 sb-full_10_0) (and (not stmt_11_0_0) (not stmt_11_0_1) (not stmt_11_0_2) (not stmt_11_0_3) (not stmt_11_0_4)) (= block_11_0_0 (ite check_10_0 false block_10_0_0)) (and halt_11_0 (ite (and halt_11_1 halt_11_2) (and exit_11 (= exit-code #x0000)) (not exit_11))) (= heap_11 heap_10))))

(assert (=> (not thread_10_0) (and (= accu_11_0 accu_10_0) (= mem_11_0 mem_10_0) (= sb-adr_11_0 sb-adr_10_0) (= sb-val_11_0 sb-val_10_0) (= sb-full_11_0 (ite flush_10_0 false sb-full_10_0)) (and (= stmt_11_0_0 stmt_10_0_0) (= stmt_11_0_1 stmt_10_0_1) (= stmt_11_0_2 stmt_10_0_2) (= stmt_11_0_3 stmt_10_0_3) (= stmt_11_0_4 stmt_10_0_4)) (= block_11_0_0 (ite check_10_0 false block_10_0_0)) (= halt_11_0 halt_10_0))))

(assert (=> flush_10_0 (and (= heap_11 (store heap_10 sb-adr_10_0 sb-val_10_0)) (not exit_11))))

; thread 1
(assert (=> exec_10_1_0 (and (= accu_11_1 (bvadd accu_10_1 #x0001)) (= mem_11_1 mem_10_1) (= sb-adr_11_1 sb-adr_10_1) (= sb-val_11_1 sb-val_10_1) (= sb-full_11_1 sb-full_10_1) (and (not stmt_11_1_0) stmt_11_1_1 (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4)) (= block_11_0_1 (ite check_10_0 false block_10_0_1)) (= halt_11_1 halt_10_1) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_1_1 (and (= accu_11_1 accu_10_1) (= mem_11_1 mem_10_1) (= sb-adr_11_1 #x0001) (= sb-val_11_1 accu_10_1) sb-full_11_1 (and (not stmt_11_1_0) (not stmt_11_1_1) stmt_11_1_2 (not stmt_11_1_3) (not stmt_11_1_4)) (= block_11_0_1 (ite check_10_0 false block_10_0_1)) (= halt_11_1 halt_10_1) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_1_2 (and (= accu_11_1 (ite (and sb-full_10_1 (= sb-adr_10_1 #x0000)) sb-val_10_1 (select heap_10 #x0000))) (= mem_11_1 mem_10_1) (= sb-adr_11_1 sb-adr_10_1) (= sb-val_11_1 sb-val_10_1) (= sb-full_11_1 sb-full_10_1) (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) stmt_11_1_3 (not stmt_11_1_4)) (= block_11_0_1 (ite check_10_0 false block_10_0_1)) (= halt_11_1 halt_10_1) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_1_3 (and (= accu_11_1 accu_10_1) (= mem_11_1 mem_10_1) (= sb-adr_11_1 sb-adr_10_1) (= sb-val_11_1 sb-val_10_1) (= sb-full_11_1 sb-full_10_1) (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) stmt_11_1_4) block_11_0_1 (= halt_11_1 halt_10_1) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_1_4 (and (= accu_11_1 accu_10_1) (= mem_11_1 mem_10_1) (= sb-adr_11_1 sb-adr_10_1) (= sb-val_11_1 sb-val_10_1) (= sb-full_11_1 sb-full_10_1) (and (not stmt_11_1_0) (not stmt_11_1_1) (not stmt_11_1_2) (not stmt_11_1_3) (not stmt_11_1_4)) (= block_11_0_1 (ite check_10_0 false block_10_0_1)) (and halt_11_1 (ite (and halt_11_0 halt_11_2) (and exit_11 (= exit-code #x0000)) (not exit_11))) (= heap_11 heap_10))))

(assert (=> (not thread_10_1) (and (= accu_11_1 accu_10_1) (= mem_11_1 mem_10_1) (= sb-adr_11_1 sb-adr_10_1) (= sb-val_11_1 sb-val_10_1) (= sb-full_11_1 (ite flush_10_1 false sb-full_10_1)) (and (= stmt_11_1_0 stmt_10_1_0) (= stmt_11_1_1 stmt_10_1_1) (= stmt_11_1_2 stmt_10_1_2) (= stmt_11_1_3 stmt_10_1_3) (= stmt_11_1_4 stmt_10_1_4)) (= block_11_0_1 (ite check_10_0 false block_10_0_1)) (= halt_11_1 halt_10_1))))

(assert (=> flush_10_1 (and (= heap_11 (store heap_10 sb-adr_10_1 sb-val_10_1)) (not exit_11))))

; thread 2
(assert (=> exec_10_2_0 (and (= accu_11_2 accu_10_2) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) stmt_11_2_1 (not stmt_11_2_2) (not stmt_11_2_3) (not stmt_11_2_4) (not stmt_11_2_5)) block_11_0_2 (= halt_11_2 halt_10_2) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_2_1 (and (= accu_11_2 (bvadd accu_10_2 (ite (and sb-full_10_2 (= sb-adr_10_2 #x0000)) sb-val_10_2 (select heap_10 #x0000)))) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) (not stmt_11_2_1) stmt_11_2_2 (not stmt_11_2_3) (not stmt_11_2_4) (not stmt_11_2_5)) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_2_2 (and (= accu_11_2 (bvadd accu_10_2 (ite (and sb-full_10_2 (= sb-adr_10_2 #x0001)) sb-val_10_2 (select heap_10 #x0001)))) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) (not stmt_11_2_1) (not stmt_11_2_2) stmt_11_2_3 (not stmt_11_2_4) (not stmt_11_2_5)) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_2_3 (and (= accu_11_2 accu_10_2) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) (not stmt_11_2_1) (not stmt_11_2_2) (not stmt_11_2_3) (ite (= accu_10_2 #x0000) (not stmt_11_2_4) stmt_11_2_4) (ite (= accu_10_2 #x0000) stmt_11_2_5 (not stmt_11_2_5))) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2) (= heap_11 heap_10) (not exit_11))))

(assert (=> exec_10_2_4 (and (= accu_11_2 accu_10_2) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) (not stmt_11_2_1) (not stmt_11_2_2) (not stmt_11_2_3) stmt_11_2_4 (not stmt_11_2_5)) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2) (= heap_11 heap_10) exit_11 (= exit-code #x0000))))

(assert (=> exec_10_2_5 (and (= accu_11_2 accu_10_2) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 sb-full_10_2) (and (not stmt_11_2_0) (not stmt_11_2_1) (not stmt_11_2_2) (not stmt_11_2_3) (not stmt_11_2_4) stmt_11_2_5) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2) (= heap_11 heap_10) exit_11 (= exit-code #x0001))))

(assert (=> (not thread_10_2) (and (= accu_11_2 accu_10_2) (= mem_11_2 mem_10_2) (= sb-adr_11_2 sb-adr_10_2) (= sb-val_11_2 sb-val_10_2) (= sb-full_11_2 (ite flush_10_2 false sb-full_10_2)) (and (= stmt_11_2_0 stmt_10_2_0) (= stmt_11_2_1 stmt_10_2_1) (= stmt_11_2_2 stmt_10_2_2) (= stmt_11_2_3 stmt_10_2_3) (= stmt_11_2_4 stmt_10_2_4) (= stmt_11_2_5 stmt_10_2_5)) (= block_11_0_2 (ite check_10_0 false block_10_0_2)) (= halt_11_2 halt_10_2))))

(assert (=> flush_10_2 (and (= heap_11 (store heap_10 sb-adr_10_2 sb-val_10_2)) (not exit_11))))

; exited
(assert (=> exit_10 (and (= heap_11 heap_10) exit_11)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_12_0 () (_ BitVec 16))
(declare-fun accu_12_1 () (_ BitVec 16))
(declare-fun accu_12_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_12_0 () (_ BitVec 16))
(declare-fun mem_12_1 () (_ BitVec 16))
(declare-fun mem_12_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_12_0 () (_ BitVec 16))
(declare-fun sb-adr_12_1 () (_ BitVec 16))
(declare-fun sb-adr_12_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_12_0 () (_ BitVec 16))
(declare-fun sb-val_12_1 () (_ BitVec 16))
(declare-fun sb-val_12_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_12_0 () Bool)
(declare-fun sb-full_12_1 () Bool)
(declare-fun sb-full_12_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_12_0_0 () Bool)
(declare-fun stmt_12_0_1 () Bool)
(declare-fun stmt_12_0_2 () Bool)
(declare-fun stmt_12_0_3 () Bool)
(declare-fun stmt_12_0_4 () Bool)

(declare-fun stmt_12_1_0 () Bool)
(declare-fun stmt_12_1_1 () Bool)
(declare-fun stmt_12_1_2 () Bool)
(declare-fun stmt_12_1_3 () Bool)
(declare-fun stmt_12_1_4 () Bool)

(declare-fun stmt_12_2_0 () Bool)
(declare-fun stmt_12_2_1 () Bool)
(declare-fun stmt_12_2_2 () Bool)
(declare-fun stmt_12_2_3 () Bool)
(declare-fun stmt_12_2_4 () Bool)
(declare-fun stmt_12_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_12_0_0 () Bool)
(declare-fun block_12_0_1 () Bool)
(declare-fun block_12_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_12_0 () Bool)
(declare-fun halt_12_1 () Bool)
(declare-fun halt_12_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_12 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_12 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_12_0 () Bool)
(declare-fun thread_12_1 () Bool)
(declare-fun thread_12_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_12_0_0 () Bool)
(declare-fun exec_12_0_1 () Bool)
(declare-fun exec_12_0_2 () Bool)
(declare-fun exec_12_0_3 () Bool)
(declare-fun exec_12_0_4 () Bool)

(declare-fun exec_12_1_0 () Bool)
(declare-fun exec_12_1_1 () Bool)
(declare-fun exec_12_1_2 () Bool)
(declare-fun exec_12_1_3 () Bool)
(declare-fun exec_12_1_4 () Bool)

(declare-fun exec_12_2_0 () Bool)
(declare-fun exec_12_2_1 () Bool)
(declare-fun exec_12_2_2 () Bool)
(declare-fun exec_12_2_3 () Bool)
(declare-fun exec_12_2_4 () Bool)
(declare-fun exec_12_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_12_0 () Bool)
(declare-fun flush_12_1 () Bool)
(declare-fun flush_12_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_12_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_12_0_0 (and stmt_12_0_0 thread_12_0)))
(assert (= exec_12_0_1 (and stmt_12_0_1 thread_12_0)))
(assert (= exec_12_0_2 (and stmt_12_0_2 thread_12_0)))
(assert (= exec_12_0_3 (and stmt_12_0_3 thread_12_0)))
(assert (= exec_12_0_4 (and stmt_12_0_4 thread_12_0)))

(assert (= exec_12_1_0 (and stmt_12_1_0 thread_12_1)))
(assert (= exec_12_1_1 (and stmt_12_1_1 thread_12_1)))
(assert (= exec_12_1_2 (and stmt_12_1_2 thread_12_1)))
(assert (= exec_12_1_3 (and stmt_12_1_3 thread_12_1)))
(assert (= exec_12_1_4 (and stmt_12_1_4 thread_12_1)))

(assert (= exec_12_2_0 (and stmt_12_2_0 thread_12_2)))
(assert (= exec_12_2_1 (and stmt_12_2_1 thread_12_2)))
(assert (= exec_12_2_2 (and stmt_12_2_2 thread_12_2)))
(assert (= exec_12_2_3 (and stmt_12_2_3 thread_12_2)))
(assert (= exec_12_2_4 (and stmt_12_2_4 thread_12_2)))
(assert (= exec_12_2_5 (and stmt_12_2_5 thread_12_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_12_0 (and block_12_0_0 block_12_0_1 block_12_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_12_0 flush_12_0 thread_12_1 flush_12_1 thread_12_2 flush_12_2 exit_12))
(assert (or (not thread_12_0) (not flush_12_0)))
(assert (or (not thread_12_0) (not thread_12_1)))
(assert (or (not thread_12_0) (not flush_12_1)))
(assert (or (not thread_12_0) (not thread_12_2)))
(assert (or (not thread_12_0) (not flush_12_2)))
(assert (or (not thread_12_0) (not exit_12)))
(assert (or (not flush_12_0) (not thread_12_1)))
(assert (or (not flush_12_0) (not flush_12_1)))
(assert (or (not flush_12_0) (not thread_12_2)))
(assert (or (not flush_12_0) (not flush_12_2)))
(assert (or (not flush_12_0) (not exit_12)))
(assert (or (not thread_12_1) (not flush_12_1)))
(assert (or (not thread_12_1) (not thread_12_2)))
(assert (or (not thread_12_1) (not flush_12_2)))
(assert (or (not thread_12_1) (not exit_12)))
(assert (or (not flush_12_1) (not thread_12_2)))
(assert (or (not flush_12_1) (not flush_12_2)))
(assert (or (not flush_12_1) (not exit_12)))
(assert (or (not thread_12_2) (not flush_12_2)))
(assert (or (not thread_12_2) (not exit_12)))
(assert (or (not flush_12_2) (not exit_12)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_12_0 (=> (or stmt_12_0_1 stmt_12_0_4) (not thread_12_0)) (not flush_12_0)))
(assert (ite sb-full_12_1 (=> (or stmt_12_1_1 stmt_12_1_4) (not thread_12_1)) (not flush_12_1)))
(assert (=> (not sb-full_12_2) (not flush_12_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_12_0_0 (not check_12_0)) (not thread_12_0))) ; checkpoint 0: thread 0
(assert (=> (and block_12_0_1 (not check_12_0)) (not thread_12_1))) ; checkpoint 0: thread 1
(assert (=> (and block_12_0_2 (not check_12_0)) (not thread_12_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_12_0 (not thread_12_0)))
(assert (=> halt_12_1 (not thread_12_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_11_0_0 (and (= accu_12_0 (bvadd accu_11_0 #x0001)) (= mem_12_0 mem_11_0) (= sb-adr_12_0 sb-adr_11_0) (= sb-val_12_0 sb-val_11_0) (= sb-full_12_0 sb-full_11_0) (and (not stmt_12_0_0) stmt_12_0_1 (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4)) (= block_12_0_0 (ite check_11_0 false block_11_0_0)) (= halt_12_0 halt_11_0) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_0_1 (and (= accu_12_0 accu_11_0) (= mem_12_0 mem_11_0) (= sb-adr_12_0 #x0000) (= sb-val_12_0 accu_11_0) sb-full_12_0 (and (not stmt_12_0_0) (not stmt_12_0_1) stmt_12_0_2 (not stmt_12_0_3) (not stmt_12_0_4)) (= block_12_0_0 (ite check_11_0 false block_11_0_0)) (= halt_12_0 halt_11_0) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_0_2 (and (= accu_12_0 (ite (and sb-full_11_0 (= sb-adr_11_0 #x0001)) sb-val_11_0 (select heap_11 #x0001))) (= mem_12_0 mem_11_0) (= sb-adr_12_0 sb-adr_11_0) (= sb-val_12_0 sb-val_11_0) (= sb-full_12_0 sb-full_11_0) (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) stmt_12_0_3 (not stmt_12_0_4)) (= block_12_0_0 (ite check_11_0 false block_11_0_0)) (= halt_12_0 halt_11_0) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_0_3 (and (= accu_12_0 accu_11_0) (= mem_12_0 mem_11_0) (= sb-adr_12_0 sb-adr_11_0) (= sb-val_12_0 sb-val_11_0) (= sb-full_12_0 sb-full_11_0) (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) stmt_12_0_4) block_12_0_0 (= halt_12_0 halt_11_0) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_0_4 (and (= accu_12_0 accu_11_0) (= mem_12_0 mem_11_0) (= sb-adr_12_0 sb-adr_11_0) (= sb-val_12_0 sb-val_11_0) (= sb-full_12_0 sb-full_11_0) (and (not stmt_12_0_0) (not stmt_12_0_1) (not stmt_12_0_2) (not stmt_12_0_3) (not stmt_12_0_4)) (= block_12_0_0 (ite check_11_0 false block_11_0_0)) (and halt_12_0 (ite (and halt_12_1 halt_12_2) (and exit_12 (= exit-code #x0000)) (not exit_12))) (= heap_12 heap_11))))

(assert (=> (not thread_11_0) (and (= accu_12_0 accu_11_0) (= mem_12_0 mem_11_0) (= sb-adr_12_0 sb-adr_11_0) (= sb-val_12_0 sb-val_11_0) (= sb-full_12_0 (ite flush_11_0 false sb-full_11_0)) (and (= stmt_12_0_0 stmt_11_0_0) (= stmt_12_0_1 stmt_11_0_1) (= stmt_12_0_2 stmt_11_0_2) (= stmt_12_0_3 stmt_11_0_3) (= stmt_12_0_4 stmt_11_0_4)) (= block_12_0_0 (ite check_11_0 false block_11_0_0)) (= halt_12_0 halt_11_0))))

(assert (=> flush_11_0 (and (= heap_12 (store heap_11 sb-adr_11_0 sb-val_11_0)) (not exit_12))))

; thread 1
(assert (=> exec_11_1_0 (and (= accu_12_1 (bvadd accu_11_1 #x0001)) (= mem_12_1 mem_11_1) (= sb-adr_12_1 sb-adr_11_1) (= sb-val_12_1 sb-val_11_1) (= sb-full_12_1 sb-full_11_1) (and (not stmt_12_1_0) stmt_12_1_1 (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4)) (= block_12_0_1 (ite check_11_0 false block_11_0_1)) (= halt_12_1 halt_11_1) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_1_1 (and (= accu_12_1 accu_11_1) (= mem_12_1 mem_11_1) (= sb-adr_12_1 #x0001) (= sb-val_12_1 accu_11_1) sb-full_12_1 (and (not stmt_12_1_0) (not stmt_12_1_1) stmt_12_1_2 (not stmt_12_1_3) (not stmt_12_1_4)) (= block_12_0_1 (ite check_11_0 false block_11_0_1)) (= halt_12_1 halt_11_1) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_1_2 (and (= accu_12_1 (ite (and sb-full_11_1 (= sb-adr_11_1 #x0000)) sb-val_11_1 (select heap_11 #x0000))) (= mem_12_1 mem_11_1) (= sb-adr_12_1 sb-adr_11_1) (= sb-val_12_1 sb-val_11_1) (= sb-full_12_1 sb-full_11_1) (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) stmt_12_1_3 (not stmt_12_1_4)) (= block_12_0_1 (ite check_11_0 false block_11_0_1)) (= halt_12_1 halt_11_1) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_1_3 (and (= accu_12_1 accu_11_1) (= mem_12_1 mem_11_1) (= sb-adr_12_1 sb-adr_11_1) (= sb-val_12_1 sb-val_11_1) (= sb-full_12_1 sb-full_11_1) (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) stmt_12_1_4) block_12_0_1 (= halt_12_1 halt_11_1) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_1_4 (and (= accu_12_1 accu_11_1) (= mem_12_1 mem_11_1) (= sb-adr_12_1 sb-adr_11_1) (= sb-val_12_1 sb-val_11_1) (= sb-full_12_1 sb-full_11_1) (and (not stmt_12_1_0) (not stmt_12_1_1) (not stmt_12_1_2) (not stmt_12_1_3) (not stmt_12_1_4)) (= block_12_0_1 (ite check_11_0 false block_11_0_1)) (and halt_12_1 (ite (and halt_12_0 halt_12_2) (and exit_12 (= exit-code #x0000)) (not exit_12))) (= heap_12 heap_11))))

(assert (=> (not thread_11_1) (and (= accu_12_1 accu_11_1) (= mem_12_1 mem_11_1) (= sb-adr_12_1 sb-adr_11_1) (= sb-val_12_1 sb-val_11_1) (= sb-full_12_1 (ite flush_11_1 false sb-full_11_1)) (and (= stmt_12_1_0 stmt_11_1_0) (= stmt_12_1_1 stmt_11_1_1) (= stmt_12_1_2 stmt_11_1_2) (= stmt_12_1_3 stmt_11_1_3) (= stmt_12_1_4 stmt_11_1_4)) (= block_12_0_1 (ite check_11_0 false block_11_0_1)) (= halt_12_1 halt_11_1))))

(assert (=> flush_11_1 (and (= heap_12 (store heap_11 sb-adr_11_1 sb-val_11_1)) (not exit_12))))

; thread 2
(assert (=> exec_11_2_0 (and (= accu_12_2 accu_11_2) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) stmt_12_2_1 (not stmt_12_2_2) (not stmt_12_2_3) (not stmt_12_2_4) (not stmt_12_2_5)) block_12_0_2 (= halt_12_2 halt_11_2) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_2_1 (and (= accu_12_2 (bvadd accu_11_2 (ite (and sb-full_11_2 (= sb-adr_11_2 #x0000)) sb-val_11_2 (select heap_11 #x0000)))) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) (not stmt_12_2_1) stmt_12_2_2 (not stmt_12_2_3) (not stmt_12_2_4) (not stmt_12_2_5)) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_2_2 (and (= accu_12_2 (bvadd accu_11_2 (ite (and sb-full_11_2 (= sb-adr_11_2 #x0001)) sb-val_11_2 (select heap_11 #x0001)))) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) (not stmt_12_2_1) (not stmt_12_2_2) stmt_12_2_3 (not stmt_12_2_4) (not stmt_12_2_5)) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_2_3 (and (= accu_12_2 accu_11_2) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) (not stmt_12_2_1) (not stmt_12_2_2) (not stmt_12_2_3) (ite (= accu_11_2 #x0000) (not stmt_12_2_4) stmt_12_2_4) (ite (= accu_11_2 #x0000) stmt_12_2_5 (not stmt_12_2_5))) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2) (= heap_12 heap_11) (not exit_12))))

(assert (=> exec_11_2_4 (and (= accu_12_2 accu_11_2) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) (not stmt_12_2_1) (not stmt_12_2_2) (not stmt_12_2_3) stmt_12_2_4 (not stmt_12_2_5)) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2) (= heap_12 heap_11) exit_12 (= exit-code #x0000))))

(assert (=> exec_11_2_5 (and (= accu_12_2 accu_11_2) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 sb-full_11_2) (and (not stmt_12_2_0) (not stmt_12_2_1) (not stmt_12_2_2) (not stmt_12_2_3) (not stmt_12_2_4) stmt_12_2_5) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2) (= heap_12 heap_11) exit_12 (= exit-code #x0001))))

(assert (=> (not thread_11_2) (and (= accu_12_2 accu_11_2) (= mem_12_2 mem_11_2) (= sb-adr_12_2 sb-adr_11_2) (= sb-val_12_2 sb-val_11_2) (= sb-full_12_2 (ite flush_11_2 false sb-full_11_2)) (and (= stmt_12_2_0 stmt_11_2_0) (= stmt_12_2_1 stmt_11_2_1) (= stmt_12_2_2 stmt_11_2_2) (= stmt_12_2_3 stmt_11_2_3) (= stmt_12_2_4 stmt_11_2_4) (= stmt_12_2_5 stmt_11_2_5)) (= block_12_0_2 (ite check_11_0 false block_11_0_2)) (= halt_12_2 halt_11_2))))

(assert (=> flush_11_2 (and (= heap_12 (store heap_11 sb-adr_11_2 sb-val_11_2)) (not exit_12))))

; exited
(assert (=> exit_11 (and (= heap_12 heap_11) exit_12)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 13
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_13_0 () (_ BitVec 16))
(declare-fun accu_13_1 () (_ BitVec 16))
(declare-fun accu_13_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_13_0 () (_ BitVec 16))
(declare-fun mem_13_1 () (_ BitVec 16))
(declare-fun mem_13_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_13_0 () (_ BitVec 16))
(declare-fun sb-adr_13_1 () (_ BitVec 16))
(declare-fun sb-adr_13_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_13_0 () (_ BitVec 16))
(declare-fun sb-val_13_1 () (_ BitVec 16))
(declare-fun sb-val_13_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_13_0 () Bool)
(declare-fun sb-full_13_1 () Bool)
(declare-fun sb-full_13_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_13_0_0 () Bool)
(declare-fun stmt_13_0_1 () Bool)
(declare-fun stmt_13_0_2 () Bool)
(declare-fun stmt_13_0_3 () Bool)
(declare-fun stmt_13_0_4 () Bool)

(declare-fun stmt_13_1_0 () Bool)
(declare-fun stmt_13_1_1 () Bool)
(declare-fun stmt_13_1_2 () Bool)
(declare-fun stmt_13_1_3 () Bool)
(declare-fun stmt_13_1_4 () Bool)

(declare-fun stmt_13_2_0 () Bool)
(declare-fun stmt_13_2_1 () Bool)
(declare-fun stmt_13_2_2 () Bool)
(declare-fun stmt_13_2_3 () Bool)
(declare-fun stmt_13_2_4 () Bool)
(declare-fun stmt_13_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_13_0_0 () Bool)
(declare-fun block_13_0_1 () Bool)
(declare-fun block_13_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_13_0 () Bool)
(declare-fun halt_13_1 () Bool)
(declare-fun halt_13_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_13 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_13 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_13_0 () Bool)
(declare-fun thread_13_1 () Bool)
(declare-fun thread_13_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_13_0_0 () Bool)
(declare-fun exec_13_0_1 () Bool)
(declare-fun exec_13_0_2 () Bool)
(declare-fun exec_13_0_3 () Bool)
(declare-fun exec_13_0_4 () Bool)

(declare-fun exec_13_1_0 () Bool)
(declare-fun exec_13_1_1 () Bool)
(declare-fun exec_13_1_2 () Bool)
(declare-fun exec_13_1_3 () Bool)
(declare-fun exec_13_1_4 () Bool)

(declare-fun exec_13_2_0 () Bool)
(declare-fun exec_13_2_1 () Bool)
(declare-fun exec_13_2_2 () Bool)
(declare-fun exec_13_2_3 () Bool)
(declare-fun exec_13_2_4 () Bool)
(declare-fun exec_13_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_13_0 () Bool)
(declare-fun flush_13_1 () Bool)
(declare-fun flush_13_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_13_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_13_0_0 (and stmt_13_0_0 thread_13_0)))
(assert (= exec_13_0_1 (and stmt_13_0_1 thread_13_0)))
(assert (= exec_13_0_2 (and stmt_13_0_2 thread_13_0)))
(assert (= exec_13_0_3 (and stmt_13_0_3 thread_13_0)))
(assert (= exec_13_0_4 (and stmt_13_0_4 thread_13_0)))

(assert (= exec_13_1_0 (and stmt_13_1_0 thread_13_1)))
(assert (= exec_13_1_1 (and stmt_13_1_1 thread_13_1)))
(assert (= exec_13_1_2 (and stmt_13_1_2 thread_13_1)))
(assert (= exec_13_1_3 (and stmt_13_1_3 thread_13_1)))
(assert (= exec_13_1_4 (and stmt_13_1_4 thread_13_1)))

(assert (= exec_13_2_0 (and stmt_13_2_0 thread_13_2)))
(assert (= exec_13_2_1 (and stmt_13_2_1 thread_13_2)))
(assert (= exec_13_2_2 (and stmt_13_2_2 thread_13_2)))
(assert (= exec_13_2_3 (and stmt_13_2_3 thread_13_2)))
(assert (= exec_13_2_4 (and stmt_13_2_4 thread_13_2)))
(assert (= exec_13_2_5 (and stmt_13_2_5 thread_13_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_13_0 (and block_13_0_0 block_13_0_1 block_13_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_13_0 flush_13_0 thread_13_1 flush_13_1 thread_13_2 flush_13_2 exit_13))
(assert (or (not thread_13_0) (not flush_13_0)))
(assert (or (not thread_13_0) (not thread_13_1)))
(assert (or (not thread_13_0) (not flush_13_1)))
(assert (or (not thread_13_0) (not thread_13_2)))
(assert (or (not thread_13_0) (not flush_13_2)))
(assert (or (not thread_13_0) (not exit_13)))
(assert (or (not flush_13_0) (not thread_13_1)))
(assert (or (not flush_13_0) (not flush_13_1)))
(assert (or (not flush_13_0) (not thread_13_2)))
(assert (or (not flush_13_0) (not flush_13_2)))
(assert (or (not flush_13_0) (not exit_13)))
(assert (or (not thread_13_1) (not flush_13_1)))
(assert (or (not thread_13_1) (not thread_13_2)))
(assert (or (not thread_13_1) (not flush_13_2)))
(assert (or (not thread_13_1) (not exit_13)))
(assert (or (not flush_13_1) (not thread_13_2)))
(assert (or (not flush_13_1) (not flush_13_2)))
(assert (or (not flush_13_1) (not exit_13)))
(assert (or (not thread_13_2) (not flush_13_2)))
(assert (or (not thread_13_2) (not exit_13)))
(assert (or (not flush_13_2) (not exit_13)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_13_0 (=> (or stmt_13_0_1 stmt_13_0_4) (not thread_13_0)) (not flush_13_0)))
(assert (ite sb-full_13_1 (=> (or stmt_13_1_1 stmt_13_1_4) (not thread_13_1)) (not flush_13_1)))
(assert (=> (not sb-full_13_2) (not flush_13_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_13_0_0 (not check_13_0)) (not thread_13_0))) ; checkpoint 0: thread 0
(assert (=> (and block_13_0_1 (not check_13_0)) (not thread_13_1))) ; checkpoint 0: thread 1
(assert (=> (and block_13_0_2 (not check_13_0)) (not thread_13_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_13_0 (not thread_13_0)))
(assert (=> halt_13_1 (not thread_13_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_12_0_0 (and (= accu_13_0 (bvadd accu_12_0 #x0001)) (= mem_13_0 mem_12_0) (= sb-adr_13_0 sb-adr_12_0) (= sb-val_13_0 sb-val_12_0) (= sb-full_13_0 sb-full_12_0) (and (not stmt_13_0_0) stmt_13_0_1 (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4)) (= block_13_0_0 (ite check_12_0 false block_12_0_0)) (= halt_13_0 halt_12_0) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_0_1 (and (= accu_13_0 accu_12_0) (= mem_13_0 mem_12_0) (= sb-adr_13_0 #x0000) (= sb-val_13_0 accu_12_0) sb-full_13_0 (and (not stmt_13_0_0) (not stmt_13_0_1) stmt_13_0_2 (not stmt_13_0_3) (not stmt_13_0_4)) (= block_13_0_0 (ite check_12_0 false block_12_0_0)) (= halt_13_0 halt_12_0) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_0_2 (and (= accu_13_0 (ite (and sb-full_12_0 (= sb-adr_12_0 #x0001)) sb-val_12_0 (select heap_12 #x0001))) (= mem_13_0 mem_12_0) (= sb-adr_13_0 sb-adr_12_0) (= sb-val_13_0 sb-val_12_0) (= sb-full_13_0 sb-full_12_0) (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) stmt_13_0_3 (not stmt_13_0_4)) (= block_13_0_0 (ite check_12_0 false block_12_0_0)) (= halt_13_0 halt_12_0) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_0_3 (and (= accu_13_0 accu_12_0) (= mem_13_0 mem_12_0) (= sb-adr_13_0 sb-adr_12_0) (= sb-val_13_0 sb-val_12_0) (= sb-full_13_0 sb-full_12_0) (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) stmt_13_0_4) block_13_0_0 (= halt_13_0 halt_12_0) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_0_4 (and (= accu_13_0 accu_12_0) (= mem_13_0 mem_12_0) (= sb-adr_13_0 sb-adr_12_0) (= sb-val_13_0 sb-val_12_0) (= sb-full_13_0 sb-full_12_0) (and (not stmt_13_0_0) (not stmt_13_0_1) (not stmt_13_0_2) (not stmt_13_0_3) (not stmt_13_0_4)) (= block_13_0_0 (ite check_12_0 false block_12_0_0)) (and halt_13_0 (ite (and halt_13_1 halt_13_2) (and exit_13 (= exit-code #x0000)) (not exit_13))) (= heap_13 heap_12))))

(assert (=> (not thread_12_0) (and (= accu_13_0 accu_12_0) (= mem_13_0 mem_12_0) (= sb-adr_13_0 sb-adr_12_0) (= sb-val_13_0 sb-val_12_0) (= sb-full_13_0 (ite flush_12_0 false sb-full_12_0)) (and (= stmt_13_0_0 stmt_12_0_0) (= stmt_13_0_1 stmt_12_0_1) (= stmt_13_0_2 stmt_12_0_2) (= stmt_13_0_3 stmt_12_0_3) (= stmt_13_0_4 stmt_12_0_4)) (= block_13_0_0 (ite check_12_0 false block_12_0_0)) (= halt_13_0 halt_12_0))))

(assert (=> flush_12_0 (and (= heap_13 (store heap_12 sb-adr_12_0 sb-val_12_0)) (not exit_13))))

; thread 1
(assert (=> exec_12_1_0 (and (= accu_13_1 (bvadd accu_12_1 #x0001)) (= mem_13_1 mem_12_1) (= sb-adr_13_1 sb-adr_12_1) (= sb-val_13_1 sb-val_12_1) (= sb-full_13_1 sb-full_12_1) (and (not stmt_13_1_0) stmt_13_1_1 (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4)) (= block_13_0_1 (ite check_12_0 false block_12_0_1)) (= halt_13_1 halt_12_1) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_1_1 (and (= accu_13_1 accu_12_1) (= mem_13_1 mem_12_1) (= sb-adr_13_1 #x0001) (= sb-val_13_1 accu_12_1) sb-full_13_1 (and (not stmt_13_1_0) (not stmt_13_1_1) stmt_13_1_2 (not stmt_13_1_3) (not stmt_13_1_4)) (= block_13_0_1 (ite check_12_0 false block_12_0_1)) (= halt_13_1 halt_12_1) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_1_2 (and (= accu_13_1 (ite (and sb-full_12_1 (= sb-adr_12_1 #x0000)) sb-val_12_1 (select heap_12 #x0000))) (= mem_13_1 mem_12_1) (= sb-adr_13_1 sb-adr_12_1) (= sb-val_13_1 sb-val_12_1) (= sb-full_13_1 sb-full_12_1) (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) stmt_13_1_3 (not stmt_13_1_4)) (= block_13_0_1 (ite check_12_0 false block_12_0_1)) (= halt_13_1 halt_12_1) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_1_3 (and (= accu_13_1 accu_12_1) (= mem_13_1 mem_12_1) (= sb-adr_13_1 sb-adr_12_1) (= sb-val_13_1 sb-val_12_1) (= sb-full_13_1 sb-full_12_1) (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) stmt_13_1_4) block_13_0_1 (= halt_13_1 halt_12_1) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_1_4 (and (= accu_13_1 accu_12_1) (= mem_13_1 mem_12_1) (= sb-adr_13_1 sb-adr_12_1) (= sb-val_13_1 sb-val_12_1) (= sb-full_13_1 sb-full_12_1) (and (not stmt_13_1_0) (not stmt_13_1_1) (not stmt_13_1_2) (not stmt_13_1_3) (not stmt_13_1_4)) (= block_13_0_1 (ite check_12_0 false block_12_0_1)) (and halt_13_1 (ite (and halt_13_0 halt_13_2) (and exit_13 (= exit-code #x0000)) (not exit_13))) (= heap_13 heap_12))))

(assert (=> (not thread_12_1) (and (= accu_13_1 accu_12_1) (= mem_13_1 mem_12_1) (= sb-adr_13_1 sb-adr_12_1) (= sb-val_13_1 sb-val_12_1) (= sb-full_13_1 (ite flush_12_1 false sb-full_12_1)) (and (= stmt_13_1_0 stmt_12_1_0) (= stmt_13_1_1 stmt_12_1_1) (= stmt_13_1_2 stmt_12_1_2) (= stmt_13_1_3 stmt_12_1_3) (= stmt_13_1_4 stmt_12_1_4)) (= block_13_0_1 (ite check_12_0 false block_12_0_1)) (= halt_13_1 halt_12_1))))

(assert (=> flush_12_1 (and (= heap_13 (store heap_12 sb-adr_12_1 sb-val_12_1)) (not exit_13))))

; thread 2
(assert (=> exec_12_2_0 (and (= accu_13_2 accu_12_2) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) stmt_13_2_1 (not stmt_13_2_2) (not stmt_13_2_3) (not stmt_13_2_4) (not stmt_13_2_5)) block_13_0_2 (= halt_13_2 halt_12_2) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_2_1 (and (= accu_13_2 (bvadd accu_12_2 (ite (and sb-full_12_2 (= sb-adr_12_2 #x0000)) sb-val_12_2 (select heap_12 #x0000)))) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) (not stmt_13_2_1) stmt_13_2_2 (not stmt_13_2_3) (not stmt_13_2_4) (not stmt_13_2_5)) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_2_2 (and (= accu_13_2 (bvadd accu_12_2 (ite (and sb-full_12_2 (= sb-adr_12_2 #x0001)) sb-val_12_2 (select heap_12 #x0001)))) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) (not stmt_13_2_1) (not stmt_13_2_2) stmt_13_2_3 (not stmt_13_2_4) (not stmt_13_2_5)) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_2_3 (and (= accu_13_2 accu_12_2) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) (not stmt_13_2_1) (not stmt_13_2_2) (not stmt_13_2_3) (ite (= accu_12_2 #x0000) (not stmt_13_2_4) stmt_13_2_4) (ite (= accu_12_2 #x0000) stmt_13_2_5 (not stmt_13_2_5))) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2) (= heap_13 heap_12) (not exit_13))))

(assert (=> exec_12_2_4 (and (= accu_13_2 accu_12_2) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) (not stmt_13_2_1) (not stmt_13_2_2) (not stmt_13_2_3) stmt_13_2_4 (not stmt_13_2_5)) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2) (= heap_13 heap_12) exit_13 (= exit-code #x0000))))

(assert (=> exec_12_2_5 (and (= accu_13_2 accu_12_2) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 sb-full_12_2) (and (not stmt_13_2_0) (not stmt_13_2_1) (not stmt_13_2_2) (not stmt_13_2_3) (not stmt_13_2_4) stmt_13_2_5) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2) (= heap_13 heap_12) exit_13 (= exit-code #x0001))))

(assert (=> (not thread_12_2) (and (= accu_13_2 accu_12_2) (= mem_13_2 mem_12_2) (= sb-adr_13_2 sb-adr_12_2) (= sb-val_13_2 sb-val_12_2) (= sb-full_13_2 (ite flush_12_2 false sb-full_12_2)) (and (= stmt_13_2_0 stmt_12_2_0) (= stmt_13_2_1 stmt_12_2_1) (= stmt_13_2_2 stmt_12_2_2) (= stmt_13_2_3 stmt_12_2_3) (= stmt_13_2_4 stmt_12_2_4) (= stmt_13_2_5 stmt_12_2_5)) (= block_13_0_2 (ite check_12_0 false block_12_0_2)) (= halt_13_2 halt_12_2))))

(assert (=> flush_12_2 (and (= heap_13 (store heap_12 sb-adr_12_2 sb-val_12_2)) (not exit_13))))

; exited
(assert (=> exit_12 (and (= heap_13 heap_12) exit_13)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 14
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_14_0 () (_ BitVec 16))
(declare-fun accu_14_1 () (_ BitVec 16))
(declare-fun accu_14_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_14_0 () (_ BitVec 16))
(declare-fun mem_14_1 () (_ BitVec 16))
(declare-fun mem_14_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_14_0 () (_ BitVec 16))
(declare-fun sb-adr_14_1 () (_ BitVec 16))
(declare-fun sb-adr_14_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_14_0 () (_ BitVec 16))
(declare-fun sb-val_14_1 () (_ BitVec 16))
(declare-fun sb-val_14_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_14_0 () Bool)
(declare-fun sb-full_14_1 () Bool)
(declare-fun sb-full_14_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_14_0_0 () Bool)
(declare-fun stmt_14_0_1 () Bool)
(declare-fun stmt_14_0_2 () Bool)
(declare-fun stmt_14_0_3 () Bool)
(declare-fun stmt_14_0_4 () Bool)

(declare-fun stmt_14_1_0 () Bool)
(declare-fun stmt_14_1_1 () Bool)
(declare-fun stmt_14_1_2 () Bool)
(declare-fun stmt_14_1_3 () Bool)
(declare-fun stmt_14_1_4 () Bool)

(declare-fun stmt_14_2_0 () Bool)
(declare-fun stmt_14_2_1 () Bool)
(declare-fun stmt_14_2_2 () Bool)
(declare-fun stmt_14_2_3 () Bool)
(declare-fun stmt_14_2_4 () Bool)
(declare-fun stmt_14_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_14_0_0 () Bool)
(declare-fun block_14_0_1 () Bool)
(declare-fun block_14_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_14_0 () Bool)
(declare-fun halt_14_1 () Bool)
(declare-fun halt_14_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_14 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_14 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_14_0 () Bool)
(declare-fun thread_14_1 () Bool)
(declare-fun thread_14_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_14_0_0 () Bool)
(declare-fun exec_14_0_1 () Bool)
(declare-fun exec_14_0_2 () Bool)
(declare-fun exec_14_0_3 () Bool)
(declare-fun exec_14_0_4 () Bool)

(declare-fun exec_14_1_0 () Bool)
(declare-fun exec_14_1_1 () Bool)
(declare-fun exec_14_1_2 () Bool)
(declare-fun exec_14_1_3 () Bool)
(declare-fun exec_14_1_4 () Bool)

(declare-fun exec_14_2_0 () Bool)
(declare-fun exec_14_2_1 () Bool)
(declare-fun exec_14_2_2 () Bool)
(declare-fun exec_14_2_3 () Bool)
(declare-fun exec_14_2_4 () Bool)
(declare-fun exec_14_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_14_0 () Bool)
(declare-fun flush_14_1 () Bool)
(declare-fun flush_14_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_14_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_14_0_0 (and stmt_14_0_0 thread_14_0)))
(assert (= exec_14_0_1 (and stmt_14_0_1 thread_14_0)))
(assert (= exec_14_0_2 (and stmt_14_0_2 thread_14_0)))
(assert (= exec_14_0_3 (and stmt_14_0_3 thread_14_0)))
(assert (= exec_14_0_4 (and stmt_14_0_4 thread_14_0)))

(assert (= exec_14_1_0 (and stmt_14_1_0 thread_14_1)))
(assert (= exec_14_1_1 (and stmt_14_1_1 thread_14_1)))
(assert (= exec_14_1_2 (and stmt_14_1_2 thread_14_1)))
(assert (= exec_14_1_3 (and stmt_14_1_3 thread_14_1)))
(assert (= exec_14_1_4 (and stmt_14_1_4 thread_14_1)))

(assert (= exec_14_2_0 (and stmt_14_2_0 thread_14_2)))
(assert (= exec_14_2_1 (and stmt_14_2_1 thread_14_2)))
(assert (= exec_14_2_2 (and stmt_14_2_2 thread_14_2)))
(assert (= exec_14_2_3 (and stmt_14_2_3 thread_14_2)))
(assert (= exec_14_2_4 (and stmt_14_2_4 thread_14_2)))
(assert (= exec_14_2_5 (and stmt_14_2_5 thread_14_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_14_0 (and block_14_0_0 block_14_0_1 block_14_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_14_0 flush_14_0 thread_14_1 flush_14_1 thread_14_2 flush_14_2 exit_14))
(assert (or (not thread_14_0) (not flush_14_0)))
(assert (or (not thread_14_0) (not thread_14_1)))
(assert (or (not thread_14_0) (not flush_14_1)))
(assert (or (not thread_14_0) (not thread_14_2)))
(assert (or (not thread_14_0) (not flush_14_2)))
(assert (or (not thread_14_0) (not exit_14)))
(assert (or (not flush_14_0) (not thread_14_1)))
(assert (or (not flush_14_0) (not flush_14_1)))
(assert (or (not flush_14_0) (not thread_14_2)))
(assert (or (not flush_14_0) (not flush_14_2)))
(assert (or (not flush_14_0) (not exit_14)))
(assert (or (not thread_14_1) (not flush_14_1)))
(assert (or (not thread_14_1) (not thread_14_2)))
(assert (or (not thread_14_1) (not flush_14_2)))
(assert (or (not thread_14_1) (not exit_14)))
(assert (or (not flush_14_1) (not thread_14_2)))
(assert (or (not flush_14_1) (not flush_14_2)))
(assert (or (not flush_14_1) (not exit_14)))
(assert (or (not thread_14_2) (not flush_14_2)))
(assert (or (not thread_14_2) (not exit_14)))
(assert (or (not flush_14_2) (not exit_14)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_14_0 (=> (or stmt_14_0_1 stmt_14_0_4) (not thread_14_0)) (not flush_14_0)))
(assert (ite sb-full_14_1 (=> (or stmt_14_1_1 stmt_14_1_4) (not thread_14_1)) (not flush_14_1)))
(assert (=> (not sb-full_14_2) (not flush_14_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_14_0_0 (not check_14_0)) (not thread_14_0))) ; checkpoint 0: thread 0
(assert (=> (and block_14_0_1 (not check_14_0)) (not thread_14_1))) ; checkpoint 0: thread 1
(assert (=> (and block_14_0_2 (not check_14_0)) (not thread_14_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_14_0 (not thread_14_0)))
(assert (=> halt_14_1 (not thread_14_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_13_0_0 (and (= accu_14_0 (bvadd accu_13_0 #x0001)) (= mem_14_0 mem_13_0) (= sb-adr_14_0 sb-adr_13_0) (= sb-val_14_0 sb-val_13_0) (= sb-full_14_0 sb-full_13_0) (and (not stmt_14_0_0) stmt_14_0_1 (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4)) (= block_14_0_0 (ite check_13_0 false block_13_0_0)) (= halt_14_0 halt_13_0) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_0_1 (and (= accu_14_0 accu_13_0) (= mem_14_0 mem_13_0) (= sb-adr_14_0 #x0000) (= sb-val_14_0 accu_13_0) sb-full_14_0 (and (not stmt_14_0_0) (not stmt_14_0_1) stmt_14_0_2 (not stmt_14_0_3) (not stmt_14_0_4)) (= block_14_0_0 (ite check_13_0 false block_13_0_0)) (= halt_14_0 halt_13_0) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_0_2 (and (= accu_14_0 (ite (and sb-full_13_0 (= sb-adr_13_0 #x0001)) sb-val_13_0 (select heap_13 #x0001))) (= mem_14_0 mem_13_0) (= sb-adr_14_0 sb-adr_13_0) (= sb-val_14_0 sb-val_13_0) (= sb-full_14_0 sb-full_13_0) (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) stmt_14_0_3 (not stmt_14_0_4)) (= block_14_0_0 (ite check_13_0 false block_13_0_0)) (= halt_14_0 halt_13_0) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_0_3 (and (= accu_14_0 accu_13_0) (= mem_14_0 mem_13_0) (= sb-adr_14_0 sb-adr_13_0) (= sb-val_14_0 sb-val_13_0) (= sb-full_14_0 sb-full_13_0) (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) stmt_14_0_4) block_14_0_0 (= halt_14_0 halt_13_0) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_0_4 (and (= accu_14_0 accu_13_0) (= mem_14_0 mem_13_0) (= sb-adr_14_0 sb-adr_13_0) (= sb-val_14_0 sb-val_13_0) (= sb-full_14_0 sb-full_13_0) (and (not stmt_14_0_0) (not stmt_14_0_1) (not stmt_14_0_2) (not stmt_14_0_3) (not stmt_14_0_4)) (= block_14_0_0 (ite check_13_0 false block_13_0_0)) (and halt_14_0 (ite (and halt_14_1 halt_14_2) (and exit_14 (= exit-code #x0000)) (not exit_14))) (= heap_14 heap_13))))

(assert (=> (not thread_13_0) (and (= accu_14_0 accu_13_0) (= mem_14_0 mem_13_0) (= sb-adr_14_0 sb-adr_13_0) (= sb-val_14_0 sb-val_13_0) (= sb-full_14_0 (ite flush_13_0 false sb-full_13_0)) (and (= stmt_14_0_0 stmt_13_0_0) (= stmt_14_0_1 stmt_13_0_1) (= stmt_14_0_2 stmt_13_0_2) (= stmt_14_0_3 stmt_13_0_3) (= stmt_14_0_4 stmt_13_0_4)) (= block_14_0_0 (ite check_13_0 false block_13_0_0)) (= halt_14_0 halt_13_0))))

(assert (=> flush_13_0 (and (= heap_14 (store heap_13 sb-adr_13_0 sb-val_13_0)) (not exit_14))))

; thread 1
(assert (=> exec_13_1_0 (and (= accu_14_1 (bvadd accu_13_1 #x0001)) (= mem_14_1 mem_13_1) (= sb-adr_14_1 sb-adr_13_1) (= sb-val_14_1 sb-val_13_1) (= sb-full_14_1 sb-full_13_1) (and (not stmt_14_1_0) stmt_14_1_1 (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4)) (= block_14_0_1 (ite check_13_0 false block_13_0_1)) (= halt_14_1 halt_13_1) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_1_1 (and (= accu_14_1 accu_13_1) (= mem_14_1 mem_13_1) (= sb-adr_14_1 #x0001) (= sb-val_14_1 accu_13_1) sb-full_14_1 (and (not stmt_14_1_0) (not stmt_14_1_1) stmt_14_1_2 (not stmt_14_1_3) (not stmt_14_1_4)) (= block_14_0_1 (ite check_13_0 false block_13_0_1)) (= halt_14_1 halt_13_1) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_1_2 (and (= accu_14_1 (ite (and sb-full_13_1 (= sb-adr_13_1 #x0000)) sb-val_13_1 (select heap_13 #x0000))) (= mem_14_1 mem_13_1) (= sb-adr_14_1 sb-adr_13_1) (= sb-val_14_1 sb-val_13_1) (= sb-full_14_1 sb-full_13_1) (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) stmt_14_1_3 (not stmt_14_1_4)) (= block_14_0_1 (ite check_13_0 false block_13_0_1)) (= halt_14_1 halt_13_1) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_1_3 (and (= accu_14_1 accu_13_1) (= mem_14_1 mem_13_1) (= sb-adr_14_1 sb-adr_13_1) (= sb-val_14_1 sb-val_13_1) (= sb-full_14_1 sb-full_13_1) (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) stmt_14_1_4) block_14_0_1 (= halt_14_1 halt_13_1) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_1_4 (and (= accu_14_1 accu_13_1) (= mem_14_1 mem_13_1) (= sb-adr_14_1 sb-adr_13_1) (= sb-val_14_1 sb-val_13_1) (= sb-full_14_1 sb-full_13_1) (and (not stmt_14_1_0) (not stmt_14_1_1) (not stmt_14_1_2) (not stmt_14_1_3) (not stmt_14_1_4)) (= block_14_0_1 (ite check_13_0 false block_13_0_1)) (and halt_14_1 (ite (and halt_14_0 halt_14_2) (and exit_14 (= exit-code #x0000)) (not exit_14))) (= heap_14 heap_13))))

(assert (=> (not thread_13_1) (and (= accu_14_1 accu_13_1) (= mem_14_1 mem_13_1) (= sb-adr_14_1 sb-adr_13_1) (= sb-val_14_1 sb-val_13_1) (= sb-full_14_1 (ite flush_13_1 false sb-full_13_1)) (and (= stmt_14_1_0 stmt_13_1_0) (= stmt_14_1_1 stmt_13_1_1) (= stmt_14_1_2 stmt_13_1_2) (= stmt_14_1_3 stmt_13_1_3) (= stmt_14_1_4 stmt_13_1_4)) (= block_14_0_1 (ite check_13_0 false block_13_0_1)) (= halt_14_1 halt_13_1))))

(assert (=> flush_13_1 (and (= heap_14 (store heap_13 sb-adr_13_1 sb-val_13_1)) (not exit_14))))

; thread 2
(assert (=> exec_13_2_0 (and (= accu_14_2 accu_13_2) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) stmt_14_2_1 (not stmt_14_2_2) (not stmt_14_2_3) (not stmt_14_2_4) (not stmt_14_2_5)) block_14_0_2 (= halt_14_2 halt_13_2) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_2_1 (and (= accu_14_2 (bvadd accu_13_2 (ite (and sb-full_13_2 (= sb-adr_13_2 #x0000)) sb-val_13_2 (select heap_13 #x0000)))) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) (not stmt_14_2_1) stmt_14_2_2 (not stmt_14_2_3) (not stmt_14_2_4) (not stmt_14_2_5)) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_2_2 (and (= accu_14_2 (bvadd accu_13_2 (ite (and sb-full_13_2 (= sb-adr_13_2 #x0001)) sb-val_13_2 (select heap_13 #x0001)))) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) (not stmt_14_2_1) (not stmt_14_2_2) stmt_14_2_3 (not stmt_14_2_4) (not stmt_14_2_5)) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_2_3 (and (= accu_14_2 accu_13_2) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) (not stmt_14_2_1) (not stmt_14_2_2) (not stmt_14_2_3) (ite (= accu_13_2 #x0000) (not stmt_14_2_4) stmt_14_2_4) (ite (= accu_13_2 #x0000) stmt_14_2_5 (not stmt_14_2_5))) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2) (= heap_14 heap_13) (not exit_14))))

(assert (=> exec_13_2_4 (and (= accu_14_2 accu_13_2) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) (not stmt_14_2_1) (not stmt_14_2_2) (not stmt_14_2_3) stmt_14_2_4 (not stmt_14_2_5)) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2) (= heap_14 heap_13) exit_14 (= exit-code #x0000))))

(assert (=> exec_13_2_5 (and (= accu_14_2 accu_13_2) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 sb-full_13_2) (and (not stmt_14_2_0) (not stmt_14_2_1) (not stmt_14_2_2) (not stmt_14_2_3) (not stmt_14_2_4) stmt_14_2_5) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2) (= heap_14 heap_13) exit_14 (= exit-code #x0001))))

(assert (=> (not thread_13_2) (and (= accu_14_2 accu_13_2) (= mem_14_2 mem_13_2) (= sb-adr_14_2 sb-adr_13_2) (= sb-val_14_2 sb-val_13_2) (= sb-full_14_2 (ite flush_13_2 false sb-full_13_2)) (and (= stmt_14_2_0 stmt_13_2_0) (= stmt_14_2_1 stmt_13_2_1) (= stmt_14_2_2 stmt_13_2_2) (= stmt_14_2_3 stmt_13_2_3) (= stmt_14_2_4 stmt_13_2_4) (= stmt_14_2_5 stmt_13_2_5)) (= block_14_0_2 (ite check_13_0 false block_13_0_2)) (= halt_14_2 halt_13_2))))

(assert (=> flush_13_2 (and (= heap_14 (store heap_13 sb-adr_13_2 sb-val_13_2)) (not exit_14))))

; exited
(assert (=> exit_13 (and (= heap_14 heap_13) exit_14)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 15
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_15_0 () (_ BitVec 16))
(declare-fun accu_15_1 () (_ BitVec 16))
(declare-fun accu_15_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_15_0 () (_ BitVec 16))
(declare-fun mem_15_1 () (_ BitVec 16))
(declare-fun mem_15_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_15_0 () (_ BitVec 16))
(declare-fun sb-adr_15_1 () (_ BitVec 16))
(declare-fun sb-adr_15_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_15_0 () (_ BitVec 16))
(declare-fun sb-val_15_1 () (_ BitVec 16))
(declare-fun sb-val_15_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_15_0 () Bool)
(declare-fun sb-full_15_1 () Bool)
(declare-fun sb-full_15_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_15_0_0 () Bool)
(declare-fun stmt_15_0_1 () Bool)
(declare-fun stmt_15_0_2 () Bool)
(declare-fun stmt_15_0_3 () Bool)
(declare-fun stmt_15_0_4 () Bool)

(declare-fun stmt_15_1_0 () Bool)
(declare-fun stmt_15_1_1 () Bool)
(declare-fun stmt_15_1_2 () Bool)
(declare-fun stmt_15_1_3 () Bool)
(declare-fun stmt_15_1_4 () Bool)

(declare-fun stmt_15_2_0 () Bool)
(declare-fun stmt_15_2_1 () Bool)
(declare-fun stmt_15_2_2 () Bool)
(declare-fun stmt_15_2_3 () Bool)
(declare-fun stmt_15_2_4 () Bool)
(declare-fun stmt_15_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_15_0_0 () Bool)
(declare-fun block_15_0_1 () Bool)
(declare-fun block_15_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_15_0 () Bool)
(declare-fun halt_15_1 () Bool)
(declare-fun halt_15_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_15 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_15 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_15_0 () Bool)
(declare-fun thread_15_1 () Bool)
(declare-fun thread_15_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_15_0_0 () Bool)
(declare-fun exec_15_0_1 () Bool)
(declare-fun exec_15_0_2 () Bool)
(declare-fun exec_15_0_3 () Bool)
(declare-fun exec_15_0_4 () Bool)

(declare-fun exec_15_1_0 () Bool)
(declare-fun exec_15_1_1 () Bool)
(declare-fun exec_15_1_2 () Bool)
(declare-fun exec_15_1_3 () Bool)
(declare-fun exec_15_1_4 () Bool)

(declare-fun exec_15_2_0 () Bool)
(declare-fun exec_15_2_1 () Bool)
(declare-fun exec_15_2_2 () Bool)
(declare-fun exec_15_2_3 () Bool)
(declare-fun exec_15_2_4 () Bool)
(declare-fun exec_15_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_15_0 () Bool)
(declare-fun flush_15_1 () Bool)
(declare-fun flush_15_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_15_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_15_0_0 (and stmt_15_0_0 thread_15_0)))
(assert (= exec_15_0_1 (and stmt_15_0_1 thread_15_0)))
(assert (= exec_15_0_2 (and stmt_15_0_2 thread_15_0)))
(assert (= exec_15_0_3 (and stmt_15_0_3 thread_15_0)))
(assert (= exec_15_0_4 (and stmt_15_0_4 thread_15_0)))

(assert (= exec_15_1_0 (and stmt_15_1_0 thread_15_1)))
(assert (= exec_15_1_1 (and stmt_15_1_1 thread_15_1)))
(assert (= exec_15_1_2 (and stmt_15_1_2 thread_15_1)))
(assert (= exec_15_1_3 (and stmt_15_1_3 thread_15_1)))
(assert (= exec_15_1_4 (and stmt_15_1_4 thread_15_1)))

(assert (= exec_15_2_0 (and stmt_15_2_0 thread_15_2)))
(assert (= exec_15_2_1 (and stmt_15_2_1 thread_15_2)))
(assert (= exec_15_2_2 (and stmt_15_2_2 thread_15_2)))
(assert (= exec_15_2_3 (and stmt_15_2_3 thread_15_2)))
(assert (= exec_15_2_4 (and stmt_15_2_4 thread_15_2)))
(assert (= exec_15_2_5 (and stmt_15_2_5 thread_15_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_15_0 (and block_15_0_0 block_15_0_1 block_15_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_15_0 flush_15_0 thread_15_1 flush_15_1 thread_15_2 flush_15_2 exit_15))
(assert (or (not thread_15_0) (not flush_15_0)))
(assert (or (not thread_15_0) (not thread_15_1)))
(assert (or (not thread_15_0) (not flush_15_1)))
(assert (or (not thread_15_0) (not thread_15_2)))
(assert (or (not thread_15_0) (not flush_15_2)))
(assert (or (not thread_15_0) (not exit_15)))
(assert (or (not flush_15_0) (not thread_15_1)))
(assert (or (not flush_15_0) (not flush_15_1)))
(assert (or (not flush_15_0) (not thread_15_2)))
(assert (or (not flush_15_0) (not flush_15_2)))
(assert (or (not flush_15_0) (not exit_15)))
(assert (or (not thread_15_1) (not flush_15_1)))
(assert (or (not thread_15_1) (not thread_15_2)))
(assert (or (not thread_15_1) (not flush_15_2)))
(assert (or (not thread_15_1) (not exit_15)))
(assert (or (not flush_15_1) (not thread_15_2)))
(assert (or (not flush_15_1) (not flush_15_2)))
(assert (or (not flush_15_1) (not exit_15)))
(assert (or (not thread_15_2) (not flush_15_2)))
(assert (or (not thread_15_2) (not exit_15)))
(assert (or (not flush_15_2) (not exit_15)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_15_0 (=> (or stmt_15_0_1 stmt_15_0_4) (not thread_15_0)) (not flush_15_0)))
(assert (ite sb-full_15_1 (=> (or stmt_15_1_1 stmt_15_1_4) (not thread_15_1)) (not flush_15_1)))
(assert (=> (not sb-full_15_2) (not flush_15_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_15_0_0 (not check_15_0)) (not thread_15_0))) ; checkpoint 0: thread 0
(assert (=> (and block_15_0_1 (not check_15_0)) (not thread_15_1))) ; checkpoint 0: thread 1
(assert (=> (and block_15_0_2 (not check_15_0)) (not thread_15_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_15_0 (not thread_15_0)))
(assert (=> halt_15_1 (not thread_15_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_14_0_0 (and (= accu_15_0 (bvadd accu_14_0 #x0001)) (= mem_15_0 mem_14_0) (= sb-adr_15_0 sb-adr_14_0) (= sb-val_15_0 sb-val_14_0) (= sb-full_15_0 sb-full_14_0) (and (not stmt_15_0_0) stmt_15_0_1 (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4)) (= block_15_0_0 (ite check_14_0 false block_14_0_0)) (= halt_15_0 halt_14_0) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_0_1 (and (= accu_15_0 accu_14_0) (= mem_15_0 mem_14_0) (= sb-adr_15_0 #x0000) (= sb-val_15_0 accu_14_0) sb-full_15_0 (and (not stmt_15_0_0) (not stmt_15_0_1) stmt_15_0_2 (not stmt_15_0_3) (not stmt_15_0_4)) (= block_15_0_0 (ite check_14_0 false block_14_0_0)) (= halt_15_0 halt_14_0) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_0_2 (and (= accu_15_0 (ite (and sb-full_14_0 (= sb-adr_14_0 #x0001)) sb-val_14_0 (select heap_14 #x0001))) (= mem_15_0 mem_14_0) (= sb-adr_15_0 sb-adr_14_0) (= sb-val_15_0 sb-val_14_0) (= sb-full_15_0 sb-full_14_0) (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) stmt_15_0_3 (not stmt_15_0_4)) (= block_15_0_0 (ite check_14_0 false block_14_0_0)) (= halt_15_0 halt_14_0) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_0_3 (and (= accu_15_0 accu_14_0) (= mem_15_0 mem_14_0) (= sb-adr_15_0 sb-adr_14_0) (= sb-val_15_0 sb-val_14_0) (= sb-full_15_0 sb-full_14_0) (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) stmt_15_0_4) block_15_0_0 (= halt_15_0 halt_14_0) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_0_4 (and (= accu_15_0 accu_14_0) (= mem_15_0 mem_14_0) (= sb-adr_15_0 sb-adr_14_0) (= sb-val_15_0 sb-val_14_0) (= sb-full_15_0 sb-full_14_0) (and (not stmt_15_0_0) (not stmt_15_0_1) (not stmt_15_0_2) (not stmt_15_0_3) (not stmt_15_0_4)) (= block_15_0_0 (ite check_14_0 false block_14_0_0)) (and halt_15_0 (ite (and halt_15_1 halt_15_2) (and exit_15 (= exit-code #x0000)) (not exit_15))) (= heap_15 heap_14))))

(assert (=> (not thread_14_0) (and (= accu_15_0 accu_14_0) (= mem_15_0 mem_14_0) (= sb-adr_15_0 sb-adr_14_0) (= sb-val_15_0 sb-val_14_0) (= sb-full_15_0 (ite flush_14_0 false sb-full_14_0)) (and (= stmt_15_0_0 stmt_14_0_0) (= stmt_15_0_1 stmt_14_0_1) (= stmt_15_0_2 stmt_14_0_2) (= stmt_15_0_3 stmt_14_0_3) (= stmt_15_0_4 stmt_14_0_4)) (= block_15_0_0 (ite check_14_0 false block_14_0_0)) (= halt_15_0 halt_14_0))))

(assert (=> flush_14_0 (and (= heap_15 (store heap_14 sb-adr_14_0 sb-val_14_0)) (not exit_15))))

; thread 1
(assert (=> exec_14_1_0 (and (= accu_15_1 (bvadd accu_14_1 #x0001)) (= mem_15_1 mem_14_1) (= sb-adr_15_1 sb-adr_14_1) (= sb-val_15_1 sb-val_14_1) (= sb-full_15_1 sb-full_14_1) (and (not stmt_15_1_0) stmt_15_1_1 (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4)) (= block_15_0_1 (ite check_14_0 false block_14_0_1)) (= halt_15_1 halt_14_1) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_1_1 (and (= accu_15_1 accu_14_1) (= mem_15_1 mem_14_1) (= sb-adr_15_1 #x0001) (= sb-val_15_1 accu_14_1) sb-full_15_1 (and (not stmt_15_1_0) (not stmt_15_1_1) stmt_15_1_2 (not stmt_15_1_3) (not stmt_15_1_4)) (= block_15_0_1 (ite check_14_0 false block_14_0_1)) (= halt_15_1 halt_14_1) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_1_2 (and (= accu_15_1 (ite (and sb-full_14_1 (= sb-adr_14_1 #x0000)) sb-val_14_1 (select heap_14 #x0000))) (= mem_15_1 mem_14_1) (= sb-adr_15_1 sb-adr_14_1) (= sb-val_15_1 sb-val_14_1) (= sb-full_15_1 sb-full_14_1) (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) stmt_15_1_3 (not stmt_15_1_4)) (= block_15_0_1 (ite check_14_0 false block_14_0_1)) (= halt_15_1 halt_14_1) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_1_3 (and (= accu_15_1 accu_14_1) (= mem_15_1 mem_14_1) (= sb-adr_15_1 sb-adr_14_1) (= sb-val_15_1 sb-val_14_1) (= sb-full_15_1 sb-full_14_1) (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) stmt_15_1_4) block_15_0_1 (= halt_15_1 halt_14_1) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_1_4 (and (= accu_15_1 accu_14_1) (= mem_15_1 mem_14_1) (= sb-adr_15_1 sb-adr_14_1) (= sb-val_15_1 sb-val_14_1) (= sb-full_15_1 sb-full_14_1) (and (not stmt_15_1_0) (not stmt_15_1_1) (not stmt_15_1_2) (not stmt_15_1_3) (not stmt_15_1_4)) (= block_15_0_1 (ite check_14_0 false block_14_0_1)) (and halt_15_1 (ite (and halt_15_0 halt_15_2) (and exit_15 (= exit-code #x0000)) (not exit_15))) (= heap_15 heap_14))))

(assert (=> (not thread_14_1) (and (= accu_15_1 accu_14_1) (= mem_15_1 mem_14_1) (= sb-adr_15_1 sb-adr_14_1) (= sb-val_15_1 sb-val_14_1) (= sb-full_15_1 (ite flush_14_1 false sb-full_14_1)) (and (= stmt_15_1_0 stmt_14_1_0) (= stmt_15_1_1 stmt_14_1_1) (= stmt_15_1_2 stmt_14_1_2) (= stmt_15_1_3 stmt_14_1_3) (= stmt_15_1_4 stmt_14_1_4)) (= block_15_0_1 (ite check_14_0 false block_14_0_1)) (= halt_15_1 halt_14_1))))

(assert (=> flush_14_1 (and (= heap_15 (store heap_14 sb-adr_14_1 sb-val_14_1)) (not exit_15))))

; thread 2
(assert (=> exec_14_2_0 (and (= accu_15_2 accu_14_2) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) stmt_15_2_1 (not stmt_15_2_2) (not stmt_15_2_3) (not stmt_15_2_4) (not stmt_15_2_5)) block_15_0_2 (= halt_15_2 halt_14_2) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_2_1 (and (= accu_15_2 (bvadd accu_14_2 (ite (and sb-full_14_2 (= sb-adr_14_2 #x0000)) sb-val_14_2 (select heap_14 #x0000)))) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) (not stmt_15_2_1) stmt_15_2_2 (not stmt_15_2_3) (not stmt_15_2_4) (not stmt_15_2_5)) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_2_2 (and (= accu_15_2 (bvadd accu_14_2 (ite (and sb-full_14_2 (= sb-adr_14_2 #x0001)) sb-val_14_2 (select heap_14 #x0001)))) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) (not stmt_15_2_1) (not stmt_15_2_2) stmt_15_2_3 (not stmt_15_2_4) (not stmt_15_2_5)) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_2_3 (and (= accu_15_2 accu_14_2) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) (not stmt_15_2_1) (not stmt_15_2_2) (not stmt_15_2_3) (ite (= accu_14_2 #x0000) (not stmt_15_2_4) stmt_15_2_4) (ite (= accu_14_2 #x0000) stmt_15_2_5 (not stmt_15_2_5))) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2) (= heap_15 heap_14) (not exit_15))))

(assert (=> exec_14_2_4 (and (= accu_15_2 accu_14_2) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) (not stmt_15_2_1) (not stmt_15_2_2) (not stmt_15_2_3) stmt_15_2_4 (not stmt_15_2_5)) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2) (= heap_15 heap_14) exit_15 (= exit-code #x0000))))

(assert (=> exec_14_2_5 (and (= accu_15_2 accu_14_2) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 sb-full_14_2) (and (not stmt_15_2_0) (not stmt_15_2_1) (not stmt_15_2_2) (not stmt_15_2_3) (not stmt_15_2_4) stmt_15_2_5) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2) (= heap_15 heap_14) exit_15 (= exit-code #x0001))))

(assert (=> (not thread_14_2) (and (= accu_15_2 accu_14_2) (= mem_15_2 mem_14_2) (= sb-adr_15_2 sb-adr_14_2) (= sb-val_15_2 sb-val_14_2) (= sb-full_15_2 (ite flush_14_2 false sb-full_14_2)) (and (= stmt_15_2_0 stmt_14_2_0) (= stmt_15_2_1 stmt_14_2_1) (= stmt_15_2_2 stmt_14_2_2) (= stmt_15_2_3 stmt_14_2_3) (= stmt_15_2_4 stmt_14_2_4) (= stmt_15_2_5 stmt_14_2_5)) (= block_15_0_2 (ite check_14_0 false block_14_0_2)) (= halt_15_2 halt_14_2))))

(assert (=> flush_14_2 (and (= heap_15 (store heap_14 sb-adr_14_2 sb-val_14_2)) (not exit_15))))

; exited
(assert (=> exit_14 (and (= heap_15 heap_14) exit_15)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 16
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_16_0 () (_ BitVec 16))
(declare-fun accu_16_1 () (_ BitVec 16))
(declare-fun accu_16_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_16_0 () (_ BitVec 16))
(declare-fun mem_16_1 () (_ BitVec 16))
(declare-fun mem_16_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_16_0 () (_ BitVec 16))
(declare-fun sb-adr_16_1 () (_ BitVec 16))
(declare-fun sb-adr_16_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_16_0 () (_ BitVec 16))
(declare-fun sb-val_16_1 () (_ BitVec 16))
(declare-fun sb-val_16_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_16_0 () Bool)
(declare-fun sb-full_16_1 () Bool)
(declare-fun sb-full_16_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_16_0_0 () Bool)
(declare-fun stmt_16_0_1 () Bool)
(declare-fun stmt_16_0_2 () Bool)
(declare-fun stmt_16_0_3 () Bool)
(declare-fun stmt_16_0_4 () Bool)

(declare-fun stmt_16_1_0 () Bool)
(declare-fun stmt_16_1_1 () Bool)
(declare-fun stmt_16_1_2 () Bool)
(declare-fun stmt_16_1_3 () Bool)
(declare-fun stmt_16_1_4 () Bool)

(declare-fun stmt_16_2_0 () Bool)
(declare-fun stmt_16_2_1 () Bool)
(declare-fun stmt_16_2_2 () Bool)
(declare-fun stmt_16_2_3 () Bool)
(declare-fun stmt_16_2_4 () Bool)
(declare-fun stmt_16_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_16_0_0 () Bool)
(declare-fun block_16_0_1 () Bool)
(declare-fun block_16_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_16_0 () Bool)
(declare-fun halt_16_1 () Bool)
(declare-fun halt_16_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_16 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_16 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_16_0 () Bool)
(declare-fun thread_16_1 () Bool)
(declare-fun thread_16_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_16_0_0 () Bool)
(declare-fun exec_16_0_1 () Bool)
(declare-fun exec_16_0_2 () Bool)
(declare-fun exec_16_0_3 () Bool)
(declare-fun exec_16_0_4 () Bool)

(declare-fun exec_16_1_0 () Bool)
(declare-fun exec_16_1_1 () Bool)
(declare-fun exec_16_1_2 () Bool)
(declare-fun exec_16_1_3 () Bool)
(declare-fun exec_16_1_4 () Bool)

(declare-fun exec_16_2_0 () Bool)
(declare-fun exec_16_2_1 () Bool)
(declare-fun exec_16_2_2 () Bool)
(declare-fun exec_16_2_3 () Bool)
(declare-fun exec_16_2_4 () Bool)
(declare-fun exec_16_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_16_0 () Bool)
(declare-fun flush_16_1 () Bool)
(declare-fun flush_16_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_16_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_16_0_0 (and stmt_16_0_0 thread_16_0)))
(assert (= exec_16_0_1 (and stmt_16_0_1 thread_16_0)))
(assert (= exec_16_0_2 (and stmt_16_0_2 thread_16_0)))
(assert (= exec_16_0_3 (and stmt_16_0_3 thread_16_0)))
(assert (= exec_16_0_4 (and stmt_16_0_4 thread_16_0)))

(assert (= exec_16_1_0 (and stmt_16_1_0 thread_16_1)))
(assert (= exec_16_1_1 (and stmt_16_1_1 thread_16_1)))
(assert (= exec_16_1_2 (and stmt_16_1_2 thread_16_1)))
(assert (= exec_16_1_3 (and stmt_16_1_3 thread_16_1)))
(assert (= exec_16_1_4 (and stmt_16_1_4 thread_16_1)))

(assert (= exec_16_2_0 (and stmt_16_2_0 thread_16_2)))
(assert (= exec_16_2_1 (and stmt_16_2_1 thread_16_2)))
(assert (= exec_16_2_2 (and stmt_16_2_2 thread_16_2)))
(assert (= exec_16_2_3 (and stmt_16_2_3 thread_16_2)))
(assert (= exec_16_2_4 (and stmt_16_2_4 thread_16_2)))
(assert (= exec_16_2_5 (and stmt_16_2_5 thread_16_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_16_0 (and block_16_0_0 block_16_0_1 block_16_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_16_0 flush_16_0 thread_16_1 flush_16_1 thread_16_2 flush_16_2 exit_16))
(assert (or (not thread_16_0) (not flush_16_0)))
(assert (or (not thread_16_0) (not thread_16_1)))
(assert (or (not thread_16_0) (not flush_16_1)))
(assert (or (not thread_16_0) (not thread_16_2)))
(assert (or (not thread_16_0) (not flush_16_2)))
(assert (or (not thread_16_0) (not exit_16)))
(assert (or (not flush_16_0) (not thread_16_1)))
(assert (or (not flush_16_0) (not flush_16_1)))
(assert (or (not flush_16_0) (not thread_16_2)))
(assert (or (not flush_16_0) (not flush_16_2)))
(assert (or (not flush_16_0) (not exit_16)))
(assert (or (not thread_16_1) (not flush_16_1)))
(assert (or (not thread_16_1) (not thread_16_2)))
(assert (or (not thread_16_1) (not flush_16_2)))
(assert (or (not thread_16_1) (not exit_16)))
(assert (or (not flush_16_1) (not thread_16_2)))
(assert (or (not flush_16_1) (not flush_16_2)))
(assert (or (not flush_16_1) (not exit_16)))
(assert (or (not thread_16_2) (not flush_16_2)))
(assert (or (not thread_16_2) (not exit_16)))
(assert (or (not flush_16_2) (not exit_16)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_16_0 (=> (or stmt_16_0_1 stmt_16_0_4) (not thread_16_0)) (not flush_16_0)))
(assert (ite sb-full_16_1 (=> (or stmt_16_1_1 stmt_16_1_4) (not thread_16_1)) (not flush_16_1)))
(assert (=> (not sb-full_16_2) (not flush_16_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_16_0_0 (not check_16_0)) (not thread_16_0))) ; checkpoint 0: thread 0
(assert (=> (and block_16_0_1 (not check_16_0)) (not thread_16_1))) ; checkpoint 0: thread 1
(assert (=> (and block_16_0_2 (not check_16_0)) (not thread_16_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_16_0 (not thread_16_0)))
(assert (=> halt_16_1 (not thread_16_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_15_0_0 (and (= accu_16_0 (bvadd accu_15_0 #x0001)) (= mem_16_0 mem_15_0) (= sb-adr_16_0 sb-adr_15_0) (= sb-val_16_0 sb-val_15_0) (= sb-full_16_0 sb-full_15_0) (and (not stmt_16_0_0) stmt_16_0_1 (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4)) (= block_16_0_0 (ite check_15_0 false block_15_0_0)) (= halt_16_0 halt_15_0) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_0_1 (and (= accu_16_0 accu_15_0) (= mem_16_0 mem_15_0) (= sb-adr_16_0 #x0000) (= sb-val_16_0 accu_15_0) sb-full_16_0 (and (not stmt_16_0_0) (not stmt_16_0_1) stmt_16_0_2 (not stmt_16_0_3) (not stmt_16_0_4)) (= block_16_0_0 (ite check_15_0 false block_15_0_0)) (= halt_16_0 halt_15_0) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_0_2 (and (= accu_16_0 (ite (and sb-full_15_0 (= sb-adr_15_0 #x0001)) sb-val_15_0 (select heap_15 #x0001))) (= mem_16_0 mem_15_0) (= sb-adr_16_0 sb-adr_15_0) (= sb-val_16_0 sb-val_15_0) (= sb-full_16_0 sb-full_15_0) (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) stmt_16_0_3 (not stmt_16_0_4)) (= block_16_0_0 (ite check_15_0 false block_15_0_0)) (= halt_16_0 halt_15_0) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_0_3 (and (= accu_16_0 accu_15_0) (= mem_16_0 mem_15_0) (= sb-adr_16_0 sb-adr_15_0) (= sb-val_16_0 sb-val_15_0) (= sb-full_16_0 sb-full_15_0) (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) stmt_16_0_4) block_16_0_0 (= halt_16_0 halt_15_0) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_0_4 (and (= accu_16_0 accu_15_0) (= mem_16_0 mem_15_0) (= sb-adr_16_0 sb-adr_15_0) (= sb-val_16_0 sb-val_15_0) (= sb-full_16_0 sb-full_15_0) (and (not stmt_16_0_0) (not stmt_16_0_1) (not stmt_16_0_2) (not stmt_16_0_3) (not stmt_16_0_4)) (= block_16_0_0 (ite check_15_0 false block_15_0_0)) (and halt_16_0 (ite (and halt_16_1 halt_16_2) (and exit_16 (= exit-code #x0000)) (not exit_16))) (= heap_16 heap_15))))

(assert (=> (not thread_15_0) (and (= accu_16_0 accu_15_0) (= mem_16_0 mem_15_0) (= sb-adr_16_0 sb-adr_15_0) (= sb-val_16_0 sb-val_15_0) (= sb-full_16_0 (ite flush_15_0 false sb-full_15_0)) (and (= stmt_16_0_0 stmt_15_0_0) (= stmt_16_0_1 stmt_15_0_1) (= stmt_16_0_2 stmt_15_0_2) (= stmt_16_0_3 stmt_15_0_3) (= stmt_16_0_4 stmt_15_0_4)) (= block_16_0_0 (ite check_15_0 false block_15_0_0)) (= halt_16_0 halt_15_0))))

(assert (=> flush_15_0 (and (= heap_16 (store heap_15 sb-adr_15_0 sb-val_15_0)) (not exit_16))))

; thread 1
(assert (=> exec_15_1_0 (and (= accu_16_1 (bvadd accu_15_1 #x0001)) (= mem_16_1 mem_15_1) (= sb-adr_16_1 sb-adr_15_1) (= sb-val_16_1 sb-val_15_1) (= sb-full_16_1 sb-full_15_1) (and (not stmt_16_1_0) stmt_16_1_1 (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4)) (= block_16_0_1 (ite check_15_0 false block_15_0_1)) (= halt_16_1 halt_15_1) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_1_1 (and (= accu_16_1 accu_15_1) (= mem_16_1 mem_15_1) (= sb-adr_16_1 #x0001) (= sb-val_16_1 accu_15_1) sb-full_16_1 (and (not stmt_16_1_0) (not stmt_16_1_1) stmt_16_1_2 (not stmt_16_1_3) (not stmt_16_1_4)) (= block_16_0_1 (ite check_15_0 false block_15_0_1)) (= halt_16_1 halt_15_1) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_1_2 (and (= accu_16_1 (ite (and sb-full_15_1 (= sb-adr_15_1 #x0000)) sb-val_15_1 (select heap_15 #x0000))) (= mem_16_1 mem_15_1) (= sb-adr_16_1 sb-adr_15_1) (= sb-val_16_1 sb-val_15_1) (= sb-full_16_1 sb-full_15_1) (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) stmt_16_1_3 (not stmt_16_1_4)) (= block_16_0_1 (ite check_15_0 false block_15_0_1)) (= halt_16_1 halt_15_1) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_1_3 (and (= accu_16_1 accu_15_1) (= mem_16_1 mem_15_1) (= sb-adr_16_1 sb-adr_15_1) (= sb-val_16_1 sb-val_15_1) (= sb-full_16_1 sb-full_15_1) (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) stmt_16_1_4) block_16_0_1 (= halt_16_1 halt_15_1) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_1_4 (and (= accu_16_1 accu_15_1) (= mem_16_1 mem_15_1) (= sb-adr_16_1 sb-adr_15_1) (= sb-val_16_1 sb-val_15_1) (= sb-full_16_1 sb-full_15_1) (and (not stmt_16_1_0) (not stmt_16_1_1) (not stmt_16_1_2) (not stmt_16_1_3) (not stmt_16_1_4)) (= block_16_0_1 (ite check_15_0 false block_15_0_1)) (and halt_16_1 (ite (and halt_16_0 halt_16_2) (and exit_16 (= exit-code #x0000)) (not exit_16))) (= heap_16 heap_15))))

(assert (=> (not thread_15_1) (and (= accu_16_1 accu_15_1) (= mem_16_1 mem_15_1) (= sb-adr_16_1 sb-adr_15_1) (= sb-val_16_1 sb-val_15_1) (= sb-full_16_1 (ite flush_15_1 false sb-full_15_1)) (and (= stmt_16_1_0 stmt_15_1_0) (= stmt_16_1_1 stmt_15_1_1) (= stmt_16_1_2 stmt_15_1_2) (= stmt_16_1_3 stmt_15_1_3) (= stmt_16_1_4 stmt_15_1_4)) (= block_16_0_1 (ite check_15_0 false block_15_0_1)) (= halt_16_1 halt_15_1))))

(assert (=> flush_15_1 (and (= heap_16 (store heap_15 sb-adr_15_1 sb-val_15_1)) (not exit_16))))

; thread 2
(assert (=> exec_15_2_0 (and (= accu_16_2 accu_15_2) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) stmt_16_2_1 (not stmt_16_2_2) (not stmt_16_2_3) (not stmt_16_2_4) (not stmt_16_2_5)) block_16_0_2 (= halt_16_2 halt_15_2) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_2_1 (and (= accu_16_2 (bvadd accu_15_2 (ite (and sb-full_15_2 (= sb-adr_15_2 #x0000)) sb-val_15_2 (select heap_15 #x0000)))) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) (not stmt_16_2_1) stmt_16_2_2 (not stmt_16_2_3) (not stmt_16_2_4) (not stmt_16_2_5)) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_2_2 (and (= accu_16_2 (bvadd accu_15_2 (ite (and sb-full_15_2 (= sb-adr_15_2 #x0001)) sb-val_15_2 (select heap_15 #x0001)))) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) (not stmt_16_2_1) (not stmt_16_2_2) stmt_16_2_3 (not stmt_16_2_4) (not stmt_16_2_5)) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_2_3 (and (= accu_16_2 accu_15_2) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) (not stmt_16_2_1) (not stmt_16_2_2) (not stmt_16_2_3) (ite (= accu_15_2 #x0000) (not stmt_16_2_4) stmt_16_2_4) (ite (= accu_15_2 #x0000) stmt_16_2_5 (not stmt_16_2_5))) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2) (= heap_16 heap_15) (not exit_16))))

(assert (=> exec_15_2_4 (and (= accu_16_2 accu_15_2) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) (not stmt_16_2_1) (not stmt_16_2_2) (not stmt_16_2_3) stmt_16_2_4 (not stmt_16_2_5)) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2) (= heap_16 heap_15) exit_16 (= exit-code #x0000))))

(assert (=> exec_15_2_5 (and (= accu_16_2 accu_15_2) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 sb-full_15_2) (and (not stmt_16_2_0) (not stmt_16_2_1) (not stmt_16_2_2) (not stmt_16_2_3) (not stmt_16_2_4) stmt_16_2_5) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2) (= heap_16 heap_15) exit_16 (= exit-code #x0001))))

(assert (=> (not thread_15_2) (and (= accu_16_2 accu_15_2) (= mem_16_2 mem_15_2) (= sb-adr_16_2 sb-adr_15_2) (= sb-val_16_2 sb-val_15_2) (= sb-full_16_2 (ite flush_15_2 false sb-full_15_2)) (and (= stmt_16_2_0 stmt_15_2_0) (= stmt_16_2_1 stmt_15_2_1) (= stmt_16_2_2 stmt_15_2_2) (= stmt_16_2_3 stmt_15_2_3) (= stmt_16_2_4 stmt_15_2_4) (= stmt_16_2_5 stmt_15_2_5)) (= block_16_0_2 (ite check_15_0 false block_15_0_2)) (= halt_16_2 halt_15_2))))

(assert (=> flush_15_2 (and (= heap_16 (store heap_15 sb-adr_15_2 sb-val_15_2)) (not exit_16))))

; exited
(assert (=> exit_15 (and (= heap_16 heap_15) exit_16)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 17
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_17_0 () (_ BitVec 16))
(declare-fun accu_17_1 () (_ BitVec 16))
(declare-fun accu_17_2 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_17_0 () (_ BitVec 16))
(declare-fun mem_17_1 () (_ BitVec 16))
(declare-fun mem_17_2 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_17_0 () (_ BitVec 16))
(declare-fun sb-adr_17_1 () (_ BitVec 16))
(declare-fun sb-adr_17_2 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_17_0 () (_ BitVec 16))
(declare-fun sb-val_17_1 () (_ BitVec 16))
(declare-fun sb-val_17_2 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_17_0 () Bool)
(declare-fun sb-full_17_1 () Bool)
(declare-fun sb-full_17_2 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_17_0_0 () Bool)
(declare-fun stmt_17_0_1 () Bool)
(declare-fun stmt_17_0_2 () Bool)
(declare-fun stmt_17_0_3 () Bool)
(declare-fun stmt_17_0_4 () Bool)

(declare-fun stmt_17_1_0 () Bool)
(declare-fun stmt_17_1_1 () Bool)
(declare-fun stmt_17_1_2 () Bool)
(declare-fun stmt_17_1_3 () Bool)
(declare-fun stmt_17_1_4 () Bool)

(declare-fun stmt_17_2_0 () Bool)
(declare-fun stmt_17_2_1 () Bool)
(declare-fun stmt_17_2_2 () Bool)
(declare-fun stmt_17_2_3 () Bool)
(declare-fun stmt_17_2_4 () Bool)
(declare-fun stmt_17_2_5 () Bool)

; blocking variables - block_<step>_<id>_<thread>
(declare-fun block_17_0_0 () Bool)
(declare-fun block_17_0_1 () Bool)
(declare-fun block_17_0_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_17_0 () Bool)
(declare-fun halt_17_1 () Bool)
(declare-fun halt_17_2 () Bool)

; heap variable - heap_<step>
(declare-fun heap_17 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_17 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_17_0 () Bool)
(declare-fun thread_17_1 () Bool)
(declare-fun thread_17_2 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_17_0_0 () Bool)
(declare-fun exec_17_0_1 () Bool)
(declare-fun exec_17_0_2 () Bool)
(declare-fun exec_17_0_3 () Bool)
(declare-fun exec_17_0_4 () Bool)

(declare-fun exec_17_1_0 () Bool)
(declare-fun exec_17_1_1 () Bool)
(declare-fun exec_17_1_2 () Bool)
(declare-fun exec_17_1_3 () Bool)
(declare-fun exec_17_1_4 () Bool)

(declare-fun exec_17_2_0 () Bool)
(declare-fun exec_17_2_1 () Bool)
(declare-fun exec_17_2_2 () Bool)
(declare-fun exec_17_2_3 () Bool)
(declare-fun exec_17_2_4 () Bool)
(declare-fun exec_17_2_5 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_17_0 () Bool)
(declare-fun flush_17_1 () Bool)
(declare-fun flush_17_2 () Bool)

; checkpoint variables - check_<step>_<id>
(declare-fun check_17_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_17_0_0 (and stmt_17_0_0 thread_17_0)))
(assert (= exec_17_0_1 (and stmt_17_0_1 thread_17_0)))
(assert (= exec_17_0_2 (and stmt_17_0_2 thread_17_0)))
(assert (= exec_17_0_3 (and stmt_17_0_3 thread_17_0)))
(assert (= exec_17_0_4 (and stmt_17_0_4 thread_17_0)))

(assert (= exec_17_1_0 (and stmt_17_1_0 thread_17_1)))
(assert (= exec_17_1_1 (and stmt_17_1_1 thread_17_1)))
(assert (= exec_17_1_2 (and stmt_17_1_2 thread_17_1)))
(assert (= exec_17_1_3 (and stmt_17_1_3 thread_17_1)))
(assert (= exec_17_1_4 (and stmt_17_1_4 thread_17_1)))

(assert (= exec_17_2_0 (and stmt_17_2_0 thread_17_2)))
(assert (= exec_17_2_1 (and stmt_17_2_1 thread_17_2)))
(assert (= exec_17_2_2 (and stmt_17_2_2 thread_17_2)))
(assert (= exec_17_2_3 (and stmt_17_2_3 thread_17_2)))
(assert (= exec_17_2_4 (and stmt_17_2_4 thread_17_2)))
(assert (= exec_17_2_5 (and stmt_17_2_5 thread_17_2)))

; checkpoint variables - check_<step>_<id>
(assert (= check_17_0 (and block_17_0_0 block_17_0_1 block_17_0_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_17_0 flush_17_0 thread_17_1 flush_17_1 thread_17_2 flush_17_2 exit_17))
(assert (or (not thread_17_0) (not flush_17_0)))
(assert (or (not thread_17_0) (not thread_17_1)))
(assert (or (not thread_17_0) (not flush_17_1)))
(assert (or (not thread_17_0) (not thread_17_2)))
(assert (or (not thread_17_0) (not flush_17_2)))
(assert (or (not thread_17_0) (not exit_17)))
(assert (or (not flush_17_0) (not thread_17_1)))
(assert (or (not flush_17_0) (not flush_17_1)))
(assert (or (not flush_17_0) (not thread_17_2)))
(assert (or (not flush_17_0) (not flush_17_2)))
(assert (or (not flush_17_0) (not exit_17)))
(assert (or (not thread_17_1) (not flush_17_1)))
(assert (or (not thread_17_1) (not thread_17_2)))
(assert (or (not thread_17_1) (not flush_17_2)))
(assert (or (not thread_17_1) (not exit_17)))
(assert (or (not flush_17_1) (not thread_17_2)))
(assert (or (not flush_17_1) (not flush_17_2)))
(assert (or (not flush_17_1) (not exit_17)))
(assert (or (not thread_17_2) (not flush_17_2)))
(assert (or (not thread_17_2) (not exit_17)))
(assert (or (not flush_17_2) (not exit_17)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_17_0 (=> (or stmt_17_0_1 stmt_17_0_4) (not thread_17_0)) (not flush_17_0)))
(assert (ite sb-full_17_1 (=> (or stmt_17_1_1 stmt_17_1_4) (not thread_17_1)) (not flush_17_1)))
(assert (=> (not sb-full_17_2) (not flush_17_2)))

; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> (and block_17_0_0 (not check_17_0)) (not thread_17_0))) ; checkpoint 0: thread 0
(assert (=> (and block_17_0_1 (not check_17_0)) (not thread_17_1))) ; checkpoint 0: thread 1
(assert (=> (and block_17_0_2 (not check_17_0)) (not thread_17_2))) ; checkpoint 0: thread 2

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_17_0 (not thread_17_0)))
(assert (=> halt_17_1 (not thread_17_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_16_0_0 (and (= accu_17_0 (bvadd accu_16_0 #x0001)) (= mem_17_0 mem_16_0) (= sb-adr_17_0 sb-adr_16_0) (= sb-val_17_0 sb-val_16_0) (= sb-full_17_0 sb-full_16_0) (and (not stmt_17_0_0) stmt_17_0_1 (not stmt_17_0_2) (not stmt_17_0_3) (not stmt_17_0_4)) (= block_17_0_0 (ite check_16_0 false block_16_0_0)) (= halt_17_0 halt_16_0) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_0_1 (and (= accu_17_0 accu_16_0) (= mem_17_0 mem_16_0) (= sb-adr_17_0 #x0000) (= sb-val_17_0 accu_16_0) sb-full_17_0 (and (not stmt_17_0_0) (not stmt_17_0_1) stmt_17_0_2 (not stmt_17_0_3) (not stmt_17_0_4)) (= block_17_0_0 (ite check_16_0 false block_16_0_0)) (= halt_17_0 halt_16_0) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_0_2 (and (= accu_17_0 (ite (and sb-full_16_0 (= sb-adr_16_0 #x0001)) sb-val_16_0 (select heap_16 #x0001))) (= mem_17_0 mem_16_0) (= sb-adr_17_0 sb-adr_16_0) (= sb-val_17_0 sb-val_16_0) (= sb-full_17_0 sb-full_16_0) (and (not stmt_17_0_0) (not stmt_17_0_1) (not stmt_17_0_2) stmt_17_0_3 (not stmt_17_0_4)) (= block_17_0_0 (ite check_16_0 false block_16_0_0)) (= halt_17_0 halt_16_0) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_0_3 (and (= accu_17_0 accu_16_0) (= mem_17_0 mem_16_0) (= sb-adr_17_0 sb-adr_16_0) (= sb-val_17_0 sb-val_16_0) (= sb-full_17_0 sb-full_16_0) (and (not stmt_17_0_0) (not stmt_17_0_1) (not stmt_17_0_2) (not stmt_17_0_3) stmt_17_0_4) block_17_0_0 (= halt_17_0 halt_16_0) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_0_4 (and (= accu_17_0 accu_16_0) (= mem_17_0 mem_16_0) (= sb-adr_17_0 sb-adr_16_0) (= sb-val_17_0 sb-val_16_0) (= sb-full_17_0 sb-full_16_0) (and (not stmt_17_0_0) (not stmt_17_0_1) (not stmt_17_0_2) (not stmt_17_0_3) (not stmt_17_0_4)) (= block_17_0_0 (ite check_16_0 false block_16_0_0)) (and halt_17_0 (ite (and halt_17_1 halt_17_2) (and exit_17 (= exit-code #x0000)) (not exit_17))) (= heap_17 heap_16))))

(assert (=> (not thread_16_0) (and (= accu_17_0 accu_16_0) (= mem_17_0 mem_16_0) (= sb-adr_17_0 sb-adr_16_0) (= sb-val_17_0 sb-val_16_0) (= sb-full_17_0 (ite flush_16_0 false sb-full_16_0)) (and (= stmt_17_0_0 stmt_16_0_0) (= stmt_17_0_1 stmt_16_0_1) (= stmt_17_0_2 stmt_16_0_2) (= stmt_17_0_3 stmt_16_0_3) (= stmt_17_0_4 stmt_16_0_4)) (= block_17_0_0 (ite check_16_0 false block_16_0_0)) (= halt_17_0 halt_16_0))))

(assert (=> flush_16_0 (and (= heap_17 (store heap_16 sb-adr_16_0 sb-val_16_0)) (not exit_17))))

; thread 1
(assert (=> exec_16_1_0 (and (= accu_17_1 (bvadd accu_16_1 #x0001)) (= mem_17_1 mem_16_1) (= sb-adr_17_1 sb-adr_16_1) (= sb-val_17_1 sb-val_16_1) (= sb-full_17_1 sb-full_16_1) (and (not stmt_17_1_0) stmt_17_1_1 (not stmt_17_1_2) (not stmt_17_1_3) (not stmt_17_1_4)) (= block_17_0_1 (ite check_16_0 false block_16_0_1)) (= halt_17_1 halt_16_1) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_1_1 (and (= accu_17_1 accu_16_1) (= mem_17_1 mem_16_1) (= sb-adr_17_1 #x0001) (= sb-val_17_1 accu_16_1) sb-full_17_1 (and (not stmt_17_1_0) (not stmt_17_1_1) stmt_17_1_2 (not stmt_17_1_3) (not stmt_17_1_4)) (= block_17_0_1 (ite check_16_0 false block_16_0_1)) (= halt_17_1 halt_16_1) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_1_2 (and (= accu_17_1 (ite (and sb-full_16_1 (= sb-adr_16_1 #x0000)) sb-val_16_1 (select heap_16 #x0000))) (= mem_17_1 mem_16_1) (= sb-adr_17_1 sb-adr_16_1) (= sb-val_17_1 sb-val_16_1) (= sb-full_17_1 sb-full_16_1) (and (not stmt_17_1_0) (not stmt_17_1_1) (not stmt_17_1_2) stmt_17_1_3 (not stmt_17_1_4)) (= block_17_0_1 (ite check_16_0 false block_16_0_1)) (= halt_17_1 halt_16_1) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_1_3 (and (= accu_17_1 accu_16_1) (= mem_17_1 mem_16_1) (= sb-adr_17_1 sb-adr_16_1) (= sb-val_17_1 sb-val_16_1) (= sb-full_17_1 sb-full_16_1) (and (not stmt_17_1_0) (not stmt_17_1_1) (not stmt_17_1_2) (not stmt_17_1_3) stmt_17_1_4) block_17_0_1 (= halt_17_1 halt_16_1) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_1_4 (and (= accu_17_1 accu_16_1) (= mem_17_1 mem_16_1) (= sb-adr_17_1 sb-adr_16_1) (= sb-val_17_1 sb-val_16_1) (= sb-full_17_1 sb-full_16_1) (and (not stmt_17_1_0) (not stmt_17_1_1) (not stmt_17_1_2) (not stmt_17_1_3) (not stmt_17_1_4)) (= block_17_0_1 (ite check_16_0 false block_16_0_1)) (and halt_17_1 (ite (and halt_17_0 halt_17_2) (and exit_17 (= exit-code #x0000)) (not exit_17))) (= heap_17 heap_16))))

(assert (=> (not thread_16_1) (and (= accu_17_1 accu_16_1) (= mem_17_1 mem_16_1) (= sb-adr_17_1 sb-adr_16_1) (= sb-val_17_1 sb-val_16_1) (= sb-full_17_1 (ite flush_16_1 false sb-full_16_1)) (and (= stmt_17_1_0 stmt_16_1_0) (= stmt_17_1_1 stmt_16_1_1) (= stmt_17_1_2 stmt_16_1_2) (= stmt_17_1_3 stmt_16_1_3) (= stmt_17_1_4 stmt_16_1_4)) (= block_17_0_1 (ite check_16_0 false block_16_0_1)) (= halt_17_1 halt_16_1))))

(assert (=> flush_16_1 (and (= heap_17 (store heap_16 sb-adr_16_1 sb-val_16_1)) (not exit_17))))

; thread 2
(assert (=> exec_16_2_0 (and (= accu_17_2 accu_16_2) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) stmt_17_2_1 (not stmt_17_2_2) (not stmt_17_2_3) (not stmt_17_2_4) (not stmt_17_2_5)) block_17_0_2 (= halt_17_2 halt_16_2) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_2_1 (and (= accu_17_2 (bvadd accu_16_2 (ite (and sb-full_16_2 (= sb-adr_16_2 #x0000)) sb-val_16_2 (select heap_16 #x0000)))) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) (not stmt_17_2_1) stmt_17_2_2 (not stmt_17_2_3) (not stmt_17_2_4) (not stmt_17_2_5)) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_2_2 (and (= accu_17_2 (bvadd accu_16_2 (ite (and sb-full_16_2 (= sb-adr_16_2 #x0001)) sb-val_16_2 (select heap_16 #x0001)))) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) (not stmt_17_2_1) (not stmt_17_2_2) stmt_17_2_3 (not stmt_17_2_4) (not stmt_17_2_5)) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_2_3 (and (= accu_17_2 accu_16_2) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) (not stmt_17_2_1) (not stmt_17_2_2) (not stmt_17_2_3) (ite (= accu_16_2 #x0000) (not stmt_17_2_4) stmt_17_2_4) (ite (= accu_16_2 #x0000) stmt_17_2_5 (not stmt_17_2_5))) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2) (= heap_17 heap_16) (not exit_17))))

(assert (=> exec_16_2_4 (and (= accu_17_2 accu_16_2) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) (not stmt_17_2_1) (not stmt_17_2_2) (not stmt_17_2_3) stmt_17_2_4 (not stmt_17_2_5)) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2) (= heap_17 heap_16) exit_17 (= exit-code #x0000))))

(assert (=> exec_16_2_5 (and (= accu_17_2 accu_16_2) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 sb-full_16_2) (and (not stmt_17_2_0) (not stmt_17_2_1) (not stmt_17_2_2) (not stmt_17_2_3) (not stmt_17_2_4) stmt_17_2_5) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2) (= heap_17 heap_16) exit_17 (= exit-code #x0001))))

(assert (=> (not thread_16_2) (and (= accu_17_2 accu_16_2) (= mem_17_2 mem_16_2) (= sb-adr_17_2 sb-adr_16_2) (= sb-val_17_2 sb-val_16_2) (= sb-full_17_2 (ite flush_16_2 false sb-full_16_2)) (and (= stmt_17_2_0 stmt_16_2_0) (= stmt_17_2_1 stmt_16_2_1) (= stmt_17_2_2 stmt_16_2_2) (= stmt_17_2_3 stmt_16_2_3) (= stmt_17_2_4 stmt_16_2_4) (= stmt_17_2_5 stmt_16_2_5)) (= block_17_0_2 (ite check_16_0 false block_16_0_2)) (= halt_17_2 halt_16_2))))

(assert (=> flush_16_2 (and (= heap_17 (store heap_16 sb-adr_16_2 sb-val_16_2)) (not exit_17))))

; exited
(assert (=> exit_16 (and (= heap_17 heap_16) exit_17)))

(assert (=> (not exit_17) (= exit-code #x0000)))

