(set-logic QF_AUFBV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_0_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_0_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_0_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_0_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_0_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_0_0_0 () Bool)
(declare-fun stmt_0_0_1 () Bool)
(declare-fun stmt_0_0_2 () Bool)
(declare-fun stmt_0_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_0_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_0 () Bool)

; exit code variable
(declare-fun exit-code () (_ BitVec 16))

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_0_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_0_0_0 () Bool)
(declare-fun exec_0_0_1 () Bool)
(declare-fun exec_0_0_2 () Bool)
(declare-fun exec_0_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_0_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))
(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))
(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))
(assert (= exec_0_0_3 (and stmt_0_0_3 thread_0_0)))

; state variable initializations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_0_0 #x0000))

; mem variables - mem_<step>_<thread>
(assert (= mem_0_0 #x0000))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_0_0 #x0000))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_0_0 #x0000))

; store buffer full variables - sb-full_<step>_<thread>
(assert (not sb-full_0_0))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert stmt_0_0_0)
(assert (not stmt_0_0_1))
(assert (not stmt_0_0_2))
(assert (not stmt_0_0_3))

; halt variables - halt_<step>_<thread>
(assert (not halt_0_0))

; heap variable - heap_<step>
(assert (= (select heap_0 #x0000) #x0000))

; exit flag variable - exit_<step>
(assert (not exit_0))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_0_0 flush_0_0 exit_0))
(assert (or (not thread_0_0) (not flush_0_0)))
(assert (or (not thread_0_0) (not exit_0)))
(assert (or (not flush_0_0) (not exit_0)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_0_0 (=> (or stmt_0_0_1 stmt_0_0_3) (not thread_0_0)) (not flush_0_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_0_0 (not thread_0_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_1_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_1_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_1_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_1_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_1_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_0_0 () Bool)
(declare-fun stmt_1_0_1 () Bool)
(declare-fun stmt_1_0_2 () Bool)
(declare-fun stmt_1_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_1_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_1 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_0_0 () Bool)
(declare-fun exec_1_0_1 () Bool)
(declare-fun exec_1_0_2 () Bool)
(declare-fun exec_1_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_1_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))
(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))
(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))
(assert (= exec_1_0_3 (and stmt_1_0_3 thread_1_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_0_0_0 (and (= accu_1_0 (bvadd accu_0_0 #x0001)) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) stmt_1_0_1 (not stmt_1_0_2) (not stmt_1_0_3)) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_1 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 #x0000) (= sb-val_1_0 accu_0_0) sb-full_1_0 (and (not stmt_1_0_0) (not stmt_1_0_1) stmt_1_0_2 (not stmt_1_0_3)) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_2 (and (= accu_1_0 (ite (and sb-full_0_0 (= sb-adr_0_0 #x0000)) sb-val_0_0 (select heap_0 #x0000))) (= mem_1_0 (ite (and sb-full_0_0 (= sb-adr_0_0 #x0000)) sb-val_0_0 (select heap_0 #x0000))) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) (not stmt_1_0_2) stmt_1_0_3) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_3 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and halt_1_0 (=> halt_1_0 exit_1)) (= heap_1 heap_0))))

(assert (=> (not thread_0_0) (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) (and (= stmt_1_0_0 stmt_0_0_0) (= stmt_1_0_1 stmt_0_0_1) (= stmt_1_0_2 stmt_0_0_2) (= stmt_1_0_3 stmt_0_0_3)) (= halt_1_0 halt_0_0))))

(assert (=> flush_0_0 (and (not sb-full_1_0) (= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)))))

; exited
(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_1_0 flush_1_0 exit_1))
(assert (or (not thread_1_0) (not flush_1_0)))
(assert (or (not thread_1_0) (not exit_1)))
(assert (or (not flush_1_0) (not exit_1)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_1_0 (=> (or stmt_1_0_1 stmt_1_0_3) (not thread_1_0)) (not flush_1_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_1_0 (not thread_1_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_2_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_2_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_2_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_2_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_2_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_0_0 () Bool)
(declare-fun stmt_2_0_1 () Bool)
(declare-fun stmt_2_0_2 () Bool)
(declare-fun stmt_2_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_2_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_2 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_0_0 () Bool)
(declare-fun exec_2_0_1 () Bool)
(declare-fun exec_2_0_2 () Bool)
(declare-fun exec_2_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_2_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_2_0_0 (and stmt_2_0_0 thread_2_0)))
(assert (= exec_2_0_1 (and stmt_2_0_1 thread_2_0)))
(assert (= exec_2_0_2 (and stmt_2_0_2 thread_2_0)))
(assert (= exec_2_0_3 (and stmt_2_0_3 thread_2_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_1_0_0 (and (= accu_2_0 (bvadd accu_1_0 #x0001)) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) stmt_2_0_1 (not stmt_2_0_2) (not stmt_2_0_3)) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_1 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 #x0000) (= sb-val_2_0 accu_1_0) sb-full_2_0 (and (not stmt_2_0_0) (not stmt_2_0_1) stmt_2_0_2 (not stmt_2_0_3)) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_2 (and (= accu_2_0 (ite (and sb-full_1_0 (= sb-adr_1_0 #x0000)) sb-val_1_0 (select heap_1 #x0000))) (= mem_2_0 (ite (and sb-full_1_0 (= sb-adr_1_0 #x0000)) sb-val_1_0 (select heap_1 #x0000))) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2) stmt_2_0_3) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_3 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and halt_2_0 (=> halt_2_0 exit_2)) (= heap_2 heap_1))))

(assert (=> (not thread_1_0) (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 (ite flush_1_0 false sb-full_1_0)) (and (= stmt_2_0_0 stmt_1_0_0) (= stmt_2_0_1 stmt_1_0_1) (= stmt_2_0_2 stmt_1_0_2) (= stmt_2_0_3 stmt_1_0_3)) (= halt_2_0 halt_1_0))))

(assert (=> flush_1_0 (and (not sb-full_2_0) (= heap_2 (store heap_1 sb-adr_1_0 sb-val_1_0)))))

; exited
(assert (=> exit_1 (and (= heap_2 heap_1) exit_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_2_0 flush_2_0 exit_2))
(assert (or (not thread_2_0) (not flush_2_0)))
(assert (or (not thread_2_0) (not exit_2)))
(assert (or (not flush_2_0) (not exit_2)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_2_0 (=> (or stmt_2_0_1 stmt_2_0_3) (not thread_2_0)) (not flush_2_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_2_0 (not thread_2_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_3_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_3_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_3_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_3_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_3_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_0_0 () Bool)
(declare-fun stmt_3_0_1 () Bool)
(declare-fun stmt_3_0_2 () Bool)
(declare-fun stmt_3_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_3_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_3 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_0_0 () Bool)
(declare-fun exec_3_0_1 () Bool)
(declare-fun exec_3_0_2 () Bool)
(declare-fun exec_3_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_3_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_3_0_0 (and stmt_3_0_0 thread_3_0)))
(assert (= exec_3_0_1 (and stmt_3_0_1 thread_3_0)))
(assert (= exec_3_0_2 (and stmt_3_0_2 thread_3_0)))
(assert (= exec_3_0_3 (and stmt_3_0_3 thread_3_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_2_0_0 (and (= accu_3_0 (bvadd accu_2_0 #x0001)) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) stmt_3_0_1 (not stmt_3_0_2) (not stmt_3_0_3)) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_1 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 #x0000) (= sb-val_3_0 accu_2_0) sb-full_3_0 (and (not stmt_3_0_0) (not stmt_3_0_1) stmt_3_0_2 (not stmt_3_0_3)) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_2 (and (= accu_3_0 (ite (and sb-full_2_0 (= sb-adr_2_0 #x0000)) sb-val_2_0 (select heap_2 #x0000))) (= mem_3_0 (ite (and sb-full_2_0 (= sb-adr_2_0 #x0000)) sb-val_2_0 (select heap_2 #x0000))) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2) stmt_3_0_3) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_3 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and halt_3_0 (=> halt_3_0 exit_3)) (= heap_3 heap_2))))

(assert (=> (not thread_2_0) (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 (ite flush_2_0 false sb-full_2_0)) (and (= stmt_3_0_0 stmt_2_0_0) (= stmt_3_0_1 stmt_2_0_1) (= stmt_3_0_2 stmt_2_0_2) (= stmt_3_0_3 stmt_2_0_3)) (= halt_3_0 halt_2_0))))

(assert (=> flush_2_0 (and (not sb-full_3_0) (= heap_3 (store heap_2 sb-adr_2_0 sb-val_2_0)))))

; exited
(assert (=> exit_2 (and (= heap_3 heap_2) exit_3)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_3_0 flush_3_0 exit_3))
(assert (or (not thread_3_0) (not flush_3_0)))
(assert (or (not thread_3_0) (not exit_3)))
(assert (or (not flush_3_0) (not exit_3)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_3_0 (=> (or stmt_3_0_1 stmt_3_0_3) (not thread_3_0)) (not flush_3_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_3_0 (not thread_3_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_4_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_4_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_4_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_4_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_4_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_0_0 () Bool)
(declare-fun stmt_4_0_1 () Bool)
(declare-fun stmt_4_0_2 () Bool)
(declare-fun stmt_4_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_4_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_4 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_0_0 () Bool)
(declare-fun exec_4_0_1 () Bool)
(declare-fun exec_4_0_2 () Bool)
(declare-fun exec_4_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_4_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_4_0_0 (and stmt_4_0_0 thread_4_0)))
(assert (= exec_4_0_1 (and stmt_4_0_1 thread_4_0)))
(assert (= exec_4_0_2 (and stmt_4_0_2 thread_4_0)))
(assert (= exec_4_0_3 (and stmt_4_0_3 thread_4_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_3_0_0 (and (= accu_4_0 (bvadd accu_3_0 #x0001)) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) stmt_4_0_1 (not stmt_4_0_2) (not stmt_4_0_3)) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_1 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 #x0000) (= sb-val_4_0 accu_3_0) sb-full_4_0 (and (not stmt_4_0_0) (not stmt_4_0_1) stmt_4_0_2 (not stmt_4_0_3)) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_2 (and (= accu_4_0 (ite (and sb-full_3_0 (= sb-adr_3_0 #x0000)) sb-val_3_0 (select heap_3 #x0000))) (= mem_4_0 (ite (and sb-full_3_0 (= sb-adr_3_0 #x0000)) sb-val_3_0 (select heap_3 #x0000))) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2) stmt_4_0_3) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_3 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and halt_4_0 (=> halt_4_0 exit_4)) (= heap_4 heap_3))))

(assert (=> (not thread_3_0) (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 (ite flush_3_0 false sb-full_3_0)) (and (= stmt_4_0_0 stmt_3_0_0) (= stmt_4_0_1 stmt_3_0_1) (= stmt_4_0_2 stmt_3_0_2) (= stmt_4_0_3 stmt_3_0_3)) (= halt_4_0 halt_3_0))))

(assert (=> flush_3_0 (and (not sb-full_4_0) (= heap_4 (store heap_3 sb-adr_3_0 sb-val_3_0)))))

; exited
(assert (=> exit_3 (and (= heap_4 heap_3) exit_4)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_4_0 flush_4_0 exit_4))
(assert (or (not thread_4_0) (not flush_4_0)))
(assert (or (not thread_4_0) (not exit_4)))
(assert (or (not flush_4_0) (not exit_4)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_4_0 (=> (or stmt_4_0_1 stmt_4_0_3) (not thread_4_0)) (not flush_4_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_4_0 (not thread_4_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_5_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_5_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_5_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_5_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_5_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_0_0 () Bool)
(declare-fun stmt_5_0_1 () Bool)
(declare-fun stmt_5_0_2 () Bool)
(declare-fun stmt_5_0_3 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_5_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_5 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_0_0 () Bool)
(declare-fun exec_5_0_1 () Bool)
(declare-fun exec_5_0_2 () Bool)
(declare-fun exec_5_0_3 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_5_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_5_0_0 (and stmt_5_0_0 thread_5_0)))
(assert (= exec_5_0_1 (and stmt_5_0_1 thread_5_0)))
(assert (= exec_5_0_2 (and stmt_5_0_2 thread_5_0)))
(assert (= exec_5_0_3 (and stmt_5_0_3 thread_5_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_4_0_0 (and (= accu_5_0 (bvadd accu_4_0 #x0001)) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) stmt_5_0_1 (not stmt_5_0_2) (not stmt_5_0_3)) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_1 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 #x0000) (= sb-val_5_0 accu_4_0) sb-full_5_0 (and (not stmt_5_0_0) (not stmt_5_0_1) stmt_5_0_2 (not stmt_5_0_3)) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_2 (and (= accu_5_0 (ite (and sb-full_4_0 (= sb-adr_4_0 #x0000)) sb-val_4_0 (select heap_4 #x0000))) (= mem_5_0 (ite (and sb-full_4_0 (= sb-adr_4_0 #x0000)) sb-val_4_0 (select heap_4 #x0000))) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2) stmt_5_0_3) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_3 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and halt_5_0 (=> halt_5_0 exit_5)) (= heap_5 heap_4))))

(assert (=> (not thread_4_0) (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 (ite flush_4_0 false sb-full_4_0)) (and (= stmt_5_0_0 stmt_4_0_0) (= stmt_5_0_1 stmt_4_0_1) (= stmt_5_0_2 stmt_4_0_2) (= stmt_5_0_3 stmt_4_0_3)) (= halt_5_0 halt_4_0))))

(assert (=> flush_4_0 (and (not sb-full_5_0) (= heap_5 (store heap_4 sb-adr_4_0 sb-val_4_0)))))

; exited
(assert (=> exit_4 (and (= heap_5 heap_4) exit_5)))

(assert (=> (not exit_5) (= exit-code #x0000)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_5_0 flush_5_0 exit_5))
(assert (or (not thread_5_0) (not flush_5_0)))
(assert (or (not thread_5_0) (not exit_5)))
(assert (or (not flush_5_0) (not exit_5)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_5_0 (=> (or stmt_5_0_1 stmt_5_0_3) (not thread_5_0)) (not flush_5_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_5_0 (not thread_5_0)))

