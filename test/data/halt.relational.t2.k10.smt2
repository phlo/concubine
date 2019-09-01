(set-logic QF_AUFBV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_0_0 () (_ BitVec 16))
(declare-fun accu_0_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_0_0 () (_ BitVec 16))
(declare-fun mem_0_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_0_0 () (_ BitVec 16))
(declare-fun sb-adr_0_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_0_0 () (_ BitVec 16))
(declare-fun sb-val_0_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_0_0 () Bool)
(declare-fun sb-full_0_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_0_0_0 () Bool)
(declare-fun stmt_0_0_1 () Bool)
(declare-fun stmt_0_0_2 () Bool)

(declare-fun stmt_0_1_0 () Bool)
(declare-fun stmt_0_1_1 () Bool)
(declare-fun stmt_0_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_0_0 () Bool)
(declare-fun halt_0_1 () Bool)

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

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_0_0_0 () Bool)
(declare-fun exec_0_0_1 () Bool)
(declare-fun exec_0_0_2 () Bool)

(declare-fun exec_0_1_0 () Bool)
(declare-fun exec_0_1_1 () Bool)
(declare-fun exec_0_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_0_0 () Bool)
(declare-fun flush_0_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))
(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))
(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))

(assert (= exec_0_1_0 (and stmt_0_1_0 thread_0_1)))
(assert (= exec_0_1_1 (and stmt_0_1_1 thread_0_1)))
(assert (= exec_0_1_2 (and stmt_0_1_2 thread_0_1)))

; state variable initializations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_0_0 #x0000))
(assert (= accu_0_1 #x0000))

; mem variables - mem_<step>_<thread>
(assert (= mem_0_0 #x0000))
(assert (= mem_0_1 #x0000))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_0_0 #x0000))
(assert (= sb-adr_0_1 #x0000))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_0_0 #x0000))
(assert (= sb-val_0_1 #x0000))

; store buffer full variables - sb-full_<step>_<thread>
(assert (not sb-full_0_0))
(assert (not sb-full_0_1))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert stmt_0_0_0)
(assert (not stmt_0_0_1))
(assert (not stmt_0_0_2))

(assert stmt_0_1_0)
(assert (not stmt_0_1_1))
(assert (not stmt_0_1_2))

; halt variables - halt_<step>_<thread>
(assert (not halt_0_0))
(assert (not halt_0_1))

; exit flag variable - exit_<step>
(assert (not exit_0))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_0_0 flush_0_0 thread_0_1 flush_0_1 exit_0))
(assert (or (not thread_0_0) (not flush_0_0)))
(assert (or (not thread_0_0) (not thread_0_1)))
(assert (or (not thread_0_0) (not flush_0_1)))
(assert (or (not thread_0_0) (not exit_0)))
(assert (or (not flush_0_0) (not thread_0_1)))
(assert (or (not flush_0_0) (not flush_0_1)))
(assert (or (not flush_0_0) (not exit_0)))
(assert (or (not thread_0_1) (not flush_0_1)))
(assert (or (not thread_0_1) (not exit_0)))
(assert (or (not flush_0_1) (not exit_0)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_0_0 (=> stmt_0_0_1 (not thread_0_0)) (not flush_0_0)))
(assert (ite sb-full_0_1 (=> stmt_0_1_1 (not thread_0_1)) (not flush_0_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_0_0 (not thread_0_0)))
(assert (=> halt_0_1 (not thread_0_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_1_0 () (_ BitVec 16))
(declare-fun accu_1_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_1_0 () (_ BitVec 16))
(declare-fun mem_1_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_1_0 () (_ BitVec 16))
(declare-fun sb-adr_1_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_1_0 () (_ BitVec 16))
(declare-fun sb-val_1_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_1_0 () Bool)
(declare-fun sb-full_1_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_1_0_0 () Bool)
(declare-fun stmt_1_0_1 () Bool)
(declare-fun stmt_1_0_2 () Bool)

(declare-fun stmt_1_1_0 () Bool)
(declare-fun stmt_1_1_1 () Bool)
(declare-fun stmt_1_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_1_0 () Bool)
(declare-fun halt_1_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_1 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_1_0 () Bool)
(declare-fun thread_1_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_1_0_0 () Bool)
(declare-fun exec_1_0_1 () Bool)
(declare-fun exec_1_0_2 () Bool)

(declare-fun exec_1_1_0 () Bool)
(declare-fun exec_1_1_1 () Bool)
(declare-fun exec_1_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_1_0 () Bool)
(declare-fun flush_1_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))
(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))
(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))

(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))
(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))
(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_0_0_0 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (ite (not (= accu_0_0 #x0000)) (not stmt_1_0_1) stmt_1_0_1) (ite (not (= accu_0_0 #x0000)) stmt_1_0_2 (not stmt_1_0_2))) (= halt_1_0 halt_0_0) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_0_1 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) (not stmt_1_0_2)) (and halt_1_0 (ite halt_1_1 (and exit_1 (= exit-code #x0000)) (not exit_1))) (= heap_1 heap_0))))

(assert (=> exec_0_0_2 (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 sb-full_0_0) (and (not stmt_1_0_0) (not stmt_1_0_1) stmt_1_0_2) (= halt_1_0 halt_0_0) (= heap_1 heap_0) exit_1 (= exit-code #x0001))))

(assert (=> (not thread_0_0) (and (= accu_1_0 accu_0_0) (= mem_1_0 mem_0_0) (= sb-adr_1_0 sb-adr_0_0) (= sb-val_1_0 sb-val_0_0) (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) (and (= stmt_1_0_0 stmt_0_0_0) (= stmt_1_0_1 stmt_0_0_1) (= stmt_1_0_2 stmt_0_0_2)) (= halt_1_0 halt_0_0))))

(assert (=> flush_0_0 (and (not sb-full_1_0) (= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) (not exit_1))))

; thread 1
(assert (=> exec_0_1_0 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (ite (not (= accu_0_1 #x0000)) (not stmt_1_1_1) stmt_1_1_1) (ite (not (= accu_0_1 #x0000)) stmt_1_1_2 (not stmt_1_1_2))) (= halt_1_1 halt_0_1) (= heap_1 heap_0) (not exit_1))))

(assert (=> exec_0_1_1 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (not stmt_1_1_1) (not stmt_1_1_2)) (and halt_1_1 (ite halt_1_0 (and exit_1 (= exit-code #x0000)) (not exit_1))) (= heap_1 heap_0))))

(assert (=> exec_0_1_2 (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 sb-full_0_1) (and (not stmt_1_1_0) (not stmt_1_1_1) stmt_1_1_2) (= halt_1_1 halt_0_1) (= heap_1 heap_0) exit_1 (= exit-code #x0001))))

(assert (=> (not thread_0_1) (and (= accu_1_1 accu_0_1) (= mem_1_1 mem_0_1) (= sb-adr_1_1 sb-adr_0_1) (= sb-val_1_1 sb-val_0_1) (= sb-full_1_1 (ite flush_0_1 false sb-full_0_1)) (and (= stmt_1_1_0 stmt_0_1_0) (= stmt_1_1_1 stmt_0_1_1) (= stmt_1_1_2 stmt_0_1_2)) (= halt_1_1 halt_0_1))))

(assert (=> flush_0_1 (and (not sb-full_1_1) (= heap_1 (store heap_0 sb-adr_0_1 sb-val_0_1)) (not exit_1))))

; exited
(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1 exit_1))
(assert (or (not thread_1_0) (not flush_1_0)))
(assert (or (not thread_1_0) (not thread_1_1)))
(assert (or (not thread_1_0) (not flush_1_1)))
(assert (or (not thread_1_0) (not exit_1)))
(assert (or (not flush_1_0) (not thread_1_1)))
(assert (or (not flush_1_0) (not flush_1_1)))
(assert (or (not flush_1_0) (not exit_1)))
(assert (or (not thread_1_1) (not flush_1_1)))
(assert (or (not thread_1_1) (not exit_1)))
(assert (or (not flush_1_1) (not exit_1)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_1_0 (=> stmt_1_0_1 (not thread_1_0)) (not flush_1_0)))
(assert (ite sb-full_1_1 (=> stmt_1_1_1 (not thread_1_1)) (not flush_1_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_1_0 (not thread_1_0)))
(assert (=> halt_1_1 (not thread_1_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_2_0 () (_ BitVec 16))
(declare-fun accu_2_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_2_0 () (_ BitVec 16))
(declare-fun mem_2_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_2_0 () (_ BitVec 16))
(declare-fun sb-adr_2_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_2_0 () (_ BitVec 16))
(declare-fun sb-val_2_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_2_0 () Bool)
(declare-fun sb-full_2_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_2_0_0 () Bool)
(declare-fun stmt_2_0_1 () Bool)
(declare-fun stmt_2_0_2 () Bool)

(declare-fun stmt_2_1_0 () Bool)
(declare-fun stmt_2_1_1 () Bool)
(declare-fun stmt_2_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_2_0 () Bool)
(declare-fun halt_2_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_2 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_2_0 () Bool)
(declare-fun thread_2_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_2_0_0 () Bool)
(declare-fun exec_2_0_1 () Bool)
(declare-fun exec_2_0_2 () Bool)

(declare-fun exec_2_1_0 () Bool)
(declare-fun exec_2_1_1 () Bool)
(declare-fun exec_2_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_2_0 () Bool)
(declare-fun flush_2_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_2_0_0 (and stmt_2_0_0 thread_2_0)))
(assert (= exec_2_0_1 (and stmt_2_0_1 thread_2_0)))
(assert (= exec_2_0_2 (and stmt_2_0_2 thread_2_0)))

(assert (= exec_2_1_0 (and stmt_2_1_0 thread_2_1)))
(assert (= exec_2_1_1 (and stmt_2_1_1 thread_2_1)))
(assert (= exec_2_1_2 (and stmt_2_1_2 thread_2_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_1_0_0 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (ite (not (= accu_1_0 #x0000)) (not stmt_2_0_1) stmt_2_0_1) (ite (not (= accu_1_0 #x0000)) stmt_2_0_2 (not stmt_2_0_2))) (= halt_2_0 halt_1_0) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_0_1 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2)) (and halt_2_0 (ite halt_2_1 (and exit_2 (= exit-code #x0000)) (not exit_2))) (= heap_2 heap_1))))

(assert (=> exec_1_0_2 (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 sb-full_1_0) (and (not stmt_2_0_0) (not stmt_2_0_1) stmt_2_0_2) (= halt_2_0 halt_1_0) (= heap_2 heap_1) exit_2 (= exit-code #x0001))))

(assert (=> (not thread_1_0) (and (= accu_2_0 accu_1_0) (= mem_2_0 mem_1_0) (= sb-adr_2_0 sb-adr_1_0) (= sb-val_2_0 sb-val_1_0) (= sb-full_2_0 (ite flush_1_0 false sb-full_1_0)) (and (= stmt_2_0_0 stmt_1_0_0) (= stmt_2_0_1 stmt_1_0_1) (= stmt_2_0_2 stmt_1_0_2)) (= halt_2_0 halt_1_0))))

(assert (=> flush_1_0 (and (not sb-full_2_0) (= heap_2 (store heap_1 sb-adr_1_0 sb-val_1_0)) (not exit_2))))

; thread 1
(assert (=> exec_1_1_0 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (ite (not (= accu_1_1 #x0000)) (not stmt_2_1_1) stmt_2_1_1) (ite (not (= accu_1_1 #x0000)) stmt_2_1_2 (not stmt_2_1_2))) (= halt_2_1 halt_1_1) (= heap_2 heap_1) (not exit_2))))

(assert (=> exec_1_1_1 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2)) (and halt_2_1 (ite halt_2_0 (and exit_2 (= exit-code #x0000)) (not exit_2))) (= heap_2 heap_1))))

(assert (=> exec_1_1_2 (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 sb-full_1_1) (and (not stmt_2_1_0) (not stmt_2_1_1) stmt_2_1_2) (= halt_2_1 halt_1_1) (= heap_2 heap_1) exit_2 (= exit-code #x0001))))

(assert (=> (not thread_1_1) (and (= accu_2_1 accu_1_1) (= mem_2_1 mem_1_1) (= sb-adr_2_1 sb-adr_1_1) (= sb-val_2_1 sb-val_1_1) (= sb-full_2_1 (ite flush_1_1 false sb-full_1_1)) (and (= stmt_2_1_0 stmt_1_1_0) (= stmt_2_1_1 stmt_1_1_1) (= stmt_2_1_2 stmt_1_1_2)) (= halt_2_1 halt_1_1))))

(assert (=> flush_1_1 (and (not sb-full_2_1) (= heap_2 (store heap_1 sb-adr_1_1 sb-val_1_1)) (not exit_2))))

; exited
(assert (=> exit_1 (and (= heap_2 heap_1) exit_2)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_2_0 flush_2_0 thread_2_1 flush_2_1 exit_2))
(assert (or (not thread_2_0) (not flush_2_0)))
(assert (or (not thread_2_0) (not thread_2_1)))
(assert (or (not thread_2_0) (not flush_2_1)))
(assert (or (not thread_2_0) (not exit_2)))
(assert (or (not flush_2_0) (not thread_2_1)))
(assert (or (not flush_2_0) (not flush_2_1)))
(assert (or (not flush_2_0) (not exit_2)))
(assert (or (not thread_2_1) (not flush_2_1)))
(assert (or (not thread_2_1) (not exit_2)))
(assert (or (not flush_2_1) (not exit_2)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_2_0 (=> stmt_2_0_1 (not thread_2_0)) (not flush_2_0)))
(assert (ite sb-full_2_1 (=> stmt_2_1_1 (not thread_2_1)) (not flush_2_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_2_0 (not thread_2_0)))
(assert (=> halt_2_1 (not thread_2_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_3_0 () (_ BitVec 16))
(declare-fun accu_3_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_3_0 () (_ BitVec 16))
(declare-fun mem_3_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_3_0 () (_ BitVec 16))
(declare-fun sb-adr_3_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_3_0 () (_ BitVec 16))
(declare-fun sb-val_3_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_3_0 () Bool)
(declare-fun sb-full_3_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_3_0_0 () Bool)
(declare-fun stmt_3_0_1 () Bool)
(declare-fun stmt_3_0_2 () Bool)

(declare-fun stmt_3_1_0 () Bool)
(declare-fun stmt_3_1_1 () Bool)
(declare-fun stmt_3_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_3_0 () Bool)
(declare-fun halt_3_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_3 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_3 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_3_0 () Bool)
(declare-fun thread_3_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_3_0_0 () Bool)
(declare-fun exec_3_0_1 () Bool)
(declare-fun exec_3_0_2 () Bool)

(declare-fun exec_3_1_0 () Bool)
(declare-fun exec_3_1_1 () Bool)
(declare-fun exec_3_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_3_0 () Bool)
(declare-fun flush_3_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_3_0_0 (and stmt_3_0_0 thread_3_0)))
(assert (= exec_3_0_1 (and stmt_3_0_1 thread_3_0)))
(assert (= exec_3_0_2 (and stmt_3_0_2 thread_3_0)))

(assert (= exec_3_1_0 (and stmt_3_1_0 thread_3_1)))
(assert (= exec_3_1_1 (and stmt_3_1_1 thread_3_1)))
(assert (= exec_3_1_2 (and stmt_3_1_2 thread_3_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_2_0_0 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (ite (not (= accu_2_0 #x0000)) (not stmt_3_0_1) stmt_3_0_1) (ite (not (= accu_2_0 #x0000)) stmt_3_0_2 (not stmt_3_0_2))) (= halt_3_0 halt_2_0) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_0_1 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) (not stmt_3_0_2)) (and halt_3_0 (ite halt_3_1 (and exit_3 (= exit-code #x0000)) (not exit_3))) (= heap_3 heap_2))))

(assert (=> exec_2_0_2 (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 sb-full_2_0) (and (not stmt_3_0_0) (not stmt_3_0_1) stmt_3_0_2) (= halt_3_0 halt_2_0) (= heap_3 heap_2) exit_3 (= exit-code #x0001))))

(assert (=> (not thread_2_0) (and (= accu_3_0 accu_2_0) (= mem_3_0 mem_2_0) (= sb-adr_3_0 sb-adr_2_0) (= sb-val_3_0 sb-val_2_0) (= sb-full_3_0 (ite flush_2_0 false sb-full_2_0)) (and (= stmt_3_0_0 stmt_2_0_0) (= stmt_3_0_1 stmt_2_0_1) (= stmt_3_0_2 stmt_2_0_2)) (= halt_3_0 halt_2_0))))

(assert (=> flush_2_0 (and (not sb-full_3_0) (= heap_3 (store heap_2 sb-adr_2_0 sb-val_2_0)) (not exit_3))))

; thread 1
(assert (=> exec_2_1_0 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (ite (not (= accu_2_1 #x0000)) (not stmt_3_1_1) stmt_3_1_1) (ite (not (= accu_2_1 #x0000)) stmt_3_1_2 (not stmt_3_1_2))) (= halt_3_1 halt_2_1) (= heap_3 heap_2) (not exit_3))))

(assert (=> exec_2_1_1 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (not stmt_3_1_1) (not stmt_3_1_2)) (and halt_3_1 (ite halt_3_0 (and exit_3 (= exit-code #x0000)) (not exit_3))) (= heap_3 heap_2))))

(assert (=> exec_2_1_2 (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 sb-full_2_1) (and (not stmt_3_1_0) (not stmt_3_1_1) stmt_3_1_2) (= halt_3_1 halt_2_1) (= heap_3 heap_2) exit_3 (= exit-code #x0001))))

(assert (=> (not thread_2_1) (and (= accu_3_1 accu_2_1) (= mem_3_1 mem_2_1) (= sb-adr_3_1 sb-adr_2_1) (= sb-val_3_1 sb-val_2_1) (= sb-full_3_1 (ite flush_2_1 false sb-full_2_1)) (and (= stmt_3_1_0 stmt_2_1_0) (= stmt_3_1_1 stmt_2_1_1) (= stmt_3_1_2 stmt_2_1_2)) (= halt_3_1 halt_2_1))))

(assert (=> flush_2_1 (and (not sb-full_3_1) (= heap_3 (store heap_2 sb-adr_2_1 sb-val_2_1)) (not exit_3))))

; exited
(assert (=> exit_2 (and (= heap_3 heap_2) exit_3)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_3_0 flush_3_0 thread_3_1 flush_3_1 exit_3))
(assert (or (not thread_3_0) (not flush_3_0)))
(assert (or (not thread_3_0) (not thread_3_1)))
(assert (or (not thread_3_0) (not flush_3_1)))
(assert (or (not thread_3_0) (not exit_3)))
(assert (or (not flush_3_0) (not thread_3_1)))
(assert (or (not flush_3_0) (not flush_3_1)))
(assert (or (not flush_3_0) (not exit_3)))
(assert (or (not thread_3_1) (not flush_3_1)))
(assert (or (not thread_3_1) (not exit_3)))
(assert (or (not flush_3_1) (not exit_3)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_3_0 (=> stmt_3_0_1 (not thread_3_0)) (not flush_3_0)))
(assert (ite sb-full_3_1 (=> stmt_3_1_1 (not thread_3_1)) (not flush_3_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_3_0 (not thread_3_0)))
(assert (=> halt_3_1 (not thread_3_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_4_0 () (_ BitVec 16))
(declare-fun accu_4_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_4_0 () (_ BitVec 16))
(declare-fun mem_4_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_4_0 () (_ BitVec 16))
(declare-fun sb-adr_4_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_4_0 () (_ BitVec 16))
(declare-fun sb-val_4_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_4_0 () Bool)
(declare-fun sb-full_4_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_4_0_0 () Bool)
(declare-fun stmt_4_0_1 () Bool)
(declare-fun stmt_4_0_2 () Bool)

(declare-fun stmt_4_1_0 () Bool)
(declare-fun stmt_4_1_1 () Bool)
(declare-fun stmt_4_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_4_0 () Bool)
(declare-fun halt_4_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_4 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_4 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_4_0 () Bool)
(declare-fun thread_4_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_4_0_0 () Bool)
(declare-fun exec_4_0_1 () Bool)
(declare-fun exec_4_0_2 () Bool)

(declare-fun exec_4_1_0 () Bool)
(declare-fun exec_4_1_1 () Bool)
(declare-fun exec_4_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_4_0 () Bool)
(declare-fun flush_4_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_4_0_0 (and stmt_4_0_0 thread_4_0)))
(assert (= exec_4_0_1 (and stmt_4_0_1 thread_4_0)))
(assert (= exec_4_0_2 (and stmt_4_0_2 thread_4_0)))

(assert (= exec_4_1_0 (and stmt_4_1_0 thread_4_1)))
(assert (= exec_4_1_1 (and stmt_4_1_1 thread_4_1)))
(assert (= exec_4_1_2 (and stmt_4_1_2 thread_4_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_3_0_0 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (ite (not (= accu_3_0 #x0000)) (not stmt_4_0_1) stmt_4_0_1) (ite (not (= accu_3_0 #x0000)) stmt_4_0_2 (not stmt_4_0_2))) (= halt_4_0 halt_3_0) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_0_1 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) (not stmt_4_0_2)) (and halt_4_0 (ite halt_4_1 (and exit_4 (= exit-code #x0000)) (not exit_4))) (= heap_4 heap_3))))

(assert (=> exec_3_0_2 (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 sb-full_3_0) (and (not stmt_4_0_0) (not stmt_4_0_1) stmt_4_0_2) (= halt_4_0 halt_3_0) (= heap_4 heap_3) exit_4 (= exit-code #x0001))))

(assert (=> (not thread_3_0) (and (= accu_4_0 accu_3_0) (= mem_4_0 mem_3_0) (= sb-adr_4_0 sb-adr_3_0) (= sb-val_4_0 sb-val_3_0) (= sb-full_4_0 (ite flush_3_0 false sb-full_3_0)) (and (= stmt_4_0_0 stmt_3_0_0) (= stmt_4_0_1 stmt_3_0_1) (= stmt_4_0_2 stmt_3_0_2)) (= halt_4_0 halt_3_0))))

(assert (=> flush_3_0 (and (not sb-full_4_0) (= heap_4 (store heap_3 sb-adr_3_0 sb-val_3_0)) (not exit_4))))

; thread 1
(assert (=> exec_3_1_0 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (ite (not (= accu_3_1 #x0000)) (not stmt_4_1_1) stmt_4_1_1) (ite (not (= accu_3_1 #x0000)) stmt_4_1_2 (not stmt_4_1_2))) (= halt_4_1 halt_3_1) (= heap_4 heap_3) (not exit_4))))

(assert (=> exec_3_1_1 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (not stmt_4_1_1) (not stmt_4_1_2)) (and halt_4_1 (ite halt_4_0 (and exit_4 (= exit-code #x0000)) (not exit_4))) (= heap_4 heap_3))))

(assert (=> exec_3_1_2 (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 sb-full_3_1) (and (not stmt_4_1_0) (not stmt_4_1_1) stmt_4_1_2) (= halt_4_1 halt_3_1) (= heap_4 heap_3) exit_4 (= exit-code #x0001))))

(assert (=> (not thread_3_1) (and (= accu_4_1 accu_3_1) (= mem_4_1 mem_3_1) (= sb-adr_4_1 sb-adr_3_1) (= sb-val_4_1 sb-val_3_1) (= sb-full_4_1 (ite flush_3_1 false sb-full_3_1)) (and (= stmt_4_1_0 stmt_3_1_0) (= stmt_4_1_1 stmt_3_1_1) (= stmt_4_1_2 stmt_3_1_2)) (= halt_4_1 halt_3_1))))

(assert (=> flush_3_1 (and (not sb-full_4_1) (= heap_4 (store heap_3 sb-adr_3_1 sb-val_3_1)) (not exit_4))))

; exited
(assert (=> exit_3 (and (= heap_4 heap_3) exit_4)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_4_0 flush_4_0 thread_4_1 flush_4_1 exit_4))
(assert (or (not thread_4_0) (not flush_4_0)))
(assert (or (not thread_4_0) (not thread_4_1)))
(assert (or (not thread_4_0) (not flush_4_1)))
(assert (or (not thread_4_0) (not exit_4)))
(assert (or (not flush_4_0) (not thread_4_1)))
(assert (or (not flush_4_0) (not flush_4_1)))
(assert (or (not flush_4_0) (not exit_4)))
(assert (or (not thread_4_1) (not flush_4_1)))
(assert (or (not thread_4_1) (not exit_4)))
(assert (or (not flush_4_1) (not exit_4)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_4_0 (=> stmt_4_0_1 (not thread_4_0)) (not flush_4_0)))
(assert (ite sb-full_4_1 (=> stmt_4_1_1 (not thread_4_1)) (not flush_4_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_4_0 (not thread_4_0)))
(assert (=> halt_4_1 (not thread_4_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_5_0 () (_ BitVec 16))
(declare-fun accu_5_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_5_0 () (_ BitVec 16))
(declare-fun mem_5_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_5_0 () (_ BitVec 16))
(declare-fun sb-adr_5_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_5_0 () (_ BitVec 16))
(declare-fun sb-val_5_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_5_0 () Bool)
(declare-fun sb-full_5_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_5_0_0 () Bool)
(declare-fun stmt_5_0_1 () Bool)
(declare-fun stmt_5_0_2 () Bool)

(declare-fun stmt_5_1_0 () Bool)
(declare-fun stmt_5_1_1 () Bool)
(declare-fun stmt_5_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_5_0 () Bool)
(declare-fun halt_5_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_5 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_5 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_5_0 () Bool)
(declare-fun thread_5_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_5_0_0 () Bool)
(declare-fun exec_5_0_1 () Bool)
(declare-fun exec_5_0_2 () Bool)

(declare-fun exec_5_1_0 () Bool)
(declare-fun exec_5_1_1 () Bool)
(declare-fun exec_5_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_5_0 () Bool)
(declare-fun flush_5_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_5_0_0 (and stmt_5_0_0 thread_5_0)))
(assert (= exec_5_0_1 (and stmt_5_0_1 thread_5_0)))
(assert (= exec_5_0_2 (and stmt_5_0_2 thread_5_0)))

(assert (= exec_5_1_0 (and stmt_5_1_0 thread_5_1)))
(assert (= exec_5_1_1 (and stmt_5_1_1 thread_5_1)))
(assert (= exec_5_1_2 (and stmt_5_1_2 thread_5_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_4_0_0 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (ite (not (= accu_4_0 #x0000)) (not stmt_5_0_1) stmt_5_0_1) (ite (not (= accu_4_0 #x0000)) stmt_5_0_2 (not stmt_5_0_2))) (= halt_5_0 halt_4_0) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_0_1 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) (not stmt_5_0_2)) (and halt_5_0 (ite halt_5_1 (and exit_5 (= exit-code #x0000)) (not exit_5))) (= heap_5 heap_4))))

(assert (=> exec_4_0_2 (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 sb-full_4_0) (and (not stmt_5_0_0) (not stmt_5_0_1) stmt_5_0_2) (= halt_5_0 halt_4_0) (= heap_5 heap_4) exit_5 (= exit-code #x0001))))

(assert (=> (not thread_4_0) (and (= accu_5_0 accu_4_0) (= mem_5_0 mem_4_0) (= sb-adr_5_0 sb-adr_4_0) (= sb-val_5_0 sb-val_4_0) (= sb-full_5_0 (ite flush_4_0 false sb-full_4_0)) (and (= stmt_5_0_0 stmt_4_0_0) (= stmt_5_0_1 stmt_4_0_1) (= stmt_5_0_2 stmt_4_0_2)) (= halt_5_0 halt_4_0))))

(assert (=> flush_4_0 (and (not sb-full_5_0) (= heap_5 (store heap_4 sb-adr_4_0 sb-val_4_0)) (not exit_5))))

; thread 1
(assert (=> exec_4_1_0 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (ite (not (= accu_4_1 #x0000)) (not stmt_5_1_1) stmt_5_1_1) (ite (not (= accu_4_1 #x0000)) stmt_5_1_2 (not stmt_5_1_2))) (= halt_5_1 halt_4_1) (= heap_5 heap_4) (not exit_5))))

(assert (=> exec_4_1_1 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (not stmt_5_1_1) (not stmt_5_1_2)) (and halt_5_1 (ite halt_5_0 (and exit_5 (= exit-code #x0000)) (not exit_5))) (= heap_5 heap_4))))

(assert (=> exec_4_1_2 (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 sb-full_4_1) (and (not stmt_5_1_0) (not stmt_5_1_1) stmt_5_1_2) (= halt_5_1 halt_4_1) (= heap_5 heap_4) exit_5 (= exit-code #x0001))))

(assert (=> (not thread_4_1) (and (= accu_5_1 accu_4_1) (= mem_5_1 mem_4_1) (= sb-adr_5_1 sb-adr_4_1) (= sb-val_5_1 sb-val_4_1) (= sb-full_5_1 (ite flush_4_1 false sb-full_4_1)) (and (= stmt_5_1_0 stmt_4_1_0) (= stmt_5_1_1 stmt_4_1_1) (= stmt_5_1_2 stmt_4_1_2)) (= halt_5_1 halt_4_1))))

(assert (=> flush_4_1 (and (not sb-full_5_1) (= heap_5 (store heap_4 sb-adr_4_1 sb-val_4_1)) (not exit_5))))

; exited
(assert (=> exit_4 (and (= heap_5 heap_4) exit_5)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_5_0 flush_5_0 thread_5_1 flush_5_1 exit_5))
(assert (or (not thread_5_0) (not flush_5_0)))
(assert (or (not thread_5_0) (not thread_5_1)))
(assert (or (not thread_5_0) (not flush_5_1)))
(assert (or (not thread_5_0) (not exit_5)))
(assert (or (not flush_5_0) (not thread_5_1)))
(assert (or (not flush_5_0) (not flush_5_1)))
(assert (or (not flush_5_0) (not exit_5)))
(assert (or (not thread_5_1) (not flush_5_1)))
(assert (or (not thread_5_1) (not exit_5)))
(assert (or (not flush_5_1) (not exit_5)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_5_0 (=> stmt_5_0_1 (not thread_5_0)) (not flush_5_0)))
(assert (ite sb-full_5_1 (=> stmt_5_1_1 (not thread_5_1)) (not flush_5_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_5_0 (not thread_5_0)))
(assert (=> halt_5_1 (not thread_5_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_6_0 () (_ BitVec 16))
(declare-fun accu_6_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_6_0 () (_ BitVec 16))
(declare-fun mem_6_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_6_0 () (_ BitVec 16))
(declare-fun sb-adr_6_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_6_0 () (_ BitVec 16))
(declare-fun sb-val_6_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_6_0 () Bool)
(declare-fun sb-full_6_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_0_0 () Bool)
(declare-fun stmt_6_0_1 () Bool)
(declare-fun stmt_6_0_2 () Bool)

(declare-fun stmt_6_1_0 () Bool)
(declare-fun stmt_6_1_1 () Bool)
(declare-fun stmt_6_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_6_0 () Bool)
(declare-fun halt_6_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_6 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_0 () Bool)
(declare-fun thread_6_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_0_0 () Bool)
(declare-fun exec_6_0_1 () Bool)
(declare-fun exec_6_0_2 () Bool)

(declare-fun exec_6_1_0 () Bool)
(declare-fun exec_6_1_1 () Bool)
(declare-fun exec_6_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_6_0 () Bool)
(declare-fun flush_6_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_6_0_0 (and stmt_6_0_0 thread_6_0)))
(assert (= exec_6_0_1 (and stmt_6_0_1 thread_6_0)))
(assert (= exec_6_0_2 (and stmt_6_0_2 thread_6_0)))

(assert (= exec_6_1_0 (and stmt_6_1_0 thread_6_1)))
(assert (= exec_6_1_1 (and stmt_6_1_1 thread_6_1)))
(assert (= exec_6_1_2 (and stmt_6_1_2 thread_6_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_5_0_0 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (ite (not (= accu_5_0 #x0000)) (not stmt_6_0_1) stmt_6_0_1) (ite (not (= accu_5_0 #x0000)) stmt_6_0_2 (not stmt_6_0_2))) (= halt_6_0 halt_5_0) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_0_1 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (not stmt_6_0_1) (not stmt_6_0_2)) (and halt_6_0 (ite halt_6_1 (and exit_6 (= exit-code #x0000)) (not exit_6))) (= heap_6 heap_5))))

(assert (=> exec_5_0_2 (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 sb-full_5_0) (and (not stmt_6_0_0) (not stmt_6_0_1) stmt_6_0_2) (= halt_6_0 halt_5_0) (= heap_6 heap_5) exit_6 (= exit-code #x0001))))

(assert (=> (not thread_5_0) (and (= accu_6_0 accu_5_0) (= mem_6_0 mem_5_0) (= sb-adr_6_0 sb-adr_5_0) (= sb-val_6_0 sb-val_5_0) (= sb-full_6_0 (ite flush_5_0 false sb-full_5_0)) (and (= stmt_6_0_0 stmt_5_0_0) (= stmt_6_0_1 stmt_5_0_1) (= stmt_6_0_2 stmt_5_0_2)) (= halt_6_0 halt_5_0))))

(assert (=> flush_5_0 (and (not sb-full_6_0) (= heap_6 (store heap_5 sb-adr_5_0 sb-val_5_0)) (not exit_6))))

; thread 1
(assert (=> exec_5_1_0 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (ite (not (= accu_5_1 #x0000)) (not stmt_6_1_1) stmt_6_1_1) (ite (not (= accu_5_1 #x0000)) stmt_6_1_2 (not stmt_6_1_2))) (= halt_6_1 halt_5_1) (= heap_6 heap_5) (not exit_6))))

(assert (=> exec_5_1_1 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (not stmt_6_1_1) (not stmt_6_1_2)) (and halt_6_1 (ite halt_6_0 (and exit_6 (= exit-code #x0000)) (not exit_6))) (= heap_6 heap_5))))

(assert (=> exec_5_1_2 (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 sb-full_5_1) (and (not stmt_6_1_0) (not stmt_6_1_1) stmt_6_1_2) (= halt_6_1 halt_5_1) (= heap_6 heap_5) exit_6 (= exit-code #x0001))))

(assert (=> (not thread_5_1) (and (= accu_6_1 accu_5_1) (= mem_6_1 mem_5_1) (= sb-adr_6_1 sb-adr_5_1) (= sb-val_6_1 sb-val_5_1) (= sb-full_6_1 (ite flush_5_1 false sb-full_5_1)) (and (= stmt_6_1_0 stmt_5_1_0) (= stmt_6_1_1 stmt_5_1_1) (= stmt_6_1_2 stmt_5_1_2)) (= halt_6_1 halt_5_1))))

(assert (=> flush_5_1 (and (not sb-full_6_1) (= heap_6 (store heap_5 sb-adr_5_1 sb-val_5_1)) (not exit_6))))

; exited
(assert (=> exit_5 (and (= heap_6 heap_5) exit_6)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_6_0 flush_6_0 thread_6_1 flush_6_1 exit_6))
(assert (or (not thread_6_0) (not flush_6_0)))
(assert (or (not thread_6_0) (not thread_6_1)))
(assert (or (not thread_6_0) (not flush_6_1)))
(assert (or (not thread_6_0) (not exit_6)))
(assert (or (not flush_6_0) (not thread_6_1)))
(assert (or (not flush_6_0) (not flush_6_1)))
(assert (or (not flush_6_0) (not exit_6)))
(assert (or (not thread_6_1) (not flush_6_1)))
(assert (or (not thread_6_1) (not exit_6)))
(assert (or (not flush_6_1) (not exit_6)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_6_0 (=> stmt_6_0_1 (not thread_6_0)) (not flush_6_0)))
(assert (ite sb-full_6_1 (=> stmt_6_1_1 (not thread_6_1)) (not flush_6_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_6_0 (not thread_6_0)))
(assert (=> halt_6_1 (not thread_6_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_7_0 () (_ BitVec 16))
(declare-fun accu_7_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_7_0 () (_ BitVec 16))
(declare-fun mem_7_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_7_0 () (_ BitVec 16))
(declare-fun sb-adr_7_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_7_0 () (_ BitVec 16))
(declare-fun sb-val_7_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_7_0 () Bool)
(declare-fun sb-full_7_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_0_0 () Bool)
(declare-fun stmt_7_0_1 () Bool)
(declare-fun stmt_7_0_2 () Bool)

(declare-fun stmt_7_1_0 () Bool)
(declare-fun stmt_7_1_1 () Bool)
(declare-fun stmt_7_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_7_0 () Bool)
(declare-fun halt_7_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_7 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_0 () Bool)
(declare-fun thread_7_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_0_0 () Bool)
(declare-fun exec_7_0_1 () Bool)
(declare-fun exec_7_0_2 () Bool)

(declare-fun exec_7_1_0 () Bool)
(declare-fun exec_7_1_1 () Bool)
(declare-fun exec_7_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_7_0 () Bool)
(declare-fun flush_7_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_7_0_0 (and stmt_7_0_0 thread_7_0)))
(assert (= exec_7_0_1 (and stmt_7_0_1 thread_7_0)))
(assert (= exec_7_0_2 (and stmt_7_0_2 thread_7_0)))

(assert (= exec_7_1_0 (and stmt_7_1_0 thread_7_1)))
(assert (= exec_7_1_1 (and stmt_7_1_1 thread_7_1)))
(assert (= exec_7_1_2 (and stmt_7_1_2 thread_7_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_6_0_0 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (ite (not (= accu_6_0 #x0000)) (not stmt_7_0_1) stmt_7_0_1) (ite (not (= accu_6_0 #x0000)) stmt_7_0_2 (not stmt_7_0_2))) (= halt_7_0 halt_6_0) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_0_1 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (not stmt_7_0_1) (not stmt_7_0_2)) (and halt_7_0 (ite halt_7_1 (and exit_7 (= exit-code #x0000)) (not exit_7))) (= heap_7 heap_6))))

(assert (=> exec_6_0_2 (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 sb-full_6_0) (and (not stmt_7_0_0) (not stmt_7_0_1) stmt_7_0_2) (= halt_7_0 halt_6_0) (= heap_7 heap_6) exit_7 (= exit-code #x0001))))

(assert (=> (not thread_6_0) (and (= accu_7_0 accu_6_0) (= mem_7_0 mem_6_0) (= sb-adr_7_0 sb-adr_6_0) (= sb-val_7_0 sb-val_6_0) (= sb-full_7_0 (ite flush_6_0 false sb-full_6_0)) (and (= stmt_7_0_0 stmt_6_0_0) (= stmt_7_0_1 stmt_6_0_1) (= stmt_7_0_2 stmt_6_0_2)) (= halt_7_0 halt_6_0))))

(assert (=> flush_6_0 (and (not sb-full_7_0) (= heap_7 (store heap_6 sb-adr_6_0 sb-val_6_0)) (not exit_7))))

; thread 1
(assert (=> exec_6_1_0 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (ite (not (= accu_6_1 #x0000)) (not stmt_7_1_1) stmt_7_1_1) (ite (not (= accu_6_1 #x0000)) stmt_7_1_2 (not stmt_7_1_2))) (= halt_7_1 halt_6_1) (= heap_7 heap_6) (not exit_7))))

(assert (=> exec_6_1_1 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (not stmt_7_1_1) (not stmt_7_1_2)) (and halt_7_1 (ite halt_7_0 (and exit_7 (= exit-code #x0000)) (not exit_7))) (= heap_7 heap_6))))

(assert (=> exec_6_1_2 (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 sb-full_6_1) (and (not stmt_7_1_0) (not stmt_7_1_1) stmt_7_1_2) (= halt_7_1 halt_6_1) (= heap_7 heap_6) exit_7 (= exit-code #x0001))))

(assert (=> (not thread_6_1) (and (= accu_7_1 accu_6_1) (= mem_7_1 mem_6_1) (= sb-adr_7_1 sb-adr_6_1) (= sb-val_7_1 sb-val_6_1) (= sb-full_7_1 (ite flush_6_1 false sb-full_6_1)) (and (= stmt_7_1_0 stmt_6_1_0) (= stmt_7_1_1 stmt_6_1_1) (= stmt_7_1_2 stmt_6_1_2)) (= halt_7_1 halt_6_1))))

(assert (=> flush_6_1 (and (not sb-full_7_1) (= heap_7 (store heap_6 sb-adr_6_1 sb-val_6_1)) (not exit_7))))

; exited
(assert (=> exit_6 (and (= heap_7 heap_6) exit_7)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_7_0 flush_7_0 thread_7_1 flush_7_1 exit_7))
(assert (or (not thread_7_0) (not flush_7_0)))
(assert (or (not thread_7_0) (not thread_7_1)))
(assert (or (not thread_7_0) (not flush_7_1)))
(assert (or (not thread_7_0) (not exit_7)))
(assert (or (not flush_7_0) (not thread_7_1)))
(assert (or (not flush_7_0) (not flush_7_1)))
(assert (or (not flush_7_0) (not exit_7)))
(assert (or (not thread_7_1) (not flush_7_1)))
(assert (or (not thread_7_1) (not exit_7)))
(assert (or (not flush_7_1) (not exit_7)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_7_0 (=> stmt_7_0_1 (not thread_7_0)) (not flush_7_0)))
(assert (ite sb-full_7_1 (=> stmt_7_1_1 (not thread_7_1)) (not flush_7_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_7_0 (not thread_7_0)))
(assert (=> halt_7_1 (not thread_7_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_8_0 () (_ BitVec 16))
(declare-fun accu_8_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_8_0 () (_ BitVec 16))
(declare-fun mem_8_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_8_0 () (_ BitVec 16))
(declare-fun sb-adr_8_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_8_0 () (_ BitVec 16))
(declare-fun sb-val_8_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_8_0 () Bool)
(declare-fun sb-full_8_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_0_0 () Bool)
(declare-fun stmt_8_0_1 () Bool)
(declare-fun stmt_8_0_2 () Bool)

(declare-fun stmt_8_1_0 () Bool)
(declare-fun stmt_8_1_1 () Bool)
(declare-fun stmt_8_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_8_0 () Bool)
(declare-fun halt_8_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_8 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_0 () Bool)
(declare-fun thread_8_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_0_0 () Bool)
(declare-fun exec_8_0_1 () Bool)
(declare-fun exec_8_0_2 () Bool)

(declare-fun exec_8_1_0 () Bool)
(declare-fun exec_8_1_1 () Bool)
(declare-fun exec_8_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_8_0 () Bool)
(declare-fun flush_8_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_8_0_0 (and stmt_8_0_0 thread_8_0)))
(assert (= exec_8_0_1 (and stmt_8_0_1 thread_8_0)))
(assert (= exec_8_0_2 (and stmt_8_0_2 thread_8_0)))

(assert (= exec_8_1_0 (and stmt_8_1_0 thread_8_1)))
(assert (= exec_8_1_1 (and stmt_8_1_1 thread_8_1)))
(assert (= exec_8_1_2 (and stmt_8_1_2 thread_8_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_7_0_0 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (ite (not (= accu_7_0 #x0000)) (not stmt_8_0_1) stmt_8_0_1) (ite (not (= accu_7_0 #x0000)) stmt_8_0_2 (not stmt_8_0_2))) (= halt_8_0 halt_7_0) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_0_1 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (not stmt_8_0_1) (not stmt_8_0_2)) (and halt_8_0 (ite halt_8_1 (and exit_8 (= exit-code #x0000)) (not exit_8))) (= heap_8 heap_7))))

(assert (=> exec_7_0_2 (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 sb-full_7_0) (and (not stmt_8_0_0) (not stmt_8_0_1) stmt_8_0_2) (= halt_8_0 halt_7_0) (= heap_8 heap_7) exit_8 (= exit-code #x0001))))

(assert (=> (not thread_7_0) (and (= accu_8_0 accu_7_0) (= mem_8_0 mem_7_0) (= sb-adr_8_0 sb-adr_7_0) (= sb-val_8_0 sb-val_7_0) (= sb-full_8_0 (ite flush_7_0 false sb-full_7_0)) (and (= stmt_8_0_0 stmt_7_0_0) (= stmt_8_0_1 stmt_7_0_1) (= stmt_8_0_2 stmt_7_0_2)) (= halt_8_0 halt_7_0))))

(assert (=> flush_7_0 (and (not sb-full_8_0) (= heap_8 (store heap_7 sb-adr_7_0 sb-val_7_0)) (not exit_8))))

; thread 1
(assert (=> exec_7_1_0 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (ite (not (= accu_7_1 #x0000)) (not stmt_8_1_1) stmt_8_1_1) (ite (not (= accu_7_1 #x0000)) stmt_8_1_2 (not stmt_8_1_2))) (= halt_8_1 halt_7_1) (= heap_8 heap_7) (not exit_8))))

(assert (=> exec_7_1_1 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (not stmt_8_1_1) (not stmt_8_1_2)) (and halt_8_1 (ite halt_8_0 (and exit_8 (= exit-code #x0000)) (not exit_8))) (= heap_8 heap_7))))

(assert (=> exec_7_1_2 (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 sb-full_7_1) (and (not stmt_8_1_0) (not stmt_8_1_1) stmt_8_1_2) (= halt_8_1 halt_7_1) (= heap_8 heap_7) exit_8 (= exit-code #x0001))))

(assert (=> (not thread_7_1) (and (= accu_8_1 accu_7_1) (= mem_8_1 mem_7_1) (= sb-adr_8_1 sb-adr_7_1) (= sb-val_8_1 sb-val_7_1) (= sb-full_8_1 (ite flush_7_1 false sb-full_7_1)) (and (= stmt_8_1_0 stmt_7_1_0) (= stmt_8_1_1 stmt_7_1_1) (= stmt_8_1_2 stmt_7_1_2)) (= halt_8_1 halt_7_1))))

(assert (=> flush_7_1 (and (not sb-full_8_1) (= heap_8 (store heap_7 sb-adr_7_1 sb-val_7_1)) (not exit_8))))

; exited
(assert (=> exit_7 (and (= heap_8 heap_7) exit_8)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_8_0 flush_8_0 thread_8_1 flush_8_1 exit_8))
(assert (or (not thread_8_0) (not flush_8_0)))
(assert (or (not thread_8_0) (not thread_8_1)))
(assert (or (not thread_8_0) (not flush_8_1)))
(assert (or (not thread_8_0) (not exit_8)))
(assert (or (not flush_8_0) (not thread_8_1)))
(assert (or (not flush_8_0) (not flush_8_1)))
(assert (or (not flush_8_0) (not exit_8)))
(assert (or (not thread_8_1) (not flush_8_1)))
(assert (or (not thread_8_1) (not exit_8)))
(assert (or (not flush_8_1) (not exit_8)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_8_0 (=> stmt_8_0_1 (not thread_8_0)) (not flush_8_0)))
(assert (ite sb-full_8_1 (=> stmt_8_1_1 (not thread_8_1)) (not flush_8_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_8_0 (not thread_8_0)))
(assert (=> halt_8_1 (not thread_8_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_9_0 () (_ BitVec 16))
(declare-fun accu_9_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_9_0 () (_ BitVec 16))
(declare-fun mem_9_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_9_0 () (_ BitVec 16))
(declare-fun sb-adr_9_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_9_0 () (_ BitVec 16))
(declare-fun sb-val_9_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_9_0 () Bool)
(declare-fun sb-full_9_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_9_0_0 () Bool)
(declare-fun stmt_9_0_1 () Bool)
(declare-fun stmt_9_0_2 () Bool)

(declare-fun stmt_9_1_0 () Bool)
(declare-fun stmt_9_1_1 () Bool)
(declare-fun stmt_9_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_9_0 () Bool)
(declare-fun halt_9_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_9 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_9 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_9_0 () Bool)
(declare-fun thread_9_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_9_0_0 () Bool)
(declare-fun exec_9_0_1 () Bool)
(declare-fun exec_9_0_2 () Bool)

(declare-fun exec_9_1_0 () Bool)
(declare-fun exec_9_1_1 () Bool)
(declare-fun exec_9_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_9_0 () Bool)
(declare-fun flush_9_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_9_0_0 (and stmt_9_0_0 thread_9_0)))
(assert (= exec_9_0_1 (and stmt_9_0_1 thread_9_0)))
(assert (= exec_9_0_2 (and stmt_9_0_2 thread_9_0)))

(assert (= exec_9_1_0 (and stmt_9_1_0 thread_9_1)))
(assert (= exec_9_1_1 (and stmt_9_1_1 thread_9_1)))
(assert (= exec_9_1_2 (and stmt_9_1_2 thread_9_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_8_0_0 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (ite (not (= accu_8_0 #x0000)) (not stmt_9_0_1) stmt_9_0_1) (ite (not (= accu_8_0 #x0000)) stmt_9_0_2 (not stmt_9_0_2))) (= halt_9_0 halt_8_0) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_0_1 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (not stmt_9_0_1) (not stmt_9_0_2)) (and halt_9_0 (ite halt_9_1 (and exit_9 (= exit-code #x0000)) (not exit_9))) (= heap_9 heap_8))))

(assert (=> exec_8_0_2 (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 sb-full_8_0) (and (not stmt_9_0_0) (not stmt_9_0_1) stmt_9_0_2) (= halt_9_0 halt_8_0) (= heap_9 heap_8) exit_9 (= exit-code #x0001))))

(assert (=> (not thread_8_0) (and (= accu_9_0 accu_8_0) (= mem_9_0 mem_8_0) (= sb-adr_9_0 sb-adr_8_0) (= sb-val_9_0 sb-val_8_0) (= sb-full_9_0 (ite flush_8_0 false sb-full_8_0)) (and (= stmt_9_0_0 stmt_8_0_0) (= stmt_9_0_1 stmt_8_0_1) (= stmt_9_0_2 stmt_8_0_2)) (= halt_9_0 halt_8_0))))

(assert (=> flush_8_0 (and (not sb-full_9_0) (= heap_9 (store heap_8 sb-adr_8_0 sb-val_8_0)) (not exit_9))))

; thread 1
(assert (=> exec_8_1_0 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (ite (not (= accu_8_1 #x0000)) (not stmt_9_1_1) stmt_9_1_1) (ite (not (= accu_8_1 #x0000)) stmt_9_1_2 (not stmt_9_1_2))) (= halt_9_1 halt_8_1) (= heap_9 heap_8) (not exit_9))))

(assert (=> exec_8_1_1 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (not stmt_9_1_1) (not stmt_9_1_2)) (and halt_9_1 (ite halt_9_0 (and exit_9 (= exit-code #x0000)) (not exit_9))) (= heap_9 heap_8))))

(assert (=> exec_8_1_2 (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 sb-full_8_1) (and (not stmt_9_1_0) (not stmt_9_1_1) stmt_9_1_2) (= halt_9_1 halt_8_1) (= heap_9 heap_8) exit_9 (= exit-code #x0001))))

(assert (=> (not thread_8_1) (and (= accu_9_1 accu_8_1) (= mem_9_1 mem_8_1) (= sb-adr_9_1 sb-adr_8_1) (= sb-val_9_1 sb-val_8_1) (= sb-full_9_1 (ite flush_8_1 false sb-full_8_1)) (and (= stmt_9_1_0 stmt_8_1_0) (= stmt_9_1_1 stmt_8_1_1) (= stmt_9_1_2 stmt_8_1_2)) (= halt_9_1 halt_8_1))))

(assert (=> flush_8_1 (and (not sb-full_9_1) (= heap_9 (store heap_8 sb-adr_8_1 sb-val_8_1)) (not exit_9))))

; exited
(assert (=> exit_8 (and (= heap_9 heap_8) exit_9)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_9_0 flush_9_0 thread_9_1 flush_9_1 exit_9))
(assert (or (not thread_9_0) (not flush_9_0)))
(assert (or (not thread_9_0) (not thread_9_1)))
(assert (or (not thread_9_0) (not flush_9_1)))
(assert (or (not thread_9_0) (not exit_9)))
(assert (or (not flush_9_0) (not thread_9_1)))
(assert (or (not flush_9_0) (not flush_9_1)))
(assert (or (not flush_9_0) (not exit_9)))
(assert (or (not thread_9_1) (not flush_9_1)))
(assert (or (not thread_9_1) (not exit_9)))
(assert (or (not flush_9_1) (not exit_9)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_9_0 (=> stmt_9_0_1 (not thread_9_0)) (not flush_9_0)))
(assert (ite sb-full_9_1 (=> stmt_9_1_1 (not thread_9_1)) (not flush_9_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_9_0 (not thread_9_0)))
(assert (=> halt_9_1 (not thread_9_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 10
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_10_0 () (_ BitVec 16))
(declare-fun accu_10_1 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_10_0 () (_ BitVec 16))
(declare-fun mem_10_1 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_10_0 () (_ BitVec 16))
(declare-fun sb-adr_10_1 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_10_0 () (_ BitVec 16))
(declare-fun sb-val_10_1 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_10_0 () Bool)
(declare-fun sb-full_10_1 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_10_0_0 () Bool)
(declare-fun stmt_10_0_1 () Bool)
(declare-fun stmt_10_0_2 () Bool)

(declare-fun stmt_10_1_0 () Bool)
(declare-fun stmt_10_1_1 () Bool)
(declare-fun stmt_10_1_2 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_10_0 () Bool)
(declare-fun halt_10_1 () Bool)

; heap variable - heap_<step>
(declare-fun heap_10 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_10 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_10_0 () Bool)
(declare-fun thread_10_1 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_10_0_0 () Bool)
(declare-fun exec_10_0_1 () Bool)
(declare-fun exec_10_0_2 () Bool)

(declare-fun exec_10_1_0 () Bool)
(declare-fun exec_10_1_1 () Bool)
(declare-fun exec_10_1_2 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_10_0 () Bool)
(declare-fun flush_10_1 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_10_0_0 (and stmt_10_0_0 thread_10_0)))
(assert (= exec_10_0_1 (and stmt_10_0_1 thread_10_0)))
(assert (= exec_10_0_2 (and stmt_10_0_2 thread_10_0)))

(assert (= exec_10_1_0 (and stmt_10_1_0 thread_10_1)))
(assert (= exec_10_1_1 (and stmt_10_1_1 thread_10_1)))
(assert (= exec_10_1_2 (and stmt_10_1_2 thread_10_1)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread 0
(assert (=> exec_9_0_0 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (ite (not (= accu_9_0 #x0000)) (not stmt_10_0_1) stmt_10_0_1) (ite (not (= accu_9_0 #x0000)) stmt_10_0_2 (not stmt_10_0_2))) (= halt_10_0 halt_9_0) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_0_1 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (not stmt_10_0_1) (not stmt_10_0_2)) (and halt_10_0 (ite halt_10_1 (and exit_10 (= exit-code #x0000)) (not exit_10))) (= heap_10 heap_9))))

(assert (=> exec_9_0_2 (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 sb-full_9_0) (and (not stmt_10_0_0) (not stmt_10_0_1) stmt_10_0_2) (= halt_10_0 halt_9_0) (= heap_10 heap_9) exit_10 (= exit-code #x0001))))

(assert (=> (not thread_9_0) (and (= accu_10_0 accu_9_0) (= mem_10_0 mem_9_0) (= sb-adr_10_0 sb-adr_9_0) (= sb-val_10_0 sb-val_9_0) (= sb-full_10_0 (ite flush_9_0 false sb-full_9_0)) (and (= stmt_10_0_0 stmt_9_0_0) (= stmt_10_0_1 stmt_9_0_1) (= stmt_10_0_2 stmt_9_0_2)) (= halt_10_0 halt_9_0))))

(assert (=> flush_9_0 (and (not sb-full_10_0) (= heap_10 (store heap_9 sb-adr_9_0 sb-val_9_0)) (not exit_10))))

; thread 1
(assert (=> exec_9_1_0 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (ite (not (= accu_9_1 #x0000)) (not stmt_10_1_1) stmt_10_1_1) (ite (not (= accu_9_1 #x0000)) stmt_10_1_2 (not stmt_10_1_2))) (= halt_10_1 halt_9_1) (= heap_10 heap_9) (not exit_10))))

(assert (=> exec_9_1_1 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (not stmt_10_1_1) (not stmt_10_1_2)) (and halt_10_1 (ite halt_10_0 (and exit_10 (= exit-code #x0000)) (not exit_10))) (= heap_10 heap_9))))

(assert (=> exec_9_1_2 (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 sb-full_9_1) (and (not stmt_10_1_0) (not stmt_10_1_1) stmt_10_1_2) (= halt_10_1 halt_9_1) (= heap_10 heap_9) exit_10 (= exit-code #x0001))))

(assert (=> (not thread_9_1) (and (= accu_10_1 accu_9_1) (= mem_10_1 mem_9_1) (= sb-adr_10_1 sb-adr_9_1) (= sb-val_10_1 sb-val_9_1) (= sb-full_10_1 (ite flush_9_1 false sb-full_9_1)) (and (= stmt_10_1_0 stmt_9_1_0) (= stmt_10_1_1 stmt_9_1_1) (= stmt_10_1_2 stmt_9_1_2)) (= halt_10_1 halt_9_1))))

(assert (=> flush_9_1 (and (not sb-full_10_1) (= heap_10 (store heap_9 sb-adr_9_1 sb-val_9_1)) (not exit_10))))

; exited
(assert (=> exit_9 (and (= heap_10 heap_9) exit_10)))

(assert (=> (not exit_10) (= exit-code #x0000)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_10_0 flush_10_0 thread_10_1 flush_10_1 exit_10))
(assert (or (not thread_10_0) (not flush_10_0)))
(assert (or (not thread_10_0) (not thread_10_1)))
(assert (or (not thread_10_0) (not flush_10_1)))
(assert (or (not thread_10_0) (not exit_10)))
(assert (or (not flush_10_0) (not thread_10_1)))
(assert (or (not flush_10_0) (not flush_10_1)))
(assert (or (not flush_10_0) (not exit_10)))
(assert (or (not thread_10_1) (not flush_10_1)))
(assert (or (not thread_10_1) (not exit_10)))
(assert (or (not flush_10_1) (not exit_10)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_10_0 (=> stmt_10_0_1 (not thread_10_0)) (not flush_10_0)))
(assert (ite sb-full_10_1 (=> stmt_10_1_1 (not thread_10_1)) (not flush_10_1)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_10_0 (not thread_10_0)))
(assert (=> halt_10_1 (not thread_10_1)))

