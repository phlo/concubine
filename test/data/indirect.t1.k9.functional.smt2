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
(declare-fun stmt_0_0_4 () Bool)
(declare-fun stmt_0_0_5 () Bool)
(declare-fun stmt_0_0_6 () Bool)

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
(declare-fun exec_0_0_4 () Bool)
(declare-fun exec_0_0_5 () Bool)
(declare-fun exec_0_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_0_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))
(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))
(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))
(assert (= exec_0_0_3 (and stmt_0_0_3 thread_0_0)))
(assert (= exec_0_0_4 (and stmt_0_0_4 thread_0_0)))
(assert (= exec_0_0_5 (and stmt_0_0_5 thread_0_0)))
(assert (= exec_0_0_6 (and stmt_0_0_6 thread_0_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_0_0 flush_0_0 exit_0))
(assert (or (not thread_0_0) (not flush_0_0)))
(assert (or (not thread_0_0) (not exit_0)))
(assert (or (not flush_0_0) (not exit_0)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_0_0 (=> (or stmt_0_0_0 stmt_0_0_2 stmt_0_0_6) (not thread_0_0)) (not flush_0_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_0_0 (not thread_0_0)))

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
(assert (not stmt_0_0_4))
(assert (not stmt_0_0_5))
(assert (not stmt_0_0_6))

; halt variables - halt_<step>_<thread>
(assert (not halt_0_0))

; exit flag variable - exit_<step>
(assert (not exit_0))

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
(declare-fun stmt_1_0_4 () Bool)
(declare-fun stmt_1_0_5 () Bool)
(declare-fun stmt_1_0_6 () Bool)

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
(declare-fun exec_1_0_4 () Bool)
(declare-fun exec_1_0_5 () Bool)
(declare-fun exec_1_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_1_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))
(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))
(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))
(assert (= exec_1_0_3 (and stmt_1_0_3 thread_1_0)))
(assert (= exec_1_0_4 (and stmt_1_0_4 thread_1_0)))
(assert (= exec_1_0_5 (and stmt_1_0_5 thread_1_0)))
(assert (= exec_1_0_6 (and stmt_1_0_6 thread_1_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_1_0 flush_1_0 exit_1))
(assert (or (not thread_1_0) (not flush_1_0)))
(assert (or (not thread_1_0) (not exit_1)))
(assert (or (not flush_1_0) (not exit_1)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_1_0 (=> (or stmt_1_0_0 stmt_1_0_2 stmt_1_0_6) (not thread_1_0)) (not flush_1_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_1_0 (not thread_1_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_1_0 (ite exec_0_0_1 (bvadd accu_0_0 #x0001) (ite exec_0_0_3 (ite sb-full_0_0 (ite (= sb-adr_0_0 #x0000) (ite (= sb-val_0_0 #x0000) sb-val_0_0 (select heap_0 sb-val_0_0)) (ite (= sb-adr_0_0 (select heap_0 #x0000)) sb-val_0_0 (select heap_0 (select heap_0 #x0000)))) (select heap_0 (select heap_0 #x0000))) (ite exec_0_0_4 (bvadd accu_0_0 (ite sb-full_0_0 (ite (= sb-adr_0_0 #x0001) (ite (= sb-val_0_0 #x0001) sb-val_0_0 (select heap_0 sb-val_0_0)) (ite (= sb-adr_0_0 (select heap_0 #x0001)) sb-val_0_0 (select heap_0 (select heap_0 #x0001)))) (select heap_0 (select heap_0 #x0001)))) (ite exec_0_0_5 (bvsub accu_0_0 (ite sb-full_0_0 (ite (= sb-adr_0_0 #x0001) (ite (= sb-val_0_0 #x0001) sb-val_0_0 (select heap_0 sb-val_0_0)) (ite (= sb-adr_0_0 (select heap_0 #x0001)) sb-val_0_0 (select heap_0 (select heap_0 #x0001)))) (select heap_0 (select heap_0 #x0001)))) accu_0_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_1_0 mem_0_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_1_0 (ite exec_0_0_0 #x0001 (ite exec_0_0_2 (ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) sb-val_0_0 (select heap_0 #x0001)) sb-adr_0_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_1_0 (ite exec_0_0_0 accu_0_0 (ite exec_0_0_2 accu_0_0 sb-val_0_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_1_0 (ite flush_0_0 false (or exec_0_0_2 exec_0_0_0 sb-full_0_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))
(assert (= stmt_1_0_1 (ite stmt_0_0_0 exec_0_0_0 (and stmt_0_0_1 (not exec_0_0_1)))))
(assert (= stmt_1_0_2 (ite stmt_0_0_1 exec_0_0_1 (and stmt_0_0_2 (not exec_0_0_2)))))
(assert (= stmt_1_0_3 (ite stmt_0_0_2 exec_0_0_2 (and stmt_0_0_3 (not exec_0_0_3)))))
(assert (= stmt_1_0_4 (ite stmt_0_0_3 exec_0_0_3 (and stmt_0_0_4 (not exec_0_0_4)))))
(assert (= stmt_1_0_5 (ite stmt_0_0_4 exec_0_0_4 (and stmt_0_0_5 (not exec_0_0_5)))))
(assert (= stmt_1_0_6 (ite stmt_0_0_5 exec_0_0_5 (and stmt_0_0_6 (not exec_0_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_1_0 (or exec_0_0_6 halt_0_0)))

; heap variable - heap_<step>
(assert (= heap_1 (ite flush_0_0 (store heap_0 sb-adr_0_0 sb-val_0_0) heap_0)))

; exit flag variable - exit_<step>
(assert (= exit_1 (or exit_0 halt_1_0)))

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
(declare-fun stmt_2_0_4 () Bool)
(declare-fun stmt_2_0_5 () Bool)
(declare-fun stmt_2_0_6 () Bool)

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
(declare-fun exec_2_0_4 () Bool)
(declare-fun exec_2_0_5 () Bool)
(declare-fun exec_2_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_2_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_2_0_0 (and stmt_2_0_0 thread_2_0)))
(assert (= exec_2_0_1 (and stmt_2_0_1 thread_2_0)))
(assert (= exec_2_0_2 (and stmt_2_0_2 thread_2_0)))
(assert (= exec_2_0_3 (and stmt_2_0_3 thread_2_0)))
(assert (= exec_2_0_4 (and stmt_2_0_4 thread_2_0)))
(assert (= exec_2_0_5 (and stmt_2_0_5 thread_2_0)))
(assert (= exec_2_0_6 (and stmt_2_0_6 thread_2_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_2_0 flush_2_0 exit_2))
(assert (or (not thread_2_0) (not flush_2_0)))
(assert (or (not thread_2_0) (not exit_2)))
(assert (or (not flush_2_0) (not exit_2)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_2_0 (=> (or stmt_2_0_0 stmt_2_0_2 stmt_2_0_6) (not thread_2_0)) (not flush_2_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_2_0 (not thread_2_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_2_0 (ite exec_1_0_1 (bvadd accu_1_0 #x0001) (ite exec_1_0_3 (ite sb-full_1_0 (ite (= sb-adr_1_0 #x0000) (ite (= sb-val_1_0 #x0000) sb-val_1_0 (select heap_1 sb-val_1_0)) (ite (= sb-adr_1_0 (select heap_1 #x0000)) sb-val_1_0 (select heap_1 (select heap_1 #x0000)))) (select heap_1 (select heap_1 #x0000))) (ite exec_1_0_4 (bvadd accu_1_0 (ite sb-full_1_0 (ite (= sb-adr_1_0 #x0001) (ite (= sb-val_1_0 #x0001) sb-val_1_0 (select heap_1 sb-val_1_0)) (ite (= sb-adr_1_0 (select heap_1 #x0001)) sb-val_1_0 (select heap_1 (select heap_1 #x0001)))) (select heap_1 (select heap_1 #x0001)))) (ite exec_1_0_5 (bvsub accu_1_0 (ite sb-full_1_0 (ite (= sb-adr_1_0 #x0001) (ite (= sb-val_1_0 #x0001) sb-val_1_0 (select heap_1 sb-val_1_0)) (ite (= sb-adr_1_0 (select heap_1 #x0001)) sb-val_1_0 (select heap_1 (select heap_1 #x0001)))) (select heap_1 (select heap_1 #x0001)))) accu_1_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_2_0 mem_1_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_2_0 (ite exec_1_0_0 #x0001 (ite exec_1_0_2 (ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) sb-val_1_0 (select heap_1 #x0001)) sb-adr_1_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_2_0 (ite exec_1_0_0 accu_1_0 (ite exec_1_0_2 accu_1_0 sb-val_1_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_2_0 (ite flush_1_0 false (or exec_1_0_2 exec_1_0_0 sb-full_1_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))
(assert (= stmt_2_0_1 (ite stmt_1_0_0 exec_1_0_0 (and stmt_1_0_1 (not exec_1_0_1)))))
(assert (= stmt_2_0_2 (ite stmt_1_0_1 exec_1_0_1 (and stmt_1_0_2 (not exec_1_0_2)))))
(assert (= stmt_2_0_3 (ite stmt_1_0_2 exec_1_0_2 (and stmt_1_0_3 (not exec_1_0_3)))))
(assert (= stmt_2_0_4 (ite stmt_1_0_3 exec_1_0_3 (and stmt_1_0_4 (not exec_1_0_4)))))
(assert (= stmt_2_0_5 (ite stmt_1_0_4 exec_1_0_4 (and stmt_1_0_5 (not exec_1_0_5)))))
(assert (= stmt_2_0_6 (ite stmt_1_0_5 exec_1_0_5 (and stmt_1_0_6 (not exec_1_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_2_0 (or exec_1_0_6 halt_1_0)))

; heap variable - heap_<step>
(assert (= heap_2 (ite flush_1_0 (store heap_1 sb-adr_1_0 sb-val_1_0) heap_1)))

; exit flag variable - exit_<step>
(assert (= exit_2 (or exit_1 halt_2_0)))

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
(declare-fun stmt_3_0_4 () Bool)
(declare-fun stmt_3_0_5 () Bool)
(declare-fun stmt_3_0_6 () Bool)

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
(declare-fun exec_3_0_4 () Bool)
(declare-fun exec_3_0_5 () Bool)
(declare-fun exec_3_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_3_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_3_0_0 (and stmt_3_0_0 thread_3_0)))
(assert (= exec_3_0_1 (and stmt_3_0_1 thread_3_0)))
(assert (= exec_3_0_2 (and stmt_3_0_2 thread_3_0)))
(assert (= exec_3_0_3 (and stmt_3_0_3 thread_3_0)))
(assert (= exec_3_0_4 (and stmt_3_0_4 thread_3_0)))
(assert (= exec_3_0_5 (and stmt_3_0_5 thread_3_0)))
(assert (= exec_3_0_6 (and stmt_3_0_6 thread_3_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_3_0 flush_3_0 exit_3))
(assert (or (not thread_3_0) (not flush_3_0)))
(assert (or (not thread_3_0) (not exit_3)))
(assert (or (not flush_3_0) (not exit_3)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_3_0 (=> (or stmt_3_0_0 stmt_3_0_2 stmt_3_0_6) (not thread_3_0)) (not flush_3_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_3_0 (not thread_3_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_3_0 (ite exec_2_0_1 (bvadd accu_2_0 #x0001) (ite exec_2_0_3 (ite sb-full_2_0 (ite (= sb-adr_2_0 #x0000) (ite (= sb-val_2_0 #x0000) sb-val_2_0 (select heap_2 sb-val_2_0)) (ite (= sb-adr_2_0 (select heap_2 #x0000)) sb-val_2_0 (select heap_2 (select heap_2 #x0000)))) (select heap_2 (select heap_2 #x0000))) (ite exec_2_0_4 (bvadd accu_2_0 (ite sb-full_2_0 (ite (= sb-adr_2_0 #x0001) (ite (= sb-val_2_0 #x0001) sb-val_2_0 (select heap_2 sb-val_2_0)) (ite (= sb-adr_2_0 (select heap_2 #x0001)) sb-val_2_0 (select heap_2 (select heap_2 #x0001)))) (select heap_2 (select heap_2 #x0001)))) (ite exec_2_0_5 (bvsub accu_2_0 (ite sb-full_2_0 (ite (= sb-adr_2_0 #x0001) (ite (= sb-val_2_0 #x0001) sb-val_2_0 (select heap_2 sb-val_2_0)) (ite (= sb-adr_2_0 (select heap_2 #x0001)) sb-val_2_0 (select heap_2 (select heap_2 #x0001)))) (select heap_2 (select heap_2 #x0001)))) accu_2_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_3_0 mem_2_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_3_0 (ite exec_2_0_0 #x0001 (ite exec_2_0_2 (ite (and sb-full_2_0 (= sb-adr_2_0 #x0001)) sb-val_2_0 (select heap_2 #x0001)) sb-adr_2_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_3_0 (ite exec_2_0_0 accu_2_0 (ite exec_2_0_2 accu_2_0 sb-val_2_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_3_0 (ite flush_2_0 false (or exec_2_0_2 exec_2_0_0 sb-full_2_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_3_0_0 (and stmt_2_0_0 (not exec_2_0_0))))
(assert (= stmt_3_0_1 (ite stmt_2_0_0 exec_2_0_0 (and stmt_2_0_1 (not exec_2_0_1)))))
(assert (= stmt_3_0_2 (ite stmt_2_0_1 exec_2_0_1 (and stmt_2_0_2 (not exec_2_0_2)))))
(assert (= stmt_3_0_3 (ite stmt_2_0_2 exec_2_0_2 (and stmt_2_0_3 (not exec_2_0_3)))))
(assert (= stmt_3_0_4 (ite stmt_2_0_3 exec_2_0_3 (and stmt_2_0_4 (not exec_2_0_4)))))
(assert (= stmt_3_0_5 (ite stmt_2_0_4 exec_2_0_4 (and stmt_2_0_5 (not exec_2_0_5)))))
(assert (= stmt_3_0_6 (ite stmt_2_0_5 exec_2_0_5 (and stmt_2_0_6 (not exec_2_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_3_0 (or exec_2_0_6 halt_2_0)))

; heap variable - heap_<step>
(assert (= heap_3 (ite flush_2_0 (store heap_2 sb-adr_2_0 sb-val_2_0) heap_2)))

; exit flag variable - exit_<step>
(assert (= exit_3 (or exit_2 halt_3_0)))

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
(declare-fun stmt_4_0_4 () Bool)
(declare-fun stmt_4_0_5 () Bool)
(declare-fun stmt_4_0_6 () Bool)

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
(declare-fun exec_4_0_4 () Bool)
(declare-fun exec_4_0_5 () Bool)
(declare-fun exec_4_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_4_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_4_0_0 (and stmt_4_0_0 thread_4_0)))
(assert (= exec_4_0_1 (and stmt_4_0_1 thread_4_0)))
(assert (= exec_4_0_2 (and stmt_4_0_2 thread_4_0)))
(assert (= exec_4_0_3 (and stmt_4_0_3 thread_4_0)))
(assert (= exec_4_0_4 (and stmt_4_0_4 thread_4_0)))
(assert (= exec_4_0_5 (and stmt_4_0_5 thread_4_0)))
(assert (= exec_4_0_6 (and stmt_4_0_6 thread_4_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_4_0 flush_4_0 exit_4))
(assert (or (not thread_4_0) (not flush_4_0)))
(assert (or (not thread_4_0) (not exit_4)))
(assert (or (not flush_4_0) (not exit_4)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_4_0 (=> (or stmt_4_0_0 stmt_4_0_2 stmt_4_0_6) (not thread_4_0)) (not flush_4_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_4_0 (not thread_4_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_4_0 (ite exec_3_0_1 (bvadd accu_3_0 #x0001) (ite exec_3_0_3 (ite sb-full_3_0 (ite (= sb-adr_3_0 #x0000) (ite (= sb-val_3_0 #x0000) sb-val_3_0 (select heap_3 sb-val_3_0)) (ite (= sb-adr_3_0 (select heap_3 #x0000)) sb-val_3_0 (select heap_3 (select heap_3 #x0000)))) (select heap_3 (select heap_3 #x0000))) (ite exec_3_0_4 (bvadd accu_3_0 (ite sb-full_3_0 (ite (= sb-adr_3_0 #x0001) (ite (= sb-val_3_0 #x0001) sb-val_3_0 (select heap_3 sb-val_3_0)) (ite (= sb-adr_3_0 (select heap_3 #x0001)) sb-val_3_0 (select heap_3 (select heap_3 #x0001)))) (select heap_3 (select heap_3 #x0001)))) (ite exec_3_0_5 (bvsub accu_3_0 (ite sb-full_3_0 (ite (= sb-adr_3_0 #x0001) (ite (= sb-val_3_0 #x0001) sb-val_3_0 (select heap_3 sb-val_3_0)) (ite (= sb-adr_3_0 (select heap_3 #x0001)) sb-val_3_0 (select heap_3 (select heap_3 #x0001)))) (select heap_3 (select heap_3 #x0001)))) accu_3_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_4_0 mem_3_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_4_0 (ite exec_3_0_0 #x0001 (ite exec_3_0_2 (ite (and sb-full_3_0 (= sb-adr_3_0 #x0001)) sb-val_3_0 (select heap_3 #x0001)) sb-adr_3_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_4_0 (ite exec_3_0_0 accu_3_0 (ite exec_3_0_2 accu_3_0 sb-val_3_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_4_0 (ite flush_3_0 false (or exec_3_0_2 exec_3_0_0 sb-full_3_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_4_0_0 (and stmt_3_0_0 (not exec_3_0_0))))
(assert (= stmt_4_0_1 (ite stmt_3_0_0 exec_3_0_0 (and stmt_3_0_1 (not exec_3_0_1)))))
(assert (= stmt_4_0_2 (ite stmt_3_0_1 exec_3_0_1 (and stmt_3_0_2 (not exec_3_0_2)))))
(assert (= stmt_4_0_3 (ite stmt_3_0_2 exec_3_0_2 (and stmt_3_0_3 (not exec_3_0_3)))))
(assert (= stmt_4_0_4 (ite stmt_3_0_3 exec_3_0_3 (and stmt_3_0_4 (not exec_3_0_4)))))
(assert (= stmt_4_0_5 (ite stmt_3_0_4 exec_3_0_4 (and stmt_3_0_5 (not exec_3_0_5)))))
(assert (= stmt_4_0_6 (ite stmt_3_0_5 exec_3_0_5 (and stmt_3_0_6 (not exec_3_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_4_0 (or exec_3_0_6 halt_3_0)))

; heap variable - heap_<step>
(assert (= heap_4 (ite flush_3_0 (store heap_3 sb-adr_3_0 sb-val_3_0) heap_3)))

; exit flag variable - exit_<step>
(assert (= exit_4 (or exit_3 halt_4_0)))

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
(declare-fun stmt_5_0_4 () Bool)
(declare-fun stmt_5_0_5 () Bool)
(declare-fun stmt_5_0_6 () Bool)

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
(declare-fun exec_5_0_4 () Bool)
(declare-fun exec_5_0_5 () Bool)
(declare-fun exec_5_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_5_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_5_0_0 (and stmt_5_0_0 thread_5_0)))
(assert (= exec_5_0_1 (and stmt_5_0_1 thread_5_0)))
(assert (= exec_5_0_2 (and stmt_5_0_2 thread_5_0)))
(assert (= exec_5_0_3 (and stmt_5_0_3 thread_5_0)))
(assert (= exec_5_0_4 (and stmt_5_0_4 thread_5_0)))
(assert (= exec_5_0_5 (and stmt_5_0_5 thread_5_0)))
(assert (= exec_5_0_6 (and stmt_5_0_6 thread_5_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_5_0 flush_5_0 exit_5))
(assert (or (not thread_5_0) (not flush_5_0)))
(assert (or (not thread_5_0) (not exit_5)))
(assert (or (not flush_5_0) (not exit_5)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_5_0 (=> (or stmt_5_0_0 stmt_5_0_2 stmt_5_0_6) (not thread_5_0)) (not flush_5_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_5_0 (not thread_5_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_5_0 (ite exec_4_0_1 (bvadd accu_4_0 #x0001) (ite exec_4_0_3 (ite sb-full_4_0 (ite (= sb-adr_4_0 #x0000) (ite (= sb-val_4_0 #x0000) sb-val_4_0 (select heap_4 sb-val_4_0)) (ite (= sb-adr_4_0 (select heap_4 #x0000)) sb-val_4_0 (select heap_4 (select heap_4 #x0000)))) (select heap_4 (select heap_4 #x0000))) (ite exec_4_0_4 (bvadd accu_4_0 (ite sb-full_4_0 (ite (= sb-adr_4_0 #x0001) (ite (= sb-val_4_0 #x0001) sb-val_4_0 (select heap_4 sb-val_4_0)) (ite (= sb-adr_4_0 (select heap_4 #x0001)) sb-val_4_0 (select heap_4 (select heap_4 #x0001)))) (select heap_4 (select heap_4 #x0001)))) (ite exec_4_0_5 (bvsub accu_4_0 (ite sb-full_4_0 (ite (= sb-adr_4_0 #x0001) (ite (= sb-val_4_0 #x0001) sb-val_4_0 (select heap_4 sb-val_4_0)) (ite (= sb-adr_4_0 (select heap_4 #x0001)) sb-val_4_0 (select heap_4 (select heap_4 #x0001)))) (select heap_4 (select heap_4 #x0001)))) accu_4_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_5_0 mem_4_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_5_0 (ite exec_4_0_0 #x0001 (ite exec_4_0_2 (ite (and sb-full_4_0 (= sb-adr_4_0 #x0001)) sb-val_4_0 (select heap_4 #x0001)) sb-adr_4_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_5_0 (ite exec_4_0_0 accu_4_0 (ite exec_4_0_2 accu_4_0 sb-val_4_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_5_0 (ite flush_4_0 false (or exec_4_0_2 exec_4_0_0 sb-full_4_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_5_0_0 (and stmt_4_0_0 (not exec_4_0_0))))
(assert (= stmt_5_0_1 (ite stmt_4_0_0 exec_4_0_0 (and stmt_4_0_1 (not exec_4_0_1)))))
(assert (= stmt_5_0_2 (ite stmt_4_0_1 exec_4_0_1 (and stmt_4_0_2 (not exec_4_0_2)))))
(assert (= stmt_5_0_3 (ite stmt_4_0_2 exec_4_0_2 (and stmt_4_0_3 (not exec_4_0_3)))))
(assert (= stmt_5_0_4 (ite stmt_4_0_3 exec_4_0_3 (and stmt_4_0_4 (not exec_4_0_4)))))
(assert (= stmt_5_0_5 (ite stmt_4_0_4 exec_4_0_4 (and stmt_4_0_5 (not exec_4_0_5)))))
(assert (= stmt_5_0_6 (ite stmt_4_0_5 exec_4_0_5 (and stmt_4_0_6 (not exec_4_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_5_0 (or exec_4_0_6 halt_4_0)))

; heap variable - heap_<step>
(assert (= heap_5 (ite flush_4_0 (store heap_4 sb-adr_4_0 sb-val_4_0) heap_4)))

; exit flag variable - exit_<step>
(assert (= exit_5 (or exit_4 halt_5_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_6_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_6_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_6_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_6_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_6_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_6_0_0 () Bool)
(declare-fun stmt_6_0_1 () Bool)
(declare-fun stmt_6_0_2 () Bool)
(declare-fun stmt_6_0_3 () Bool)
(declare-fun stmt_6_0_4 () Bool)
(declare-fun stmt_6_0_5 () Bool)
(declare-fun stmt_6_0_6 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_6_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_6 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_6 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_6_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_6_0_0 () Bool)
(declare-fun exec_6_0_1 () Bool)
(declare-fun exec_6_0_2 () Bool)
(declare-fun exec_6_0_3 () Bool)
(declare-fun exec_6_0_4 () Bool)
(declare-fun exec_6_0_5 () Bool)
(declare-fun exec_6_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_6_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_6_0_0 (and stmt_6_0_0 thread_6_0)))
(assert (= exec_6_0_1 (and stmt_6_0_1 thread_6_0)))
(assert (= exec_6_0_2 (and stmt_6_0_2 thread_6_0)))
(assert (= exec_6_0_3 (and stmt_6_0_3 thread_6_0)))
(assert (= exec_6_0_4 (and stmt_6_0_4 thread_6_0)))
(assert (= exec_6_0_5 (and stmt_6_0_5 thread_6_0)))
(assert (= exec_6_0_6 (and stmt_6_0_6 thread_6_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_6_0 flush_6_0 exit_6))
(assert (or (not thread_6_0) (not flush_6_0)))
(assert (or (not thread_6_0) (not exit_6)))
(assert (or (not flush_6_0) (not exit_6)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_6_0 (=> (or stmt_6_0_0 stmt_6_0_2 stmt_6_0_6) (not thread_6_0)) (not flush_6_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_6_0 (not thread_6_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_6_0 (ite exec_5_0_1 (bvadd accu_5_0 #x0001) (ite exec_5_0_3 (ite sb-full_5_0 (ite (= sb-adr_5_0 #x0000) (ite (= sb-val_5_0 #x0000) sb-val_5_0 (select heap_5 sb-val_5_0)) (ite (= sb-adr_5_0 (select heap_5 #x0000)) sb-val_5_0 (select heap_5 (select heap_5 #x0000)))) (select heap_5 (select heap_5 #x0000))) (ite exec_5_0_4 (bvadd accu_5_0 (ite sb-full_5_0 (ite (= sb-adr_5_0 #x0001) (ite (= sb-val_5_0 #x0001) sb-val_5_0 (select heap_5 sb-val_5_0)) (ite (= sb-adr_5_0 (select heap_5 #x0001)) sb-val_5_0 (select heap_5 (select heap_5 #x0001)))) (select heap_5 (select heap_5 #x0001)))) (ite exec_5_0_5 (bvsub accu_5_0 (ite sb-full_5_0 (ite (= sb-adr_5_0 #x0001) (ite (= sb-val_5_0 #x0001) sb-val_5_0 (select heap_5 sb-val_5_0)) (ite (= sb-adr_5_0 (select heap_5 #x0001)) sb-val_5_0 (select heap_5 (select heap_5 #x0001)))) (select heap_5 (select heap_5 #x0001)))) accu_5_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_6_0 mem_5_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_6_0 (ite exec_5_0_0 #x0001 (ite exec_5_0_2 (ite (and sb-full_5_0 (= sb-adr_5_0 #x0001)) sb-val_5_0 (select heap_5 #x0001)) sb-adr_5_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_6_0 (ite exec_5_0_0 accu_5_0 (ite exec_5_0_2 accu_5_0 sb-val_5_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_6_0 (ite flush_5_0 false (or exec_5_0_2 exec_5_0_0 sb-full_5_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_6_0_0 (and stmt_5_0_0 (not exec_5_0_0))))
(assert (= stmt_6_0_1 (ite stmt_5_0_0 exec_5_0_0 (and stmt_5_0_1 (not exec_5_0_1)))))
(assert (= stmt_6_0_2 (ite stmt_5_0_1 exec_5_0_1 (and stmt_5_0_2 (not exec_5_0_2)))))
(assert (= stmt_6_0_3 (ite stmt_5_0_2 exec_5_0_2 (and stmt_5_0_3 (not exec_5_0_3)))))
(assert (= stmt_6_0_4 (ite stmt_5_0_3 exec_5_0_3 (and stmt_5_0_4 (not exec_5_0_4)))))
(assert (= stmt_6_0_5 (ite stmt_5_0_4 exec_5_0_4 (and stmt_5_0_5 (not exec_5_0_5)))))
(assert (= stmt_6_0_6 (ite stmt_5_0_5 exec_5_0_5 (and stmt_5_0_6 (not exec_5_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_6_0 (or exec_5_0_6 halt_5_0)))

; heap variable - heap_<step>
(assert (= heap_6 (ite flush_5_0 (store heap_5 sb-adr_5_0 sb-val_5_0) heap_5)))

; exit flag variable - exit_<step>
(assert (= exit_6 (or exit_5 halt_6_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_7_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_7_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_7_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_7_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_7_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_7_0_0 () Bool)
(declare-fun stmt_7_0_1 () Bool)
(declare-fun stmt_7_0_2 () Bool)
(declare-fun stmt_7_0_3 () Bool)
(declare-fun stmt_7_0_4 () Bool)
(declare-fun stmt_7_0_5 () Bool)
(declare-fun stmt_7_0_6 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_7_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_7 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_7 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_7_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_7_0_0 () Bool)
(declare-fun exec_7_0_1 () Bool)
(declare-fun exec_7_0_2 () Bool)
(declare-fun exec_7_0_3 () Bool)
(declare-fun exec_7_0_4 () Bool)
(declare-fun exec_7_0_5 () Bool)
(declare-fun exec_7_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_7_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_7_0_0 (and stmt_7_0_0 thread_7_0)))
(assert (= exec_7_0_1 (and stmt_7_0_1 thread_7_0)))
(assert (= exec_7_0_2 (and stmt_7_0_2 thread_7_0)))
(assert (= exec_7_0_3 (and stmt_7_0_3 thread_7_0)))
(assert (= exec_7_0_4 (and stmt_7_0_4 thread_7_0)))
(assert (= exec_7_0_5 (and stmt_7_0_5 thread_7_0)))
(assert (= exec_7_0_6 (and stmt_7_0_6 thread_7_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_7_0 flush_7_0 exit_7))
(assert (or (not thread_7_0) (not flush_7_0)))
(assert (or (not thread_7_0) (not exit_7)))
(assert (or (not flush_7_0) (not exit_7)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_7_0 (=> (or stmt_7_0_0 stmt_7_0_2 stmt_7_0_6) (not thread_7_0)) (not flush_7_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_7_0 (not thread_7_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_7_0 (ite exec_6_0_1 (bvadd accu_6_0 #x0001) (ite exec_6_0_3 (ite sb-full_6_0 (ite (= sb-adr_6_0 #x0000) (ite (= sb-val_6_0 #x0000) sb-val_6_0 (select heap_6 sb-val_6_0)) (ite (= sb-adr_6_0 (select heap_6 #x0000)) sb-val_6_0 (select heap_6 (select heap_6 #x0000)))) (select heap_6 (select heap_6 #x0000))) (ite exec_6_0_4 (bvadd accu_6_0 (ite sb-full_6_0 (ite (= sb-adr_6_0 #x0001) (ite (= sb-val_6_0 #x0001) sb-val_6_0 (select heap_6 sb-val_6_0)) (ite (= sb-adr_6_0 (select heap_6 #x0001)) sb-val_6_0 (select heap_6 (select heap_6 #x0001)))) (select heap_6 (select heap_6 #x0001)))) (ite exec_6_0_5 (bvsub accu_6_0 (ite sb-full_6_0 (ite (= sb-adr_6_0 #x0001) (ite (= sb-val_6_0 #x0001) sb-val_6_0 (select heap_6 sb-val_6_0)) (ite (= sb-adr_6_0 (select heap_6 #x0001)) sb-val_6_0 (select heap_6 (select heap_6 #x0001)))) (select heap_6 (select heap_6 #x0001)))) accu_6_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_7_0 mem_6_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_7_0 (ite exec_6_0_0 #x0001 (ite exec_6_0_2 (ite (and sb-full_6_0 (= sb-adr_6_0 #x0001)) sb-val_6_0 (select heap_6 #x0001)) sb-adr_6_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_7_0 (ite exec_6_0_0 accu_6_0 (ite exec_6_0_2 accu_6_0 sb-val_6_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_7_0 (ite flush_6_0 false (or exec_6_0_2 exec_6_0_0 sb-full_6_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_7_0_0 (and stmt_6_0_0 (not exec_6_0_0))))
(assert (= stmt_7_0_1 (ite stmt_6_0_0 exec_6_0_0 (and stmt_6_0_1 (not exec_6_0_1)))))
(assert (= stmt_7_0_2 (ite stmt_6_0_1 exec_6_0_1 (and stmt_6_0_2 (not exec_6_0_2)))))
(assert (= stmt_7_0_3 (ite stmt_6_0_2 exec_6_0_2 (and stmt_6_0_3 (not exec_6_0_3)))))
(assert (= stmt_7_0_4 (ite stmt_6_0_3 exec_6_0_3 (and stmt_6_0_4 (not exec_6_0_4)))))
(assert (= stmt_7_0_5 (ite stmt_6_0_4 exec_6_0_4 (and stmt_6_0_5 (not exec_6_0_5)))))
(assert (= stmt_7_0_6 (ite stmt_6_0_5 exec_6_0_5 (and stmt_6_0_6 (not exec_6_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_7_0 (or exec_6_0_6 halt_6_0)))

; heap variable - heap_<step>
(assert (= heap_7 (ite flush_6_0 (store heap_6 sb-adr_6_0 sb-val_6_0) heap_6)))

; exit flag variable - exit_<step>
(assert (= exit_7 (or exit_6 halt_7_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_8_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_8_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_8_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_8_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_8_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_8_0_0 () Bool)
(declare-fun stmt_8_0_1 () Bool)
(declare-fun stmt_8_0_2 () Bool)
(declare-fun stmt_8_0_3 () Bool)
(declare-fun stmt_8_0_4 () Bool)
(declare-fun stmt_8_0_5 () Bool)
(declare-fun stmt_8_0_6 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_8_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_8 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_8 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_8_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_8_0_0 () Bool)
(declare-fun exec_8_0_1 () Bool)
(declare-fun exec_8_0_2 () Bool)
(declare-fun exec_8_0_3 () Bool)
(declare-fun exec_8_0_4 () Bool)
(declare-fun exec_8_0_5 () Bool)
(declare-fun exec_8_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_8_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_8_0_0 (and stmt_8_0_0 thread_8_0)))
(assert (= exec_8_0_1 (and stmt_8_0_1 thread_8_0)))
(assert (= exec_8_0_2 (and stmt_8_0_2 thread_8_0)))
(assert (= exec_8_0_3 (and stmt_8_0_3 thread_8_0)))
(assert (= exec_8_0_4 (and stmt_8_0_4 thread_8_0)))
(assert (= exec_8_0_5 (and stmt_8_0_5 thread_8_0)))
(assert (= exec_8_0_6 (and stmt_8_0_6 thread_8_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_8_0 flush_8_0 exit_8))
(assert (or (not thread_8_0) (not flush_8_0)))
(assert (or (not thread_8_0) (not exit_8)))
(assert (or (not flush_8_0) (not exit_8)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_8_0 (=> (or stmt_8_0_0 stmt_8_0_2 stmt_8_0_6) (not thread_8_0)) (not flush_8_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_8_0 (not thread_8_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_8_0 (ite exec_7_0_1 (bvadd accu_7_0 #x0001) (ite exec_7_0_3 (ite sb-full_7_0 (ite (= sb-adr_7_0 #x0000) (ite (= sb-val_7_0 #x0000) sb-val_7_0 (select heap_7 sb-val_7_0)) (ite (= sb-adr_7_0 (select heap_7 #x0000)) sb-val_7_0 (select heap_7 (select heap_7 #x0000)))) (select heap_7 (select heap_7 #x0000))) (ite exec_7_0_4 (bvadd accu_7_0 (ite sb-full_7_0 (ite (= sb-adr_7_0 #x0001) (ite (= sb-val_7_0 #x0001) sb-val_7_0 (select heap_7 sb-val_7_0)) (ite (= sb-adr_7_0 (select heap_7 #x0001)) sb-val_7_0 (select heap_7 (select heap_7 #x0001)))) (select heap_7 (select heap_7 #x0001)))) (ite exec_7_0_5 (bvsub accu_7_0 (ite sb-full_7_0 (ite (= sb-adr_7_0 #x0001) (ite (= sb-val_7_0 #x0001) sb-val_7_0 (select heap_7 sb-val_7_0)) (ite (= sb-adr_7_0 (select heap_7 #x0001)) sb-val_7_0 (select heap_7 (select heap_7 #x0001)))) (select heap_7 (select heap_7 #x0001)))) accu_7_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_8_0 mem_7_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_8_0 (ite exec_7_0_0 #x0001 (ite exec_7_0_2 (ite (and sb-full_7_0 (= sb-adr_7_0 #x0001)) sb-val_7_0 (select heap_7 #x0001)) sb-adr_7_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_8_0 (ite exec_7_0_0 accu_7_0 (ite exec_7_0_2 accu_7_0 sb-val_7_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_8_0 (ite flush_7_0 false (or exec_7_0_2 exec_7_0_0 sb-full_7_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_8_0_0 (and stmt_7_0_0 (not exec_7_0_0))))
(assert (= stmt_8_0_1 (ite stmt_7_0_0 exec_7_0_0 (and stmt_7_0_1 (not exec_7_0_1)))))
(assert (= stmt_8_0_2 (ite stmt_7_0_1 exec_7_0_1 (and stmt_7_0_2 (not exec_7_0_2)))))
(assert (= stmt_8_0_3 (ite stmt_7_0_2 exec_7_0_2 (and stmt_7_0_3 (not exec_7_0_3)))))
(assert (= stmt_8_0_4 (ite stmt_7_0_3 exec_7_0_3 (and stmt_7_0_4 (not exec_7_0_4)))))
(assert (= stmt_8_0_5 (ite stmt_7_0_4 exec_7_0_4 (and stmt_7_0_5 (not exec_7_0_5)))))
(assert (= stmt_8_0_6 (ite stmt_7_0_5 exec_7_0_5 (and stmt_7_0_6 (not exec_7_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_8_0 (or exec_7_0_6 halt_7_0)))

; heap variable - heap_<step>
(assert (= heap_8 (ite flush_7_0 (store heap_7 sb-adr_7_0 sb-val_7_0) heap_7)))

; exit flag variable - exit_<step>
(assert (= exit_8 (or exit_7 halt_8_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; step 9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(declare-fun accu_9_0 () (_ BitVec 16))

; mem variables - mem_<step>_<thread>
(declare-fun mem_9_0 () (_ BitVec 16))

; store buffer address variables - sb-adr_<step>_<thread>
(declare-fun sb-adr_9_0 () (_ BitVec 16))

; store buffer value variables - sb-val_<step>_<thread>
(declare-fun sb-val_9_0 () (_ BitVec 16))

; store buffer full variables - sb-full_<step>_<thread>
(declare-fun sb-full_9_0 () Bool)

; statement activation variables - stmt_<step>_<thread>_<pc>
(declare-fun stmt_9_0_0 () Bool)
(declare-fun stmt_9_0_1 () Bool)
(declare-fun stmt_9_0_2 () Bool)
(declare-fun stmt_9_0_3 () Bool)
(declare-fun stmt_9_0_4 () Bool)
(declare-fun stmt_9_0_5 () Bool)
(declare-fun stmt_9_0_6 () Bool)

; halt variables - halt_<step>_<thread>
(declare-fun halt_9_0 () Bool)

; heap variable - heap_<step>
(declare-fun heap_9 () (Array (_ BitVec 16) (_ BitVec 16)))

; exit flag variable - exit_<step>
(declare-fun exit_9 () Bool)

; transition variable declarations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thread activation variables - thread_<step>_<thread>
(declare-fun thread_9_0 () Bool)

; statement execution variables - exec_<step>_<thread>_<pc>
(declare-fun exec_9_0_0 () Bool)
(declare-fun exec_9_0_1 () Bool)
(declare-fun exec_9_0_2 () Bool)
(declare-fun exec_9_0_3 () Bool)
(declare-fun exec_9_0_4 () Bool)
(declare-fun exec_9_0_5 () Bool)
(declare-fun exec_9_0_6 () Bool)

; store buffer flush variables - flush_<step>_<thread>
(declare-fun flush_9_0 () Bool)

; transition variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; statement execution variables - exec_<step>_<thread>_<pc>
(assert (= exec_9_0_0 (and stmt_9_0_0 thread_9_0)))
(assert (= exec_9_0_1 (and stmt_9_0_1 thread_9_0)))
(assert (= exec_9_0_2 (and stmt_9_0_2 thread_9_0)))
(assert (= exec_9_0_3 (and stmt_9_0_3 thread_9_0)))
(assert (= exec_9_0_4 (and stmt_9_0_4 thread_9_0)))
(assert (= exec_9_0_5 (and stmt_9_0_5 thread_9_0)))
(assert (= exec_9_0_6 (and stmt_9_0_6 thread_9_0)))

; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (or thread_9_0 flush_9_0 exit_9))
(assert (or (not thread_9_0) (not flush_9_0)))
(assert (or (not thread_9_0) (not exit_9)))
(assert (or (not flush_9_0) (not exit_9)))

; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (ite sb-full_9_0 (=> (or stmt_9_0_0 stmt_9_0_2 stmt_9_0_6) (not thread_9_0)) (not flush_9_0)))

; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (=> halt_9_0 (not thread_9_0)))

; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accu variables - accu_<step>_<thread>
(assert (= accu_9_0 (ite exec_8_0_1 (bvadd accu_8_0 #x0001) (ite exec_8_0_3 (ite sb-full_8_0 (ite (= sb-adr_8_0 #x0000) (ite (= sb-val_8_0 #x0000) sb-val_8_0 (select heap_8 sb-val_8_0)) (ite (= sb-adr_8_0 (select heap_8 #x0000)) sb-val_8_0 (select heap_8 (select heap_8 #x0000)))) (select heap_8 (select heap_8 #x0000))) (ite exec_8_0_4 (bvadd accu_8_0 (ite sb-full_8_0 (ite (= sb-adr_8_0 #x0001) (ite (= sb-val_8_0 #x0001) sb-val_8_0 (select heap_8 sb-val_8_0)) (ite (= sb-adr_8_0 (select heap_8 #x0001)) sb-val_8_0 (select heap_8 (select heap_8 #x0001)))) (select heap_8 (select heap_8 #x0001)))) (ite exec_8_0_5 (bvsub accu_8_0 (ite sb-full_8_0 (ite (= sb-adr_8_0 #x0001) (ite (= sb-val_8_0 #x0001) sb-val_8_0 (select heap_8 sb-val_8_0)) (ite (= sb-adr_8_0 (select heap_8 #x0001)) sb-val_8_0 (select heap_8 (select heap_8 #x0001)))) (select heap_8 (select heap_8 #x0001)))) accu_8_0))))))

; mem variables - mem_<step>_<thread>
(assert (= mem_9_0 mem_8_0))

; store buffer address variables - sb-adr_<step>_<thread>
(assert (= sb-adr_9_0 (ite exec_8_0_0 #x0001 (ite exec_8_0_2 (ite (and sb-full_8_0 (= sb-adr_8_0 #x0001)) sb-val_8_0 (select heap_8 #x0001)) sb-adr_8_0))))

; store buffer value variables - sb-val_<step>_<thread>
(assert (= sb-val_9_0 (ite exec_8_0_0 accu_8_0 (ite exec_8_0_2 accu_8_0 sb-val_8_0))))

; store buffer full variables - sb-full_<step>_<thread>
(assert (= sb-full_9_0 (ite flush_8_0 false (or exec_8_0_2 exec_8_0_0 sb-full_8_0))))

; statement activation variables - stmt_<step>_<thread>_<pc>
(assert (= stmt_9_0_0 (and stmt_8_0_0 (not exec_8_0_0))))
(assert (= stmt_9_0_1 (ite stmt_8_0_0 exec_8_0_0 (and stmt_8_0_1 (not exec_8_0_1)))))
(assert (= stmt_9_0_2 (ite stmt_8_0_1 exec_8_0_1 (and stmt_8_0_2 (not exec_8_0_2)))))
(assert (= stmt_9_0_3 (ite stmt_8_0_2 exec_8_0_2 (and stmt_8_0_3 (not exec_8_0_3)))))
(assert (= stmt_9_0_4 (ite stmt_8_0_3 exec_8_0_3 (and stmt_8_0_4 (not exec_8_0_4)))))
(assert (= stmt_9_0_5 (ite stmt_8_0_4 exec_8_0_4 (and stmt_8_0_5 (not exec_8_0_5)))))
(assert (= stmt_9_0_6 (ite stmt_8_0_5 exec_8_0_5 (and stmt_8_0_6 (not exec_8_0_6)))))

; halt variables - halt_<step>_<thread>
(assert (= halt_9_0 (or exec_8_0_6 halt_8_0)))

; heap variable - heap_<step>
(assert (= heap_9 (ite flush_8_0 (store heap_8 sb-adr_8_0 sb-val_8_0) heap_8)))

; exit flag variable - exit_<step>
(assert (= exit_9 (or exit_8 halt_9_0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; exit code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (= exit-code #x0000))

