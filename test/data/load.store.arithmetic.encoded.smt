; program: data/load.store.arithmetic.asm
; bound: 5

(set-logic QF_AUFBV)

; activation - STMT_<bound>_<pc>
(declare-fun STMT_1_0 () Bool)
(declare-fun STMT_1_1 () Bool)
(declare-fun STMT_1_2 () Bool)
(declare-fun STMT_1_3 () Bool)
(declare-fun STMT_1_4 () Bool)
(declare-fun STMT_2_0 () Bool)
(declare-fun STMT_2_1 () Bool)
(declare-fun STMT_2_2 () Bool)
(declare-fun STMT_2_3 () Bool)
(declare-fun STMT_2_4 () Bool)
(declare-fun STMT_3_0 () Bool)
(declare-fun STMT_3_1 () Bool)
(declare-fun STMT_3_2 () Bool)
(declare-fun STMT_3_3 () Bool)
(declare-fun STMT_3_4 () Bool)
(declare-fun STMT_4_0 () Bool)
(declare-fun STMT_4_1 () Bool)
(declare-fun STMT_4_2 () Bool)
(declare-fun STMT_4_3 () Bool)
(declare-fun STMT_4_4 () Bool)
(declare-fun STMT_5_0 () Bool)
(declare-fun STMT_5_1 () Bool)
(declare-fun STMT_5_2 () Bool)
(declare-fun STMT_5_3 () Bool)
(declare-fun STMT_5_4 () Bool)
(declare-fun STMT_FINAL () Bool)

; mem - MEM_<bound>
(declare-fun MEM_0 () (_ BitVec 16))
(declare-fun MEM_1 () (_ BitVec 16))
(declare-fun MEM_2 () (_ BitVec 16))
(declare-fun MEM_3 () (_ BitVec 16))
(declare-fun MEM_4 () (_ BitVec 16))
(declare-fun MEM_5 () (_ BitVec 16))
(declare-fun MEM_FINAL () (_ BitVec 16))

; accumulator - ACCU_<bound>
(declare-fun ACCU_0 () (_ BitVec 16))
(assert (= ACCU_0 #x0000))
(declare-fun ACCU_1 () (_ BitVec 16))
(declare-fun ACCU_2 () (_ BitVec 16))
(declare-fun ACCU_3 () (_ BitVec 16))
(declare-fun ACCU_4 () (_ BitVec 16))
(declare-fun ACCU_5 () (_ BitVec 16))
(declare-fun ACCU_FINAL () (_ BitVec 16))

; machine memory - HEAP_<bound>
(declare-fun HEAP_0 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_1 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_2 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_3 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_4 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_5 () (Array (_ BitVec 16) (_ BitVec 16)))
(declare-fun HEAP_FINAL () (Array (_ BitVec 16) (_ BitVec 16)))

; exit status
(declare-fun EXIT () Bool)
(declare-fun EXIT_CODE () (_ BitVec 16))

; initial activation
(assert STMT_1_0)

; step 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ADDI
(assert (=> STMT_1_0 (= MEM_1 MEM_0)))
(assert (=> STMT_1_0 (= ACCU_1 (bvadd ACCU_0 #x0001))))
(assert (=> STMT_1_0 (= HEAP_1 HEAP_0)))
(assert (=> STMT_1_0 STMT_2_1))

; STORE
(assert (=> STMT_1_1 (= MEM_1 MEM_0)))
(assert (=> STMT_1_1 (= ACCU_1 ACCU_0)))
(assert (=> STMT_1_1 (= HEAP_1 (store HEAP_0 #x0000 ACCU_1))))
(assert (=> STMT_1_1 STMT_2_2))

; ADD
(assert (=> STMT_1_2 (= MEM_1 MEM_0)))
(assert (=> STMT_1_2 (= ACCU_1 (bvadd ACCU_0 (select HEAP_1 #x0000)))))
(assert (=> STMT_1_2 (= HEAP_1 HEAP_0)))
(assert (=> STMT_1_2 STMT_2_3))

; SUB
(assert (=> STMT_1_3 (= MEM_1 MEM_0)))
(assert (=> STMT_1_3 (= ACCU_1 (bvsub ACCU_0 (select HEAP_1 #x0000)))))
(assert (=> STMT_1_3 (= HEAP_1 HEAP_0)))
(assert (=> STMT_1_3 STMT_2_4))

; SUBI
(assert (=> STMT_1_4 (= MEM_1 MEM_0)))
(assert (=> STMT_1_4 (= ACCU_1 (bvsub ACCU_0 #x0001))))
(assert (=> STMT_1_4 (= HEAP_1 HEAP_0)))

(assert (=> STMT_1_4 STMT_FINAL))
(assert (=> STMT_1_4 (= MEM_FINAL MEM_1)))
(assert (=> STMT_1_4 (= ACCU_FINAL ACCU_1)))
(assert (=> STMT_1_4 (= HEAP_FINAL HEAP_1)))

; step 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ADDI
(assert (=> STMT_2_0 (= MEM_2 MEM_0)))
(assert (=> STMT_2_0 (= ACCU_2 (bvadd ACCU_0 #x0001))))
(assert (=> STMT_2_0 (= HEAP_2 HEAP_0)))
(assert (=> STMT_2_0 STMT_3_1))

; STORE
(assert (=> STMT_2_1 (= MEM_2 MEM_1)))
(assert (=> STMT_2_1 (= ACCU_2 ACCU_1)))
(assert (=> STMT_2_1 (= HEAP_2 (store HEAP_1 #x0000 ACCU_2))))
(assert (=> STMT_2_1 STMT_3_2))

; ADD
(assert (=> STMT_2_2 (= MEM_2 MEM_1)))
(assert (=> STMT_2_2 (= ACCU_2 (bvadd ACCU_1 (select HEAP_2 #x0000)))))
(assert (=> STMT_2_2 (= HEAP_2 HEAP_1)))
(assert (=> STMT_2_2 STMT_3_3))

; SUB
(assert (=> STMT_2_3 (= MEM_2 MEM_1)))
(assert (=> STMT_2_3 (= ACCU_2 (bvsub ACCU_1 (select HEAP_2 #x0000)))))
(assert (=> STMT_2_3 (= HEAP_2 HEAP_1)))
(assert (=> STMT_2_3 STMT_3_4))

; SUBI
(assert (=> STMT_2_4 (= MEM_2 MEM_1)))
(assert (=> STMT_2_4 (= ACCU_2 (bvsub ACCU_1 #x0001))))
(assert (=> STMT_2_4 (= HEAP_2 HEAP_1)))

(assert (=> STMT_2_4 STMT_FINAL))
(assert (=> STMT_2_4 (= MEM_FINAL MEM_2)))
(assert (=> STMT_2_4 (= ACCU_FINAL ACCU_2)))
(assert (=> STMT_2_4 (= HEAP_FINAL HEAP_2)))

; step 3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ADDI
(assert (=> STMT_3_0 (= MEM_3 MEM_0)))
(assert (=> STMT_3_0 (= ACCU_3 (bvadd ACCU_0 #x0001))))
(assert (=> STMT_3_0 (= HEAP_3 HEAP_0)))
(assert (=> STMT_3_0 STMT_4_1))

; STORE
(assert (=> STMT_3_1 (= MEM_3 MEM_2)))
(assert (=> STMT_3_1 (= ACCU_3 ACCU_2)))
(assert (=> STMT_3_1 (= HEAP_3 (store HEAP_2 #x0000 ACCU_3))))
(assert (=> STMT_3_1 STMT_4_2))

; ADD
(assert (=> STMT_3_2 (= MEM_3 MEM_2)))
(assert (=> STMT_3_2 (= ACCU_3 (bvadd ACCU_2 (select HEAP_3 #x0000)))))
(assert (=> STMT_3_2 (= HEAP_3 HEAP_2)))
(assert (=> STMT_3_2 STMT_4_3))

; SUB
(assert (=> STMT_3_3 (= MEM_3 MEM_2)))
(assert (=> STMT_3_3 (= ACCU_3 (bvsub ACCU_2 (select HEAP_3 #x0000)))))
(assert (=> STMT_3_3 (= HEAP_3 HEAP_2)))
(assert (=> STMT_3_3 STMT_4_4))

; SUBI
(assert (=> STMT_3_4 (= MEM_3 MEM_2)))
(assert (=> STMT_3_4 (= ACCU_3 (bvsub ACCU_2 #x0001))))
(assert (=> STMT_3_4 (= HEAP_3 HEAP_2)))

(assert (=> STMT_3_4 STMT_FINAL))
(assert (=> STMT_3_4 (= MEM_FINAL MEM_3)))
(assert (=> STMT_3_4 (= ACCU_FINAL ACCU_3)))
(assert (=> STMT_3_4 (= HEAP_FINAL HEAP_3)))

; step 4 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ADDI
(assert (=> STMT_4_0 (= MEM_4 MEM_0)))
(assert (=> STMT_4_0 (= ACCU_4 (bvadd ACCU_0 #x0001))))
(assert (=> STMT_4_0 (= HEAP_4 HEAP_0)))
(assert (=> STMT_4_0 STMT_5_1))

; STORE
(assert (=> STMT_4_1 (= MEM_4 MEM_3)))
(assert (=> STMT_4_1 (= ACCU_4 ACCU_3)))
(assert (=> STMT_4_1 (= HEAP_4 (store HEAP_3 #x0000 ACCU_4))))
(assert (=> STMT_4_1 STMT_5_2))

; ADD
(assert (=> STMT_4_2 (= MEM_4 MEM_3)))
(assert (=> STMT_4_2 (= ACCU_4 (bvadd ACCU_3 (select HEAP_4 #x0000)))))
(assert (=> STMT_4_2 (= HEAP_4 HEAP_3)))
(assert (=> STMT_4_2 STMT_5_3))

; SUB
(assert (=> STMT_4_3 (= MEM_4 MEM_3)))
(assert (=> STMT_4_3 (= ACCU_4 (bvsub ACCU_3 (select HEAP_4 #x0000)))))
(assert (=> STMT_4_3 (= HEAP_4 HEAP_3)))
(assert (=> STMT_4_3 STMT_5_4))

; SUBI
(assert (=> STMT_4_4 (= MEM_4 MEM_3)))
(assert (=> STMT_4_4 (= ACCU_4 (bvsub ACCU_3 #x0001))))
(assert (=> STMT_4_4 (= HEAP_4 HEAP_3)))

(assert (=> STMT_4_4 STMT_FINAL))
(assert (=> STMT_4_4 (= MEM_FINAL MEM_4)))
(assert (=> STMT_4_4 (= ACCU_FINAL ACCU_4)))
(assert (=> STMT_4_4 (= HEAP_FINAL HEAP_4)))

; step 5 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ADDI
(assert (=> STMT_5_0 (= MEM_5 MEM_0)))
(assert (=> STMT_5_0 (= ACCU_5 (bvadd ACCU_0 #x0001))))
(assert (=> STMT_5_0 (= HEAP_5 HEAP_0)))

(assert (=> STMT_5_0 STMT_FINAL))
(assert (=> STMT_5_0 (= MEM_FINAL MEM_5)))
(assert (=> STMT_5_0 (= ACCU_FINAL ACCU_5)))
(assert (=> STMT_5_0 (= HEAP_FINAL HEAP_5)))

; STORE
(assert (=> STMT_5_1 (= MEM_5 MEM_4)))
(assert (=> STMT_5_1 (= ACCU_5 ACCU_4)))
(assert (=> STMT_5_1 (= HEAP_5 (store HEAP_4 #x0000 ACCU_5))))

(assert (=> STMT_5_1 STMT_FINAL))
(assert (=> STMT_5_1 (= MEM_FINAL MEM_5)))
(assert (=> STMT_5_1 (= ACCU_FINAL ACCU_5)))
(assert (=> STMT_5_1 (= HEAP_FINAL HEAP_5)))

; ADD
(assert (=> STMT_5_2 (= MEM_5 MEM_4)))
(assert (=> STMT_5_2 (= ACCU_5 (bvadd ACCU_4 (select HEAP_5 #x0000)))))
(assert (=> STMT_5_2 (= HEAP_5 HEAP_4)))

(assert (=> STMT_5_2 STMT_FINAL))
(assert (=> STMT_5_2 (= MEM_FINAL MEM_5)))
(assert (=> STMT_5_2 (= ACCU_FINAL ACCU_5)))
(assert (=> STMT_5_2 (= HEAP_FINAL HEAP_5)))

; SUB
(assert (=> STMT_5_3 (= MEM_5 MEM_4)))
(assert (=> STMT_5_3 (= ACCU_5 (bvsub ACCU_4 (select HEAP_5 #x0000)))))
(assert (=> STMT_5_3 (= HEAP_5 HEAP_4)))

(assert (=> STMT_5_3 STMT_FINAL))
(assert (=> STMT_5_3 (= MEM_FINAL MEM_5)))
(assert (=> STMT_5_3 (= ACCU_FINAL ACCU_5)))
(assert (=> STMT_5_3 (= HEAP_FINAL HEAP_5)))

; SUBI
(assert (=> STMT_5_4 (= MEM_5 MEM_4)))
(assert (=> STMT_5_4 (= ACCU_5 (bvsub ACCU_4 #x0001))))
(assert (=> STMT_5_4 (= HEAP_5 HEAP_4)))

(assert (=> STMT_5_4 STMT_FINAL))
(assert (=> STMT_5_4 (= MEM_FINAL MEM_5)))
(assert (=> STMT_5_4 (= ACCU_FINAL ACCU_5)))
(assert (=> STMT_5_4 (= HEAP_FINAL HEAP_5)))

