;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; litmus test constraints
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (and (= accu_1_1 #x0001) (= accu_2_1 #x0000)))
(assert (and (= accu_2_1 #x0001) (= accu_3_1 #x0000)))
(assert (and (= accu_3_1 #x0001) (= accu_4_1 #x0000)))
(assert (and (= accu_4_1 #x0001) (= accu_5_1 #x0000)))
(assert (and (= accu_5_1 #x0001) (= accu_6_1 #x0000)))
(assert (and (= accu_6_1 #x0001) (= accu_7_1 #x0000)))
(assert (and (= accu_7_1 #x0001) (= accu_8_1 #x0000)))
