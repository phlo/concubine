# test for parsing and using indirect address mode
ADDI 1
STORE [1] # HEAP[0] = 1
LOAD 1    # ACCU = 0
ADD [1]   # ACCU = 1
CMP [1]   # true
