# concurrently incrementing heap[0] in a loop using CAS
STORE 0 # initialize heap[0] with 0
SYNC 0
MEM 0
ADDI 1
CAS 0
JMP 2
