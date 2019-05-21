# concurrently incrementing heap[0] in a loop using CAS
STORE 0 # initialize heap[0] with 0
CHECK 0
LOOP: MEM 0
ADDI 1
CAS 0
JMP LOOP
