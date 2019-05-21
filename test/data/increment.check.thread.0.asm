# thread 1/2: concurrently incrementing heap[0] in a loop using SYNC barriers
STORE 0 # initialize heap[0] with 0
SYNC 0
LOAD 0
ADDI 1
STORE 0
SYNC 1
JNZ 1
EXIT 1
