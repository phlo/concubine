# thread 2/2: concurrently incrementing heap[0] in a loop using SYNC barriers
SYNC 0
SYNC 1
LOAD 0
ADDI 1
STORE 0
JNZ 0
EXIT 1
