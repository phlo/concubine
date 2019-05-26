# thread 2/2: concurrently incrementing heap[0] in a loop using CHECK barriers
CHECK 0
CHECK 1
LOAD 0
ADDI 1
STORE 0
JNZ 0
EXIT 1
