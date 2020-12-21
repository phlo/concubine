# Paul McKenney's Statistical Counter (PerfBook 5.2) using CAS
#
# Counter thread: increment global variable heap[0] 3 times.
#
# steps: maximum CAS executions = 3 * m * (m + 1) / 2
#                               = 3 times triangular number for m threads
# * formula = cas * 3 * m * (m + 1) / 2 + 3 * (loop - cas) + total - loop
# * cas = 4
# * loop = 9
# * total = 11
#
# template parameter:
# * 10 = local counter address
#
# initial:
# * heap[0] = 0
# * heap[10] = 3
#
# input:
# * heap[10] = local counter variable
#
inc: MEM 0  # load global                   | cas | loop
ADDI 1      # increment global              |     |
CAS 0       # store global                  |     |
JZ inc      # retry if case failed         _|     |
LOAD 10  # load local                          |
SUBI 1      # decrement local                     |
STORE 10 # store local (global flushed)        |
JNZ inc     # repeat if not finished             _|
CHECK 0     # start checker thread
HALT
