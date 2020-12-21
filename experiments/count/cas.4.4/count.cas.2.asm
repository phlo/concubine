# Paul McKenney's Statistical Counter (PerfBook 5.2) using CAS
#
# Counter thread: increment global variable heap[0] 4 times.
#
# steps: maximum CAS executions = 4 * m * (m + 1) / 2
#                               = 4 times triangular number for m threads
# * formula = cas * 4 * m * (m + 1) / 2 + 4 * (loop - cas) + total - loop
# * cas = 4
# * loop = 9
# * total = 11
#
# template parameter:
# * 12 = local counter address
#
# initial:
# * heap[0] = 0
# * heap[12] = 4
#
# input:
# * heap[12] = local counter variable
#
inc: MEM 0  # load global                   | cas | loop
ADDI 1      # increment global              |     |
CAS 0       # store global                  |     |
JZ inc      # retry if case failed         _|     |
LOAD 12  # load local                          |
SUBI 1      # decrement local                     |
STORE 12 # store local (global flushed)        |
JNZ inc     # repeat if not finished             _|
CHECK 0     # start checker thread
HALT
