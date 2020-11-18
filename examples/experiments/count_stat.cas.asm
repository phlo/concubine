# Paul McKenney's Statistical Counter (PerfBook 5.2) using CAS
#
# Counter thread: increment global variable heap[0] n times.
#
# steps: maximum CAS executions = n * m * (m + 1) / 2
#                               = n times triangular number for m threads
# * formula = cas * n * m * (m + 1) / 2 + n * (loop - cas) + total - loop
# * cas = 4
# * loop = 9
# * total = 11
#
# template parameter:
# * <adr> = local counter address
#
# initial:
# * heap[0] = 0
# * heap[<adr>] = n
#
# input:
# * heap[<adr>] = local counter variable
#
inc: MEM 0  # load global                   | cas | loop
ADDI 1      # increment global              |     |
CAS 0       # store global                  |     |
JZ inc      # retry if case failed         _|     |
LOAD <adr>  # load local                          |
SUBI 1      # decrement local                     |
STORE <adr> # store local (global flushed)        |
JNZ inc     # repeat if not finished             _|
CHECK 0     # start checker thread
HALT
