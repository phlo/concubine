# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Counter thread: increment global variable heap[0] n times.
#
# steps:
# * formula = loop * (n - 1) + total
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
inc: LOAD 0 # load global
ADDI 1      # increment global
STORE 0     # store global
LOAD <adr>  # load local
SUBI 1      # decrement local
STORE <adr> # store local (global flushed)
JNZ inc     # repeat if not finished
CHECK 0     # start checker thread
HALT
