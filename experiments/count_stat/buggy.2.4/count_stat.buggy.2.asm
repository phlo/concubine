# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Counter thread: increment global variable heap[0] 2 times.
#
# steps:
# * formula = loop * (2 - 1) + total
# * loop = 9
# * total = 11
#
# template parameter:
# * 12 = local counter address
#
# initial:
# * heap[0] = 0
# * heap[12] = 2
#
# input:
# * heap[12] = local counter variable
#
inc: LOAD 0 # load global
ADDI 1      # increment global
STORE 0     # store global
LOAD 12  # load local
SUBI 1      # decrement local
STORE 12 # store local (global flushed)
JNZ inc     # repeat if not finished
CHECK 0     # start checker thread
HALT
