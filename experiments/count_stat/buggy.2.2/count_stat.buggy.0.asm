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
# * 10 = local counter address
#
# initial:
# * heap[0] = 0
# * heap[10] = 2
#
# input:
# * heap[10] = local counter variable
#
inc: LOAD 0 # load global
ADDI 1      # increment global
STORE 0     # store global
LOAD 10  # load local
SUBI 1      # decrement local
STORE 10 # store local (global flushed)
JNZ inc     # repeat if not finished
CHECK 0     # start checker thread
HALT
