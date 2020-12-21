# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Summation (checker) thread: EXIT 1 if global counter is not incremented 2
# times by 2 threads (heap[0] != 2 * 2).
#
# steps:
# * total = 5
#
# template parameter:
# * 4 = expected global counter value
#
CHECK 0       # start checker thread
ADDI 4    # expected result
CMP 0         # compare to global
JNZ error     # check result
EXIT 0        # result == 2 * 2
error: EXIT 1 # error: result != 2 * 2
