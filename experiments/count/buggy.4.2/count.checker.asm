# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Summation (checker) thread: EXIT 1 if global counter is not incremented 2
# times by 4 threads (heap[0] != 2 * 4).
#
# steps:
# * total = 5
#
# template parameter:
# * 8 = expected global counter value
#
CHECK 0       # start checker thread
ADDI 8    # expected result
CMP 0         # compare to global
JNZ error     # check result
EXIT 0        # result == 4 * 2
error: EXIT 1 # error: result != 4 * 2
