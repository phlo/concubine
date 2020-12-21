# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Summation (checker) thread: EXIT 1 if global counter is not incremented 4
# times by 3 threads (heap[0] != 4 * 3).
#
# steps:
# * total = 5
#
# template parameter:
# * 12 = expected global counter value
#
CHECK 0       # start checker thread
ADDI 12    # expected result
CMP 0         # compare to global
JNZ error     # check result
EXIT 0        # result == 3 * 4
error: EXIT 1 # error: result != 3 * 4
