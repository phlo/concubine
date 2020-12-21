# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Summation (checker) thread: EXIT 1 if global counter is not incremented 3
# times by 3 threads (heap[0] != 3 * 3).
#
# steps:
# * total = 5
#
# template parameter:
# * 9 = expected global counter value
#
CHECK 0       # start checker thread
ADDI 9    # expected result
CMP 0         # compare to global
JNZ error     # check result
EXIT 0        # result == 3 * 3
error: EXIT 1 # error: result != 3 * 3
