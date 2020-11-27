# Paul McKenney's Statistical Counter (PerfBook 5.2)
#
# Summation (checker) thread: EXIT 1 if global counter is not incremented n
# times by m threads (heap[0] != n * m).
#
# steps:
# * total = 5
#
# template parameter:
# * <sum> = expected global counter value
#
CHECK 0       # start checker thread
ADDI <sum>    # expected result
CMP 0         # compare to global
JNZ error     # check result
EXIT 0        # result == m * n
error: EXIT 1 # error: result != m * n
