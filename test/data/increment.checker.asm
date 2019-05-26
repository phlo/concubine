# wait for checker barrier
CHECK 1

# load incremented global
LOAD 1

# compare to expected value
SUBI 2

# jump past error handling
JZ OK

# exit error
EXIT 1

# exit success
OK: EXIT 0
