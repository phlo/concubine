# wait for checker barrier
SYNC 1
# load incremented global
LOAD 1
# compare to expected value
SUBI 2
# jump past error handling
JZ 5
# set specific exit code?
#MOVI 1
# exit
EXIT 1
# continue execution
SYNC 2
