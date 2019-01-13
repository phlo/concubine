# calculates the famous fibonacci numbers
# k = 1 => fib(0)
# k = 2 => fib(1)
STORE 1
ADDI 1
fib: STORE 2
ADD 1
STORE 1
ADD 2
JMP fib
