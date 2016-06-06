# memorize old value for CAS
START: MEM 1
# increment
ADDI 1
# CAS
CAS 1
# did it succeed? yes: accu = 1, no: accu = 0. if not, try again!
JZ START
# cas suceeded: start checker
SYNC 1
