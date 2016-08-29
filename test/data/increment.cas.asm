# memorize old value for CAS
START: MEM 1

# increment
ADDI 1

# CAS
CAS 1

# did it succeed? if not, try again!
JZ START

# cas suceeded: start checker
SYNC 1
