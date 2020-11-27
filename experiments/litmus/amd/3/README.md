# Stores Can Be Arbitrarily Delayed

> [P.234](https://www.amd.com/system/files/TechDocs/24593.pdf#page=234)

Stores from a thread appear to be committed to the memory system in program order; however, stores can be delayed arbitrarily by store buffering while the thread continues operation.
Therefore, stores from a thread may not appear to be sequentially consistent.

| Thread 0    | Thread 1    |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| LOAD 1      | LOAD 0      |

* `accu_0 = accu_1 = 1` is allowed

Both `LOAD 0` and `LOAD 1` may read `1`.

## Bound = 16

| Thread    | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 6                 | 2       | 8     |
| 1         | 6                 | 2       | 8     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| z3-4.8.6 (functional)            | 55           |
| btormc-3.1.0-pre                 | 95           |
| boolector-3.1.0-pre (functional) | 108          |
| cvc4-1.7 (functional)            | 2033         |
| boolector-3.1.0-pre (relational) | 2300         |
| z3-4.8.6 (relational)            | 2667         |
| cvc4-1.7 (relational)            | 2911         |

## Notes

[^1]: including final `HALT`
