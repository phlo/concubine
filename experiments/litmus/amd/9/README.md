# Global Visibility

> [P.235](https://www.amd.com/system/files/TechDocs/24593.pdf#page=235)

If a very strong memory ordering model is required that does not allow local store-load bypasses, a `FENCE` instruction or an atomic instruction such as `CAS` should be used between the store and the subsequent load.
This enforces a memory ordering stronger than total store ordering.

| Thread 0    | Thread 1    |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| FENCE       | FENCE       |
| MEM 0       | MEM 1       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` is not allowed

In this example, the `FENCE` instruction ensures that any buffered stores are globally visible before the loads are allowed to execute, so the result `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` will not occur.

## Bound = 14

| Thread    | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 6                 | 1       | 7     |
| 1         | 6                 | 1       | 7     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 93           |
| z3-4.8.6 (functional)            | 156          |
| btormc-3.1.0-pre                 | 355          |
| z3-4.8.6 (relational)            | 623          |
| boolector-3.1.0-pre (relational) | 983          |
| cvc4-1.7 (functional)            | 1719         |
| cvc4-1.7 (relational)            | 1664730      |

## Notes

[^1]: including final `HALT`
