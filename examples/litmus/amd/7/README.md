# Dependent Stores Appear In Program Order[^1]

> [P.235](https://www.amd.com/system/files/TechDocs/24593.pdf#page=235)

Dependent stores between different processors appear to occur in program order, as shown in the code example below.

| Processor 0 | Processor 1 | Processor 2 |
| ----------- | ----------- | ----------- |
| ADDI 1      | MEM 0[^2]   |             |
| STORE 0     | JNZ 3       |             |
|             | ADDI 1      |             |
|             | STORE 1     | MEM 1       |
|             |             | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = mem_2 = 1` and `accu_2 = 0` is not allowed

If processor 1 reads a value from `[0]` (written by processor 0) before carrying out a store to `[1]`, and if processor 2 reads the updated value from `[1]`, a subsequent read of `[0]` must also be the updated value.

## Bound = 13

| Processor | Instructions[^3]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 3                 | 1       | 4     |
| 1         | 5                 | 1       | 6     |
| 2         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| z3-4.8.6 (functional)            | 43           |
| btormc-3.1.0-pre                 | 49           |
| boolector-3.1.0-pre (functional) | 59           |
| cvc4-1.7 (functional)            | 293          |
| boolector-3.1.0-pre (relational) | 1052         |
| cvc4-1.7 (relational)            | 1831         |
| z3-4.8.6 (relational)            | 1957         |

## Notes

[^1]: identical to [Intel 6](../../intel/6)
[^2]: using `MEM` instead of `LOAD` to ignore `ADDI`
[^3]: including final `HALT`
