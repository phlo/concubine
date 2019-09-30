# Local Visibility[^1]

> [P.220](https://www.amd.com/system/files/TechDocs/24593.pdf#page=220)

The local visibility (within a processor) for a memory operation may differ from the global visibility (from another processor).
Using a data bypass, a local load can read the result of a local store in a store buffer, before the store becomes globally visible.
Program order is still maintained when using such bypasses.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 0       | MEM 1       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` is allowed

`LOAD 0` in processor 0 can read `1` using the data bypass, while `LOAD 0` in processor 1 can read `0`.
Similarly, `LOAD 1` in processor 1 can read `1` while `LOAD 1` in processor 0 can read `0`.
Therefore, the result `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` may occur.
There are no constraints on the relative order of when the `STORE 0` of processor 0 is visible to processor 1 relative to when the `STORE 1` of processor 1 is visible to processor 0.

## Bound = 12

| Processor | Instructions[^2]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| z3-4.8.6 (functional)            | 52           |
| btormc-3.1.0-pre                 | 77           |
| boolector-3.1.0-pre (functional) | 95           |
| z3-4.8.6 (relational)            | 286          |
| boolector-3.1.0-pre (relational) | 1435         |
| cvc4-1.7 (relational)            | 2626         |
| cvc4-1.7 (functional)            | 75283        |

## Notes

[^1]: identical to [Intel 5](../../intel/5)
[^2]: including final `HALT`
