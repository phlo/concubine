# Stores Are Seen In A Consistent Order By Other Processors[^1]

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

Stores to different locations in memory observed from two (or more) other processors will appear in the same order to all observers.
Behavior such as that is shown in this code example:

| Processor 0 | Processor 1 | Processor 2 | Processor 3 |
| ----------- | ----------- | ----------- | ----------- |
| ADDI 1      | ADDI 1      |             |             |
| STORE 0     | STORE 1     |             |             |
|             |             | MEM 0       | MEM 1       |
|             |             | LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_2 = 1`, `accu_2 = 0`, `mem_3 = 1` and `accu_3 = 0` is not allowed

Processor 2 seeing `STORE 0` from processor 0 before `STORE 1` from processor 1, while processor 3 sees `STORE 1` from processor 1 before `STORE 0` from processor 0, is not allowed.

## Bound = 14

| Processor | Instructions[^2]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 3                 | 1       | 4     |
| 1         | 3                 | 1       | 4     |
| 2         | 3                 | 0       | 3     |
| 3         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 134          |
| z3-4.8.6 (functional)            | 231          |
| btormc-3.1.0-pre                 | 793          |
| boolector-3.1.0-pre (relational) | 3638         |
| z3-4.8.6 (relational)            | 5955         |
| cvc4-1.7 (functional)            | 4852752      |
| cvc4-1.7 (relational)            | 32195323     |

## Notes

[^1]: identical to [Intel 7](../../intel/7)
[^2]: including final `HALT`
