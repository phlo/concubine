# Loads Do Not Pass Previous Loads, Stores Do Not Pass Previous Stores[^1]

> [P.233](https://www.amd.com/system/files/TechDocs/24593.pdf#page=233)

Successive stores from a single processor are committed to system memory and visible to other processors in program order.
A store by a processor cannot be committed to memory before a read appearing earlier in the program has captured its targeted data from memory.
In other words, stores from a processor cannot be reordered to occur prior to a load preceding it in program order.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      |             |
| STORE 0     | MEM 1       |
| STORE 1     | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = 1` and `accu_1 = 0` is not allowed

`LOAD 0` cannot read `0` when `LOAD 1` reads `1`.

## Bound = 9

| Processor | Instructions[^2]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 2       | 6     |
| 1         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 6            |
| btormc-3.1.0-pre                 | 6            |
| z3-4.8.6 (functional)            | 10           |
| cvc4-1.7 (functional)            | 29           |
| boolector-3.1.0-pre (relational) | 43           |
| cvc4-1.7 (relational)            | 133          |
| z3-4.8.6 (relational)            | 269          |

## Notes

[^1]: identical to [Intel 1](../../intel/1)
[^2]: including final `HALT`
