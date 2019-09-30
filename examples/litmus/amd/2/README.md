# Stores Do Not Pass Loads[^1]

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

Successive stores from a single processor are committed to system memory and visible to other processors in program order.
A store by a processor cannot be committed to memory before a read appearing earlier in the program has captured its targeted data from memory.
In other words, stores from a processor cannot be reordered to occur prior to a load preceding it in program order.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| MEM 0[^2]   | MEM 1[^2]   |
| ADDI 1      | ADDI 1      |
| STORE 1     | STORE 0     |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 1` is not allowed

`LOAD 0` and `LOAD 1` cannot both read `1`.

## Bound = 10

| Processor | Instructions[^3]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| btormc-3.1.0-pre                 | 16           |
| z3-4.8.6 (functional)            | 17           |
| boolector-3.1.0-pre (functional) | 28           |
| boolector-3.1.0-pre (relational) | 58           |
| cvc4-1.7 (functional)            | 67           |
| z3-4.8.6 (relational)            | 132          |
| cvc4-1.7 (relational)            | 161          |

## Notes

[^1]: identical to [Intel 2](../../intel/2)
[^2]: using `MEM` instead of `LOAD` to ignore `ADDI`
[^3]: including final `HALT`
