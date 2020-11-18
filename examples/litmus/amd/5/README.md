# Sequential Consistency

> [P.234](https://www.amd.com/system/files/TechDocs/24593.pdf#page=234)

Where sequential consistency is needed (for example in Dekker’s algorithm for mutual exclusion), an `FENCE` instruction should be used between the store and the subsequent load, or an atomic instruction, such as `CAS`, should be used for the store.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| FENCE       | FENCE       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `accu_0 = accu_1 = 0` is not allowed

`LOAD 0` and `LOAD 1` cannot both read `0`.

## Bound = 12

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 62           |
| z3-4.8.6 (functional)            | 86           |
| btormc-3.1.0-pre                 | 95           |
| boolector-3.1.0-pre (relational) | 928          |
| z3-4.8.6 (relational)            | 1133         |
| cvc4-1.7 (functional)            | 1448         |
| cvc4-1.7 (relational)            | 85749        |

## Notes

[^1]: including final `HALT`
