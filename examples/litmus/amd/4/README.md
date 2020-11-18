# Non-Overlapping Loads May Pass Stores[^1][^2]

> [P.234](https://www.amd.com/system/files/TechDocs/24593.pdf#page=234)

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `accu_0 = accu_1 = 0` is allowed

All combinations of values (`00`, `01`, `10`, and `11`) may be observed by Processors 0 and 1.

## Bound = 10

| Processor | Instructions[^3]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| btormc-3.1.0-pre                 | 17           |
| z3-4.8.6 (functional)            | 23           |
| boolector-3.1.0-pre (functional) | 32           |
| cvc4-1.7 (functional)            | 116          |
| cvc4-1.7 (relational)            | 206          |
| z3-4.8.6 (relational)            | 400          |
| boolector-3.1.0-pre (relational) | 1515         |

## Notes

[^1]: identical to [Intel 3](../../intel/3)
[^2]: shows same behaviour as [AMD 3](../3)
[^3]: including final `HALT`
