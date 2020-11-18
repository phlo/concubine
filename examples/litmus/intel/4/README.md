# Loads Are Not Reordered with Older Stores to the Same Location

> Example 8-4, [P.276](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=276)

The Intel-64 memory-ordering model allows a load to be reordered with an earlier store to a different location.
However, loads are not reordered with stores to the same location.

The fact that a load may not be reordered with an earlier store to the same location is illustrated by the following
example:

## Example 8-4. Loads Are not Reordered with Older Stores to the Same Location

| Processor 0 |
| ----------- |
| ADDI 1      |
| STORE 0     |
| LOAD 0      |

* initially `[0] = 0`
* `accu_0 = 0` is not allowed

The Intel-64 memory-ordering model does not allow the load to be reordered with the earlier store because the accesses are to the same location.
Therefore, `accu_0 = 1` must hold.

## Bound = 5

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 3            |
| boolector-3.1.0-pre (relational) | 4            |
| btormc-3.1.0-pre                 | 5            |
| z3-4.8.6 (functional)            | 10           |
| cvc4-1.7 (functional)            | 17           |
| cvc4-1.7 (relational)            | 19           |
| z3-4.8.6 (relational)            | 21           |

## Notes

[^1]: including final `HALT`
