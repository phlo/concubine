# Neither Loads Nor Stores Are Reordered with Like Operations

> Example 8-1, [P.265](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=265)

The Intel-64 memory-ordering model allows neither loads nor stores to be reordered with the same kind of operation.
That is, it ensures that loads are seen in program order and that stores are seen in program order.
This is illustrated by the following example:

## Example 8-1. Stores Are Not Reordered with Other Stores

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      |             |
| STORE 0     | MEM 1       |
| STORE 1     | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = 1` and `accu_1 = 0` is not allowed

The disallowed return values could be exhibited only if processor 0’s two stores are reordered (with the two loads occurring between them) or if processor 1’s two loads are reordered (with the two stores occurring between them).

If `mem_1 = 1`, the store to `[1]` occurs before the load from `[1]`.
Because the Intel-64 memory-ordering model does not allow stores to be reordered, the earlier store to `[0]` occurs before the load from `[1]`.
Because the Intel-64 memory-ordering model does not allow loads to be reordered, the store to `[0]` also occurs before the later load from `[0]`.
Thus `accu_1 = 1`.

## Bound = 9

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 2       | 6     |
| 1         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 6            |
| btormc-3.1.0-pre                 | 6            |
| z3-4.8.6 (functional)            | 11           |
| cvc4-1.7 (functional)            | 33           |
| boolector-3.1.0-pre (relational) | 43           |
| cvc4-1.7 (relational)            | 140          |
| z3-4.8.6 (relational)            | 270          |

## Notes

[^1]: including final `HALT`
