# Stores Are Seen in a Consistent Order by Other Processors

> Example 8-7, [P.267](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=267)

As noted in Section 8.2.3.5, the memory-ordering model allows stores by two processors to be seen in different orders by those two processors.
However, any two stores must appear to execute in the same order to all processors other than those performing the stores.
This is illustrated by the following example:

## Example 8-7. Stores Are Seen in a Consistent Order by Other Processors

| Processor 0 | Processor 1 | Processor 2 | Processor 3 |
| ----------- | ----------- | ----------- | ----------- |
| ADDI 1      | ADDI 1      |             |             |
| STORE 0     | STORE 1     |             |             |
|             |             | MEM 0       | MEM 1       |
|             |             | LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_2 = 1`, `accu_2 = 0`, `mem_3 = 1` and `accu_3 = 0` is not allowed

By the principles discussed in Section 8.2.3.2,

* processor 2’s first and second load cannot be reordered,
* processor 3’s first and second load cannot be reordered.
* If `mem_2 = 1` and `accu_2 = 0`, processor 0’s store appears to precede processor 1’s store with respect to processor 2.
* Similarly, `mem_3 = 1` and `accu_3 = 0` imply that processor 1’s store appears to precede processor 0’s store with respect to processor 1.

Because the memory-ordering model ensures that any two stores appear to execute in the same order to all processors (other than those performing the stores), this set of return values is not allowed.

## Bound = 14

| Processor | Instructions[^1]  | Flushes | Total |
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
| z3-4.8.6 (functional)            | 230          |
| btormc-3.1.0-pre                 | 790          |
| boolector-3.1.0-pre (relational) | 3651         |
| z3-4.8.6 (relational)            | 5982         |
| cvc4-1.7 (functional)            | 4914652      |
| cvc4-1.7 (relational)            | 32195323     |

## Notes

[^1]: including final `HALT`
