# Loads May Be Reordered with Earlier Stores to Different Locations

> Example 8-3, [P.275](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=275)

The Intel-64 memory-ordering model allows a load to be reordered with an earlier store to a different location.
However, loads are not reordered with stores to the same location.

The fact that a load may be reordered with an earlier store to a different location is illustrated by the following example:

## Example 8-3. Loads May be Reordered with Older Stores

| Thread 0    | Thread 1    |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `accu_0 = accu_1 = 0` is allowed

At each thread, the load and the store are to different locations and hence may be reordered.
Any interleaving of the operations is thus allowed.
One such interleaving has the two loads occurring before the two stores.
This would result in each load returning value 0.

## Bound = 10

| Thread    | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| btormc-3.1.0-pre                 | 20           |
| z3-4.8.6 (functional)            | 27           |
| boolector-3.1.0-pre (functional) | 47           |
| z3-4.8.6 (relational)            | 403          |
| cvc4-1.7 (functional)            | 755          |
| cvc4-1.7 (relational)            | 873          |
| boolector-3.1.0-pre (relational) | 1203         |

## Notes

[^1]: including final `HALT`
