# Stores Are Transitively Visible

> Example 8-6, [P.276](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=276)

The memory-ordering model ensures transitive visibility of stores; stores that are causally related appear to all threads to occur in an order consistent with the causality relation.
This is illustrated by the following example:

## Example 8-6. Stores Are Transitively Visible

| Thread 0    | Thread 1    | Thread 2    |
| ----------- | ----------- | ----------- |
| ADDI 1      | MEM 0[^1]   |             |
| STORE 0     | JNZ 3       |             |
|             | ADDI 1      |             |
|             | STORE 1     | MEM 1       |
|             |             | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = mem_2 = 1` and `accu_2 = 0` is not allowed

Assume that `mem_1 = 1` and `mem_2 = 1`.

* Because `mem_1 = 1`, thread 0’s store occurs before thread 1’s load.
* Because the memory-ordering model prevents a store from being reordered with an earlier load (see Section 8.2.3.3), thread 1’s load occurs before its store. Thus, thread 0’s store causally precedes thread 1’s store.
* Because thread 0’s store causally precedes thread 1’s store, the memory-ordering model ensures that thread 0’s store appears to occur before thread 1’s store from the point of view of all threads.
* Because `mem_2 = 1`, thread 1’s store occurs before thread 2’s load.
* Because the Intel-64 memory-ordering model prevents loads from being reordered (see Section 8.2.3.2), thread 2’s load occur in order.
* The above items imply that thread 0’s store to `[0]` occurs before thread 2’s load from `[0]`. This implies that `accu_2 = 1`.

## Bound = 13

| Thread    | Instructions[^2]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 3                 | 1       | 4     |
| 1         | 5                 | 1       | 6     |
| 2         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| z3-4.8.6 (functional)            | 43           |
| btormc-3.1.0-pre                 | 49           |
| boolector-3.1.0-pre (functional) | 58           |
| cvc4-1.7 (functional)            | 314          |
| boolector-3.1.0-pre (relational) | 1057         |
| z3-4.8.6 (relational)            | 1976         |
| cvc4-1.7 (relational)            | 1988         |

## Notes

[^1]: using `MEM` instead of `LOAD` to ignore `ADDI`
[^2]: including final `HALT`
