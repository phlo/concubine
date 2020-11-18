# Stores Are Not Reordered with Locked Instructions

> Example 8-10, [P.278](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=278)

The memory-ordering model prevents loads and stores from being reordered with locked instructions that execute earlier or later.
The examples in this section illustrate only cases in which a locked instruction is executed before a load or a store.
The reader should note that reordering is prevented also if the locked instruction is executed after a load or a store.

The second example illustrates that a store may not be reordered with an earlier locked instruction:

## Example 8-10. Stores Are not Reordered with Locks

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      |             |
| CAS 0       | MEM 1       |
| STORE 1     | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = 1` and `accu_1 = 0` is not allowed

Assume `mem_1 = 1`.
* Because `mem_1 = 1`, processor 0’s store to `[1]` occurs before processor 1’s load from `[1]`.
* Because the memory-ordering model prevents a store from being reordered with an earlier locked instruction, processor 0’s `CAS` into `[0]` occurs before its store to `[1]`.
  Thus, processor 0’s `CAS` into `[0]` occurs before processor 1’s load from `[1]`.
* Because the memory-ordering model prevents loads from being reordered (see Section 8.2.3.2), processor 1’s loads occur in order and, therefore, processor 1’s `CAS` into `[0]` occurs before processor 1’s load from `[0]`.
  Thus, `accu_1 = 1`.

## Bound = 8

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| btormc-3.1.0-pre                 | 15           |
| z3-4.8.6 (functional)            | 16           |
| boolector-3.1.0-pre (functional) | 17           |
| cvc4-1.7 (functional)            | 62           |
| z3-4.8.6 (relational)            | 85           |
| boolector-3.1.0-pre (relational) | 87           |
| cvc4-1.7 (relational)            | 134          |

## Notes

[^1]: including final `HALT`
