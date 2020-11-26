# Loads Are Not Reordered with Locked Instructions

> Example 8-9, [P.278](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=278)

The memory-ordering model prevents loads and stores from being reordered with locked instructions that execute earlier or later.
The examples in this section illustrate only cases in which a locked instruction is executed before a load or a store.
The reader should note that reordering is prevented also if the locked instruction is executed after a load or a store.

The first example illustrates that loads may not be reordered with earlier locked instructions:

## Example 8-9. Loads Are not Reordered with Locks

| Thread 0    | Thread 1    |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| CAS 0       | CAS 1       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `accu_0 = accu_1 = 0` is not allowed

As explained in Section 8.2.3.8, there is a total order of the executions of locked instructions.
Without loss of generality, suppose that thread 0’s `CAS` occurs first.

Because the Intel-64 memory-ordering model prevents thread 1’s load from being reordered with its earlier `CAS`, thread 0’s `CAS` occurs before thread 1’s load.
This implies `accu_1 = 1`.

A similar argument (referring instead to thread 2’s accesses) applies if thread 1’s `CAS` occurs before thread 0’s `CAS`.

## Bound = 8

| Thread    | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 0       | 4     |
| 1         | 4                 | 0       | 4     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 18           |
| btormc-3.1.0-pre                 | 24           |
| z3-4.8.6 (functional)            | 31           |
| z3-4.8.6 (relational)            | 130          |
| boolector-3.1.0-pre (relational) | 184          |
| cvc4-1.7 (functional)            | 414          |
| cvc4-1.7 (relational)            | 4023         |

## Notes

[^1]: including final `HALT`
