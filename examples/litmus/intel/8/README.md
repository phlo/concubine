# Locked Instructions Have a Total Order

> Example 8-8, [P.277](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=277)

The memory-ordering model ensures that all processors agree on a single execution order of all locked instructions, including those that are larger than 8 bytes or are not naturally aligned.
This is illustrated by the following example:

## Example 8-8. Locked Instructions Have a Total Order

| Processor 0 | Processor 1 | Processor 2 | Processor 3 |
| ----------- | ----------- | ----------- | ----------- |
| ADDI 1      | ADDI 1      |             |             |
| CAS 0       | CAS 1       |             |             |
|             |             | MEM 0       | MEM 1       |
|             |             | LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_2 = 1`, `accu_2 = 0`, `mem_3 = 1` and `accu_3 = 0` is not allowed

Processor 2 and processor 3 must agree on the order of the two executions of `CAS`.
Without loss of generality, suppose that processor 0’s `CAS` occurs first.

* If `mem_3 = 1`, processor 1’s `CAS` into `[1]` occurs before processor 3’s load from `[1]`.
* Because the Intel-64 memory-ordering model prevents loads from being reordered (see Section 8.2.3.2), processor 3’s loads occur in order and, therefore, processor 1’s `CAS` occurs before processor 3’s load from `[0]`.
* Since processor 0’s `CAS` into `[0]` occurs before processor 1’s `CAS` (by assumption), it occurs before processor 3’s load from `[0]`.
  Thus, `accu_3 = 1`.

A similar argument (referring instead to processor 2’s loads) applies if processor 1’s `CAS` occurs before processor 0’s `CAS`.

## Bound = 12

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 3                 | 0       | 3     |
| 1         | 3                 | 0       | 3     |
| 2         | 3                 | 0       | 3     |
| 3         | 3                 | 0       | 3     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 69           |
| z3-4.8.6 (functional)            | 132          |
| btormc-3.1.0-pre                 | 471          |
| boolector-3.1.0-pre (relational) | 1952         |
| z3-4.8.6 (relational)            | 2149         |
| cvc4-1.7 (functional)            | 278935       |
| cvc4-1.7 (relational)            | 17410043     |

## Notes

[^1]: including final `HALT`
