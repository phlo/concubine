# Loads Are Not Reordered with Locked Instructions

> Example 8-9, [P.268](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=268)

The memory-ordering model prevents loads and stores from being reordered with locked instructions that execute earlier or later.
The examples in this section illustrate only cases in which a locked instruction is executed before a load or a store.
The reader should note that reordering is prevented also if the locked instruction is executed after a load or a store.

The first example illustrates that loads may not be reordered with earlier locked instructions:

## Example 8-9. Loads Are not Reordered with Locks

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| CAS 0       | CAS 0       |
| MEM 1       | MEM 0       |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 0` is not allowed

As explained in Section 8.2.3.8, there is a total order of the executions of locked instructions.
Without loss of generality, suppose that processor 0’s `CAS` occurs first.

Because the Intel-64 memory-ordering model prevents processor 1’s load from being reordered with its earlier `CAS`, processor 0’s `CAS` occurs before processor 1’s load.
This implies `mem_1 = 1`.

A similar argument (referring instead to processor 2’s accesses) applies if processor 1’s `CAS` occurs before processor 0’s `CAS`.

## Bound = 8

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 0       | 4     |
| 1         | 4                 | 0       | 4     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.