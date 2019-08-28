# Stores Are Not Reordered With Earlier Loads

> Example 8-2, [P.265](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=265)

The Intel-64 memory-ordering model ensures that a store by a processor may not occur before a previous load by the same processor.
This is illustrated by the following example:

## Example 8-2. Stores Are Not Reordered with Older Loads

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| MEM 0       | MEM 1       |
| ADDI 1      | ADDI 1      |
| STORE 1     | STORE 0     |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 1` is not allowed

Assume `mem_0 = 1`.

* Because `mem_0 = 1`, processor 1’s store to `[0]` occurs before processor 0’s load from `[0]`.
* Because the Intel-64 memory-ordering model prevents each store from being reordered with the earlier load by the same processor, processor 1’s load from `[1]` occurs before its store to `[0]`.
* Similarly, processor 0’s load from `[0]` occurs before its store to `[1]`.
* Thus, processor 1’s load from `[1]` occurs before processor 0’s store to `[1]`, implying `mem_1 = 0`.

## Bound = 10

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
