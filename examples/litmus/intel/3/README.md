# Loads May Be Reordered with Earlier Stores to Different Locations

> Example 8-3, [P.265](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=265)

The Intel-64 memory-ordering model allows a load to be reordered with an earlier store to a different location.
However, loads are not reordered with stores to the same location.

The fact that a load may be reordered with an earlier store to a different location is illustrated by the following example:

## Example 8-3. Loads May be Reordered with Older Stores

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 1       | MEM 0       |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 0` is allowed

At each processor, the load and the store are to different locations and hence may be reordered.
Any interleaving of the operations is thus allowed.
One such interleaving has the two loads occurring before the two stores.
This would result in each load returning value 0.

## Bound = 10

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
