# Loads Are Not Reordered with Older Stores to the Same Location

> Example 8-4, [P.266](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=266)

The Intel-64 memory-ordering model allows a load to be reordered with an earlier store to a different location.
However, loads are not reordered with stores to the same location.

The fact that a load may not be reordered with an earlier store to the same location is illustrated by the following
example:

## Example 8-4. Loads Are not Reordered with Older Stores to the Same Location

| Processor 0 |
| ----------- |
| ADDI 1      |
| STORE 0     |
| MEM 0       |

* initially `[0] = 0`
* `mem_0 = 0` is not allowed

The Intel-64 memory-ordering model does not allow the load to be reordered with the earlier store because the accesses are to the same location.
Therefore, `mem_0 = 1` must hold.

## Bound = 5

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
