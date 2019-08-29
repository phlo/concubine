# Intra-Processor Forwarding Is Allowed

> Example 8-5, [P.266](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=266)

The memory-ordering model allows concurrent stores by two processors to be seen in different orders by those two processors; specifically, each processor may perceive its own store occurring before that of the other.
This is illustrated by the following example:

## Example 8-5. Intra-Processor Forwarding is Allowed

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 0       | MEM 1       |
| MEM 1       | MEM 0       |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 0` is allowed

The memory-ordering model imposes no constraints on the order in which the two stores appear to execute by the two processors.
This fact allows processor 0 to see its store before seeing processor 1's, while processor 1 sees its store before seeing processor 0's.
(Each processor is self consistent.)
This allows `mem_0 = mem_1 = 0`.

In practice, the reordering in this example can arise as a result of store-buffer forwarding.
While a store is temporarily held in a processor's store buffer, it can satisfy the processor's own loads but is not visible to (and cannot satisfy) loads by other processors.

## Bound = 12

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
