# Stores Can Be Arbitrarily Delayed

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

Stores from a processor appear to be committed to the memory system in program order; however, stores can be delayed arbitrarily by store buffering while the processor continues operation.
Therefore, stores from a processor may not appear to be sequentially consistent.

## Stores Can Be Arbitrarily Delayed

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 1       | MEM 0       |

* `mem_0 = mem_1 = 1` is allowed

Both `LOAD 0` and `LOAD 1` may read `1`.

## Bound = 16

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 6                 | 2       | 8     |
| 1         | 6                 | 2       | 8     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.