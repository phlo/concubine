# Loads Do Not Pass Previous Loads, Stores Do Not Pass Previous Stores 

> [P.218](https://www.amd.com/system/files/TechDocs/24593.pdf#page=218)

Successive stores from a single processor are committed to system memory and visible to other processors in program order.
A store by a processor cannot be committed to memory before a read appearing earlier in the program has captured its targeted data from memory.
In other words, stores from a processor cannot be reordered to occur prior to a load preceding it in program order.

## Loads And Stores Are Not Reordered

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      |             |
| STORE 0     | MEM 1       |
| STORE 1     | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = 1` and `accu_1 = 0` is not allowed

Load `[0]` cannot read `0` when Load `[1]` reads `1`.

## Bound = 9

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 2       | 6     |
| 1         | 3                 | 0       | 3     |

[^1]: including final `HALT`
