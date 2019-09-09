# Stores Do Not Pass Loads

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

Successive stores from a single processor are committed to system memory and visible to other processors in program order.
A store by a processor cannot be committed to memory before a read appearing earlier in the program has captured its targeted data from memory.
In other words, stores from a processor cannot be reordered to occur prior to a load preceding it in program order.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| MEM 0       | MEM 1       |
| ADDI 1      | ADDI 1      |
| STORE 1     | STORE 0     |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 1` is not allowed

`LOAD 0` and `LOAD 1` cannot both read `1`.

## Bound = 10

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
* Identical to [Intel 2](../../intel/2)
