# Non-Overlapping Loads May Pass Stores

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 1       | MEM 0       |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 0` is allowed

All combinations of values (`00`, `01`, `10`, and `11`) may be observed by Processors 0 and 1.

## Bound = 10

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 4                 | 1       | 5     |
| 1         | 4                 | 1       | 5     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
* Identical to [Intel 3](../../intel/3)
* Shows same behaviour as [AMD 3](../3)
