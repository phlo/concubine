# Sequential Consistency

> [P.219](https://www.amd.com/system/files/TechDocs/24593.pdf#page=219)

Where sequential consistency is needed (for example in Dekker’s algorithm for mutual exclusion), an `FENCE` instruction should be used between the store and the subsequent load, or an atomic instruction, such as `CAS`, should be used for the store.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| FENCE       | FENCE       |
| MEM 1       | MEM 0       |

* initially `[0] = [1] = 0`
* `mem_0 = mem_1 = 0` is not allowed

`LOAD 0` and `LOAD 1` cannot both read `0`.

## Bound = 12

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
