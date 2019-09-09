# Global Visibility

> [P.220](https://www.amd.com/system/files/TechDocs/24593.pdf#page=220)

If a very strong memory ordering model is required that does not allow local store-load bypasses, an `FENCE` instruction or an atomic instruction such as `CAS` should be used between the store and the subsequent load.
This enforces a memory ordering stronger than total store ordering.

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| FENCE       | FENCE       |
| MEM 0       | MEM 1       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` is not allowed

In this example, the `FENCE` instruction ensures that any buffered stores are globally visible before the loads are allowed to execute, so the result `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` will not occur.

## Bound = 14

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 6                 | 1       | 7     |
| 1         | 6                 | 1       | 7     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
