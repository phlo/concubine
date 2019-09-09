# Dependent Stores Appear In Program Order

> [P.220](https://www.amd.com/system/files/TechDocs/24593.pdf#page=220)

Dependent stores between different processors appear to occur in program order, as shown in the code example below.

| Processor 0 | Processor 1 | Processor 2 |
| ----------- | ----------- | ----------- |
| ADDI 1      | MEM 0       |             |
| STORE 0     | JNZ 3       |             |
|             | ADDI 1      |             |
|             | STORE 1     | MEM 1       |
|             |             | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_1 = mem_2 = 1` and `accu_2 = 0` is not allowed

If processor 1 reads a value from `[0]` (written by processor 0) before carrying out a store to `[1]`, and if processor 2 reads the updated value from `[1]`, a subsequent read of `[0]` must also be the updated value.

## Bound = 13

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 3                 | 1       | 4     |
| 1         | 5                 | 1       | 6     |
| 2         | 3                 | 0       | 3     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
* Identical to [Intel 6](../../intel/6)
