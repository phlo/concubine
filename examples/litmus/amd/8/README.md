# Local Visibility

> [P.220](https://www.amd.com/system/files/TechDocs/24593.pdf#page=220)

The local visibility (within a processor) for a memory operation may differ from the global visibility (from another processor).
Using a data bypass, a local load can read the result of a local store in a store buffer, before the store becomes globally visible.
Program order is still maintained when using such bypasses.

## Local Visibility

| Processor 0 | Processor 1 |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| MEM 0       | MEM 1       |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` is allowed

`LOAD 0` in processor 0 can read `1` using the data bypass, while `LOAD 0` in processor 1 can read `0`.
Similarly, `LOAD 1` in processor 1 can read `1` while `LOAD 1` in processor 0 can read `0`.
Therefore, the result `mem_0 = 1`, `accu_0 = 0`, `mem_1 = 1` and `accu_1 = 0` may occur.
There are no constraints on the relative order of when the `STORE 0` of processor 0 is visible to processor 1 relative to when the `STORE 1` of processor 1 is visible to processor 0.

## Bound = 12

| Processor | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

[^1]: including final `HALT`

## Notes

* Using `MEM` instead of `LOAD` to ignore `ADDI`.
* Identical to [Intel 5](../../intel/5)
