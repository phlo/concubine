# Demo Example

> [Intel Litmus Test #3](../litmus/intel/3)

Loads may be reordered with an earlier store to a different location.

## Programs

| Processor 0 | Processor 1 | Checker       |
| ----------- | ----------- | ------------- |
| ADDI 1      | ADDI 1      |               |
| STORE 0     | STORE 1     |               |
| LOAD 1      | LOAD 0      |               |
| CHECK 0     | CHECK 0     | CHECK 0       |
|             |             | ADD 0         |
|             |             | ADD 1         |
|             |             | JZ error      |
|             |             | EXIT 0        |
|             |             | error: EXIT 1 |
