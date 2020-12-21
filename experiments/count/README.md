# Statistical Counter (PerfBook 5.2)

A parametrizable version of Paul McKenney's statistical counter example, including a consistent version using `CAS`.

* `count.buggy` - increment a global variable `n` times.
* `count.cas` - increment a global variable `n` times using `CAS`.

## Usage

`run (buggy | cas) <increments> <threads> <solver> <encoder>`

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

### `count.buggy`

| Increments `n` | Threads `m` | Bound | BtorMC           | Boolector (functional) | Boolector (relational) |
| -------------- | ----------- | ----- | ---------------- | ---------------------- | ---------------------- |
| 2              | 2           | 45    | 20.959 sec       | 0.887 sec              |                        |
| 3              | 2           | 63    | 1 min 31.680 sec | 6.258 sec              |                        |
| 2              | 3           | 65    | >2 hrs!          | 13.406 sec             |                        |
| 3              | 3           | 92    |                  | 47.193 sec             |                        |

### `count.cas`

| Increments `n` | Threads `m` | Bound | BtorMC | Boolector (functional) | Boolector (relational) |
| -------------- | ----------- | ----- | ------ | ---------------------- | ---------------------- |
| 2              | 2           | 77    |        | 4 min 41.550 sec       |                        |
| 3              | 2           | 111   |        | 46 min 23.190 sec      |                        |
| 2              | 3           | 185   |        |                        |                        |
| 3              | 3           | 272   |        |                        |                        |
