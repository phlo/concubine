# Statistical Counter (PerfBook 5.2)

* `count_stat` - increment a global variable `n` times.
* `count_stat.cas` - increment a global variable `n` times using `CAS`.

## Usage

`run-count_stat*.sh <increments> <threads> <encoder> <solver> <output directory>`

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

### `count_stat`

| Increments `n` | Threads `m` | Bound | BtorMC           | Boolector (functional) | Boolector (relational) |
| -------------- | ----------- | ----- | ---------------- | ---------------------- | ---------------------- |
| 2              | 2           | 45    | 20.959 sec       | 0.887 sec              |                        |
| 3              | 2           | 63    | 1 min 31.680 sec | 6.258 sec              |                        |
| 2              | 3           | 65    | >2 hrs!          | 13.406 sec             |                        |
| 3              | 3           | 92    |                  | 47.193 sec             |                        |

### `count_stat.cas`

| Increments `n` | Threads `m` | Bound | BtorMC | Boolector (functional) | Boolector (relational) |
| -------------- | ----------- | ----- | ------ | ---------------------- | ---------------------- |
| 2              | 2           | 77    |        | 4 min 41.550 sec       |                        |
| 3              | 2           | 111   |        | 46 min 23.190 sec      |                        |
| 2              | 3           | 185   |        |                        |                        |
| 3              | 3           | 272   |        |                        |                        |
