# Intra-Processor Forwarding Is Allowed

> Example 8-5, [P.276](https://software.intel.com/sites/default/files/managed/7c/f1/253668-sdm-vol-3a.pdf#page=276)

The memory-ordering model allows concurrent stores by two threads to be seen in different orders by those two threads; specifically, each thread may perceive its own store occurring before that of the other.
This is illustrated by the following example:

## Example 8-5. Intra-Processor Forwarding is Allowed

| Thread 0    | Thread 1    |
| ----------- | ----------- |
| ADDI 1      | ADDI 1      |
| STORE 0     | STORE 1     |
| LOAD 0      | LOAD 1      |
| LOAD 1      | LOAD 0      |

* initially `[0] = [1] = 0`
* `accu_0 = accu_1 = 0` is allowed

The memory-ordering model imposes no constraints on the order in which the two stores appear to execute by the two threads.
This fact allows thread 0 to see its store before seeing thread 1's, while thread 1 sees its store before seeing thread 0's.
(Each thread is self consistent.)
This allows `accu_0 = accu_1 = 0`.

In practice, the reordering in this example can arise as a result of store-buffer forwarding.
While a store is temporarily held in a thread's store buffer, it can satisfy the thread's own loads but is not visible to (and cannot satisfy) loads by other threads.

## Bound = 12

| Thread    | Instructions[^1]  | Flushes | Total |
| --------- | ----------------  | ------- | ----- |
| 0         | 5                 | 1       | 6     |
| 1         | 5                 | 1       | 6     |

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| z3-4.8.6 (functional)            | 50           |
| btormc-3.1.0-pre                 | 54           |
| boolector-3.1.0-pre (functional) | 67           |
| z3-4.8.6 (relational)            | 961          |
| boolector-3.1.0-pre (relational) | 1227         |
| cvc4-1.7 (relational)            | 1411         |
| cvc4-1.7 (functional)            | 18749        |

## Notes

[^1]: including final `HALT`
