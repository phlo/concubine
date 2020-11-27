# Litmus Tests

The x86-TSO memory-ordering model (used by AMD and Intel) is defined by a set of litmus tests.
To show equivalence of ConcuBinE-TSO and x86-TSO, the tests have been ported to ConcuBinE.

## Runtime

> Intel(R) Core(TM) i7-3770K CPU @ 3.50GHz

| Solver                           | Runtime [ms] |
| -------------------------------- | ------------ |
| boolector-3.1.0-pre (functional) | 1064         |
| z3-4.8.6 (functional)            | 1240         |
| btormc-3.1.0-pre                 | 2953         |
| boolector-3.1.0-pre (relational) | 21418        |
| z3-4.8.6 (relational)            | 25531        |
| cvc4-1.7 (functional)            | 10147740     |
| cvc4-1.7 (relational)            | 83567796     |
