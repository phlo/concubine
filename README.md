[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# ConcuBinE

> /ˈkɒŋ.kjə.baɪn/

**Concu**rrent **Bin**ary **E**valuator - a toolchain for simulating and bounded model checking of random memory access sequences by concurrent programs on a simple virtual machine.

ConcuBinE can be used to symbolically execute arbitrary programs either via **simulation**, or by **solving** the resulting bounded model checking problem using state-of-the-art SMT solvers and **replaying** them for comparison.

```
      program*
     /       \
simulate    solve
     \       /
       trace
         |
       replay
        |
      graduate
```

## Prerequisites

To build ConcuBinE from source you need:

* Make
* GCC >= 7
* [Z3](https://z3prover.github.io) (C++ API)

To run ConcuBinE, access to supported solvers' executables via `$PATH` is required:

* [Boolector](https://boolector.github.io)
* [CVC4](https://cvc4.github.io)

To build and setup these solvers you can use the scripts `setup-{boolector,cvc4,z3}.sh` in the [scripts](scripts) directory and `set-search-path.sh` for adding the required entries to your shells `$PATH` variable.

## Build

```shell
git clone https://github.com/phlo/concubine.git

cd concubine

./configure.sh

make
```

## Usage

For a list of command line options, refer to `concubine -h`.

## Documentation

ConcuBinE was developed in the course of a master thesis to evaluate the potential of different encodings for verifying concurrent software with respect to the memory ordering habits of modern hardware.
See the [thesis](doc/thesis/thesis.pdf) for further details.
