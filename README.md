# Concubine

> /ˈkɒŋ.kjə.baɪn/

**Concu**rrent **Bin**ary **E**valuator - a toolchain for simulating and bounded model checking of random memory access sequences by concurrent programs on a simple virtual machine.

Concubine can be used to generate schedules of arbitrary programs either via **simulation**, or by **solving** the resulting SMT problem as well as **replaying** them for comparison.

```
         program*
        /        \
simulate          solve
        \        /
         schedule
            |
          replay
            |
         graduate
```

## Prerequisites

To run Concubine, [Boolector](https://github.com/Boolector/boolector) has to be accessible via `$PATH`.

## Build

```shell
git clone https://socialg.it/phlo/psimsmt.git

cd psimsmt

make
```

## Usage

For a list of command line options, refer to `psimsmt -h`.

## Machine

* 16 bit machine
* 1 accumulator register
* 1 (hidden) register memorizing values for *compare and swap*
* directly accessible flat memory
* any number of threads
* random schedule

### Instruction Set

| Symbol  | Operand | Description |
| ------- | --------| --------------- |
| `LOAD`  | _addr_  | load value stored at _addr_ into the accumulator |
| `STORE` | _addr_  | store the accumulator's value at _addr_ |
| `ADD`   | _addr_  | add the value found at _addr_ to the accumulator |
| `ADDI`  | _val_   | add the immediate value _val_ to the accumulator |
| `SUB`   | _addr_  | subtracts the value found at _addr_ from the accumulator |
| `SUBI`  | _val_   | subtracts the immediate value _val_ from the accumulator |
| `CMP`   | _addr_  | compare accumulator with the value found at _addr_ |
| `JMP`   | _pc_    | unconditional jump to the statement at _pc_ |
| `JZ`    | _pc_    | jump to the statement at _pc_ iff the previous compare yields zero (arguments are equal) |
| `JNZ`   | _pc_    | jump to the statement at _pc_ iff the previous compare is not zero (arguments are _not_ equal) |
| `JS`    | _pc_    | jump to the statement at _pc_ iff the previous compare results in a set _signed flag_ (accu is negative) |
| `JNS`   | _pc_    | jump to the statement at _pc_ iff the previous compare results in a unset _signed flag_ (accu is zero or positive) |
| `JNZNS` | _pc_    | jump to the statement at _pc_ iff the previous compare is non-zero and results in a unset _signed flag_ (accu is positive) |
| `MEM`   | _addr_  | loads the value at _addr_ into the accumulator and assigns it into the special CAS register |
| `CAS`   | _addr_  | atomically compares the expected value stored with `MEM` to the actual value found at _addr_ and only writes the accumulator's content back to _addr_ if they are equal |
| `SYNC`  | _id_    | wait for all other threads to synchronise on barrier _id_ |
| `EXIT`  | _val_   | stop the machine and return _val_ as exit code |

### Addressing Modes

* direct: `LOAD 1`
* indirect: `LOAD [1]`
