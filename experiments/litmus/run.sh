#!/bin/bash
#
# Run litmus test.
#
# usage: $0 <encoder> <solver>

function msg () {
  echo "[litmus/run.sh] $*"
}

function die () {
  echo "[litmus/run.sh] error: $*" 1>&2
  exit 1
}

# inputs
solver=$1
encoder=$2

[ -z "$solver" ] && die "missing solver"
[ -z "$encoder" ] && die "missing encoder"

# base command
cmd="concubine solve -v -s $solver"

# append encoder and constraints
[ $encoder = functional ] && cmd="$cmd -e smtlib"
[ $encoder = relational ] && cmd="$cmd -e smtlib-relational"
[ $encoder = btor2 ] \
  && cmd="$cmd -c constraints.btor2" \
  || cmd="$cmd -c constraints.smt2"

# append mmap
[ -f init.mmap ] && cmd="$cmd -m init.mmap"

# append output file naming
output="$solver-$encoder"
cmd="$cmd -o $output $bound"

# append bound
cmd="$cmd $(grep 'Bound =' README.md | awk '{print $4}')"

# append programs
cmd="$cmd thread.*.asm"

# run litmus test using runlim
eval $RUNLIM $cmd

# be paranoid and check result ...
[ ! -f $output.log ] && die "missing log file"

grep -q "is allowed$" README.md && [ ! -f $output.trace ] \
  && die "expected test to be sat"

grep -q "is not allowed$" README.md && [ -f $output.trace ] \
  && die "expected test to be unsat"
