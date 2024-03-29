#!/bin/bash
#
# Run statistical counter experiment.
#
# usage: $0 <variant> <threads> <increments> <encoder> <solver>

function msg () {
  echo "[count/run.sh] $*"
}

function die () {
  echo "[count/run.sh] error: $*" 1>&2
  exit 1
}

# inputs
variant=$1 # buggy or cas
m=$2
n=$3
solver=$4
encoder=$5

[ -z $variant ] && die "missing test variant"
[ -z $m ] && die "missing number of threads"
[ -z $n ] && die "missing local count"
[ -z $solver ] && die "missing solver"
[ -z $encoder ] && die "missing encoder"

# create test directory
dir="$variant.$m.$n"
cwd=$(pwd)
cd $dir 2> /dev/null || die "missing count/$dir - run './init.sh $( \
  awk '{ print $2 }' <<< "$MSG" | tr -d ':' \
)'"

# base command
cmd="concubine solve -v -s $solver"

# append encoder
[ $encoder = functional ] && cmd="$cmd -e smtlib"
[ $encoder = relational ] && cmd="$cmd -e smtlib-relational"

# append mmap
cmd="$cmd -m init.mmap"

# append output file naming
output="$solver-$encoder"
cmd="$cmd -o $output"

# select template
checker_template="$cwd/count.checker.template"
case $variant in
  buggy) thread_template="$cwd/count.buggy.template" ;;
  cas) thread_template="$cwd/count.cas.template" ;;
  *) die "unknown variant [$variant]" ;;
esac

# compute and append bound
formula=$(grep "formula" $thread_template | cut -d'=' -f2)
cas=$(grep "cas =" $thread_template | grep -o "[[:digit:]]\+")
loop=$(grep "loop =" $thread_template | grep -o "[[:digit:]]\+")
total=$(grep "total =" $thread_template | grep -o "[[:digit:]]\+")
checker=$(grep "total =" $checker_template | grep -o "[[:digit:]]\+")
bound=$((formula * m + checker))
cmd="$cmd $bound"

# append threads
cmd="$cmd $(basename ${thread_template%.*}).*.asm"

# append checker
cmd="$cmd count.checker.asm"

# run statistical counter experiment using runlim
eval $RUNLIM $cmd

# be paranoid and check result ...
[ ! -f $output.log ] && die "missing log file"

[ $variant = buggy -a ! -f $output.trace ] \
  && die "expected test to be sat"

[ $variant = cas -a -f $output.trace ] \
  && die "expected test to be unsat"
