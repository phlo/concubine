#!/bin/bash
#
# usage: $0 <variant> <n> <m> <encoder> <solver>
#
# Generate input files and run count_stat experiment.

function msg () {
  echo "[count_stat/run.sh] $*"
}

function die () {
  echo "[count_stat/run.sh] error: $*" 1>&2
  exit 1
}

# inputs
variant=$1 # buggy or cas
n=$2
m=$3
solver=$4
encoder=$5

[ -z $variant ] && die "missing test variant"
[ -z $n ] && die "missing local count"
[ -z $m ] && die "missing number of threads"
[ -z $solver ] && die "missing solver"
[ -z $encoder ] && die "missing encoder"

# create test directory
dir=$variant.$n.$m
mkdir -p $dir
cwd=$(pwd)
cd $dir

# base command
cmd="concubine solve -v -s $solver"

# append encoder
[ $encoder = functional ] && cmd="$cmd -e smtlib"
[ $encoder = relational ] && cmd="$cmd -e smtlib-relational"

# create and append mmap
mmap=init.mmap
echo "0 0" > $mmap
cmd="$cmd -m $mmap"

# append output file naming
output=$solver-$encoder
cmd="$cmd -o $output $bound"

# select template
checker_template=$cwd/count_stat.checker.template
case $variant in
  buggy) thread_template=$cwd/count_stat.buggy.template ;;
  cas) thread_template=$cwd/count_stat.cas.template ;;
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

# create threads
for t in $(seq 0 $((m - 1)))
do
  adr=$((t + 10))
  prog=$(basename ${thread_template%.*}.$t.asm)

  # generate program
  sed -e "s/<adr>/$adr/g" \
      -e "s/\<n\>/$n/g" \
      $thread_template > $prog

  # append local counter to mmap
  echo "$adr $n" >> $mmap

  # append program
  cmd="$cmd $prog"
done

# generate and append checker
sed -e "s/<sum>/$((n * m))/g" \
    -e "s/\<n\>/$n/g" \
    -e "s/\<m\>/$m/g" \
    $checker_template > count_stat.checker.asm
cmd="$cmd count_stat.checker.asm"

# run statistical counter experiment using runlim
eval $RUNLIM $cmd

# be paranoid and check result ...
[ ! -f $output.log ] && die "missing log file"

[ $variant = buggy -a ! -f $output.trace ] \
  && die "expected test to be sat"

[ $variant = cas -a -f $output.trace ] \
  && die "expected test to be unsat"
