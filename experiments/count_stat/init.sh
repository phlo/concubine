#!/bin/bash
#
# Initialize count_stat experiment.
#
# usage: $0 <variant> <n> <m>

function msg () {
  echo "[count_stat/init.sh] $*"
}

function die () {
  echo "[count_stat/init.sh] error: $*" 1>&2
  exit 1
}

# inputs
variant=$1 # buggy or cas
n=$2
m=$3

[ -z $variant ] && die "missing test variant"
[ -z $n ] && die "missing local count"
[ -z $m ] && die "missing number of threads"

# create test directory
dir="$variant.$n.$m"
grep -q $dir $INITIALIZED && msg ${MSG/initialized/skipped} && exit
mkdir -p $dir
cwd=$(pwd)
cd $dir

# create and append mmap
mmap="init.mmap"
echo "0 0" > $mmap

# select template
checker_template="$cwd/count_stat.checker.template"
case $variant in
  buggy) thread_template="$cwd/count_stat.buggy.template" ;;
  cas) thread_template="$cwd/count_stat.cas.template" ;;
  *) die "unknown variant [$variant]" ;;
esac

# compute and append bound
formula=$(grep "formula" $thread_template | cut -d'=' -f2)
cas=$(grep "cas =" $thread_template | grep -o "[[:digit:]]\+")
loop=$(grep "loop =" $thread_template | grep -o "[[:digit:]]\+")
total=$(grep "total =" $thread_template | grep -o "[[:digit:]]\+")
checker=$(grep "total =" $checker_template | grep -o "[[:digit:]]\+")
bound=$((formula * m + checker))

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
done

# generate and append checker
sed -e "s/<sum>/$((n * m))/g" \
    -e "s/\<n\>/$n/g" \
    -e "s/\<m\>/$m/g" \
    $checker_template > count_stat.checker.asm

# append to log
echo "$dir" >> "$INITIALIZED"

# print success
msg $MSG
