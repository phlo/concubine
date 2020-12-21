#!/bin/bash
#
# Initialize statistical counter experiment.
#
# usage: $0 <variant> <threads> <increments>

function msg () {
  echo "[count/init.sh] $*"
}

function die () {
  echo "[count/init.sh] error: $*" 1>&2
  exit 1
}

# inputs
variant=$1 # buggy or cas
m=$2
n=$3

[ -z $variant ] && die "missing test variant"
[ -z $m ] && die "missing number of threads"
[ -z $n ] && die "missing local count"

# create test directory
dir="$variant.$m.$n"
grep -q $dir $INITIALIZED && msg ${MSG/initialized/skipped} && exit
mkdir -p $dir
cwd=$(pwd)
cd $dir

# create and append mmap
mmap="init.mmap"
echo "0 0" > $mmap

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
sed -e "s/<sum>/$((m * n))/g" \
    -e "s/\<m\>/$m/g" \
    -e "s/\<n\>/$n/g" \
    $checker_template > count.checker.asm

# append to log
echo "$dir" >> "$INITIALIZED"

# print success
msg $MSG
