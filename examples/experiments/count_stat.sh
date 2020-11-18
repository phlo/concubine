#!/bin/bash
#
# usage: $0 <template> <n> <m> <encoder> <solver> <dir>
#
# Generate input files and run benchmark.

# executable
concubine=../../concubine

# inputs
template=$1 # thread template
n=$2        # local counter
m=$3        # number of threads
encoder=$4  # encoder
solver=$5   # solver
dir=$6      # target directory

[ -z $template ] && echo "missing template" >&2 && exit 1
[ -z $n ] && echo "missing local count" >&2 && exit 1
[ -z $m ] && echo "missing number of threads" >&2 && exit 1
[ -z $encoder ] && echo "missing encoder" >&2 && exit 1
[ -z $solver ] && echo "missing solver" >&2 && exit 1
[ -z $dir ] && echo "missing target directory" >&2 && exit 1

# reset mmap (just in case)
echo "0 0" > $dir/init.mmap

# program files
threads=""

# generate threads
for t in $(seq 0 $((m - 1)))
do
  adr=$((t + 10))
  thread=$dir/${template%.*}.$t.asm

  # generate program
  sed -e "s/<adr>/$adr/g" \
      -e "s/\<n\>/$n/g" \
      $template > $thread

  # append to mmap
  echo "$adr $n" >> $dir/init.mmap

  # append to programs
  threads="$threads $thread"
done

# generate checker
sed -e "s/<sum>/$((n * m))/g" \
    -e "s/\<n\>/$n/g" \
    -e "s/\<m\>/$m/g" \
    count_stat.checker.asm > $dir/count_stat.checker.asm

# compute bound
formula=$(grep "formula" $template | cut -d'=' -f2)
cas=$(grep "cas =" $template | grep -o "[[:digit:]]\+")
loop=$(grep "loop =" $template | grep -o "[[:digit:]]\+")
total=$(grep "total =" $template | grep -o "[[:digit:]]\+")
checker=$(grep "total =" count_stat.checker.asm | grep -o "[[:digit:]]\+")
bound=$((formula * m + checker))

# start benchmark
time $concubine solve -e $encoder -s $solver -o $dir/result -m $dir/init.mmap $bound $threads $dir/count_stat.checker.asm
