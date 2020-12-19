#!/bin/bash

usage () {
cat << EOF
usage: $(basename $0) [ <option> ... ] <directory>

where '<option>' is one of the following

-h|--help                   print this command line summary

-t <type>                   print a specific <type> of statistic:
                            * encoder - encoder performance (time and size)
                            * solver - solver performance (time)
                            * combined - all of the above

--encoder-time <factor>     multiply encoding times [sec] by a given <factor>
--solver-time <factor>      multiply solver runtimes [sec] by a given <factor>
EOF
exit 0
}

die () {
  echo "[print-experiments.sh] error: $*" 1>&2
  exit 1
}

#------------------------------------------------------------------------------#

# inputs
root="$(pwd)"
statistic=combined
encoder_factor=1
solver_factor=1

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;

    -t) shift ; statistic=$1 ;;

    --encoder-time) shift ; encoder_factor=$1 ;;
    --solver-time) shift ; solver_factor=$1 ;;

    *) [ -d "$1" ] && root="$1" || die "no such directory [$1]" ;;
  esac
  shift
done

[[ "$root" =~ "/experiments/" ]] || die "missing experiments directory"
root=$(realpath $root)
cd ${root%%experiments/*}/experiments
root="${root%/}"
root="${root##*/experiments}"
root="${root#/}"

case $statistic in
  encoder|solver|combined) ;;
  *) die "unknown statistic [$statistic]"
esac

#------------------------------------------------------------------------------#

# globals

variants='
  btormc-btor2
  boolector-functional
  boolector-relational
  z3-functional
  z3-relational
  cvc4-functional
  cvc4-relational
'

#------------------------------------------------------------------------------#

mean () {
  vals=("$@")
  mean=0
  for i in ${vals[@]}
  do
    mean=$(bc <<< "$mean + $i")
  done
  bc -l <<< "scale=3; $mean / ${#vals[@]}"
}

norm_int () {
  local cmd='{ printf "%d", $0 }'
  [ -z $@ ] && awk "$cmd" || awk "$cmd" <<< $@
}

norm_float () {
  local cmd='{ printf "%0.3f", $0 }'
  [ -z $@ ] && awk "$cmd" || awk "$cmd" <<< $@
}

#------------------------------------------------------------------------------#

header="experiment"
if [ $statistic = encoder ]
then
  header='
    experiment
    btor2-time
    btor2-size
    functional-time
    functional-size
    relational-time
    relational-size
  '
else
  for run in $variants
  do
    [ $statistic = combined ] \
      && header="$header $run-encoder-time $run-encoder-size"
    header="$header $run-solver-time"
  done
fi
echo $header
nhead=$(wc -w <<< $header)

for exp in $(find $root -type d | sort -V)
do
  [ -f "$exp/btormc-btor2.log" ] || continue
  row=(${exp//\//:})
  fun_times=()
  fun_sizes=()
  rel_times=()
  rel_sizes=()
  for run in $variants
  do
    log="${exp}/${run}.log"

    [ -f $log ] || die "missing $log"

    data=$(grep -o "generated.*commands$\|\(solving\|encoding\) took.*$" $log)

    e_time=$(grep -o "encoding.*seconds" <<< $data \
               | awk "{ printf \"%0.3f\", \$3 * $encoder_factor }")
    e_size=$(grep -o "generated.*commands" <<< $data | awk '{ print $2 }')
    s_time=$(grep -o "solving.*seconds" <<< $data \
               | awk "{ printf \"%0.3f\", \$3 * $solver_factor }")
    (( "$(wc -m <<< $s_time)" > 6 )) && s_time=$(sed 's/0\+$//g' <<< $s_time)

    if [ $statistic = encoder ]
    then
      case $run in
        *btor2) row+=($(norm_float $e_time) $e_size) ;;
        *functional)
          fun_times+=($e_time)
          fun_sizes+=($e_size)
          ;;
        *relational)
          rel_times+=($e_time)
          rel_sizes+=($e_size)
          ;;
      esac
    fi

    [ $statistic = combined ] && row+=($e_time $e_size $s_time)
    [ $statistic = solver ] && row+=($s_time)
  done

  if [ $statistic = encoder ]
  then
    fun_time=$(mean ${fun_times[@]} | norm_float)
    fun_size=$(mean ${fun_sizes[@]} | norm_int)
    [ $fun_size != ${fun_sizes[0]} ] && die "formula size missmatch"

    rel_time=$(mean ${rel_times[@]} | norm_float)
    rel_size=$(mean ${rel_sizes[@]} | norm_int)
    [ $rel_size != ${rel_sizes[0]} ] && die "formula size missmatch"

    row+=($fun_time $fun_size $rel_time $rel_size)
  fi

  echo ${row[@]}
  # [ $nhead != $(wc -w <<< ${row[@]}) ] && die "missing row items"
done
