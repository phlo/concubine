#!/bin/bash

usage () {
cat << EOF
usage: $(basename $0) [ <option> ... ] <directory> ...

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
  echo "[experiment-stats.sh] error: $*" 1>&2
  exit 1
}

#------------------------------------------------------------------------------#

# inputs
roots=()
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

    *) [ -d "$1" ] && roots+=("$1") || die "no such directory [$1]" ;;
  esac
  shift
done

for i in ${!roots[@]}
do
  roots[$i]=$(realpath ${roots[i]})
  [[ "${roots[i]}" =~ "/experiments/" ]] || die "missing experiments directory"
done

roots=($(echo ${roots[@]}| tr ' ' '\n' | sort -n))

case $statistic in
  encoder|solver|combined) ;;
  *) die "unknown statistic [$statistic]"
esac

#------------------------------------------------------------------------------#

mkrow () {
  printf ",%s" "$@" | sed 's/^,//g'
  echo
}

mean () {
  vals=("$@")
  mean=0
  for i in ${vals[@]}
  do
    mean=$(bc <<< "$mean + $i")
  done
  bc -l <<< "scale=2; $mean / ${#vals[@]}"
}

int () {
  local cmd='{ printf "%d", $0 }'
  [ -z $@ ] && awk "$cmd" || awk "$cmd" <<< $@
}

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

header="experiment"
if [ $statistic = encoder ]
then
  header='
    experiment
    bound
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
mkrow $header
nhead=$(wc -w <<< $header)

#------------------------------------------------------------------------------#

for root in ${roots[@]}
do
  cd ${root%%experiments/*}/experiments
  root="${root%/}"
  root="${root##*/experiments}"
  root="${root#/}"

  for exp in $(find $root -type d | sort -V)
  do
    [ -f "$exp/btormc-btor2.log" ] || continue
    row=("$(sed -e 's;.*/\(\(buggy\|cas\)\.\)\?;;g' <<< $exp | sed 's;\.; ;g')")
    fun_times=()
    fun_sizes=()
    rel_times=()
    rel_sizes=()
    for run in $variants
    do
      log="${exp}/${run}.log"

      [ -f $log ] || die "missing $log"

      data=$(grep -o "generated.*commands$\|\(solving\|encoding\) took.*$" $log)

      e_size=$(grep -o "generated.*commands" <<< $data | awk '{ print $2 }')
      e_time=$(grep -o "encoding.*seconds" <<< $data \
                 | awk "{ printf \"%0.2f\", \$3 * $encoder_factor }")
      [ "$e_time" = "0.00" ] && e_time="0.01"
      s_time=$(grep -o "solving.*seconds" <<< $data \
                 | awk "{ printf \"%0.2f\", \$3 * $solver_factor }")
      if [ -z "$s_time" ]
      then
        grep -q "out of \w\+" "${exp}/${run}.err" \
          && s_time="inf" \
          || die "neither out of memory nor time, but missing solver time"
      fi
      [ "$s_time" = "0.00" ] && s_time="0.01"

      if [ $statistic = encoder ]
      then
        case $run in
          *btor2)
            [[ $root == count* ]] \
              && bound=$(grep -o "argv\[9\].*$" "${exp}/${run}.err" \
                           | awk '{print $2}') \
              || bound=$(grep -o "Bound =.*$" "${exp}/README.md" \
                           | awk '{print $3}')
            row+=($bound $e_time $e_size) ;;
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
      fun_time=$(mean ${fun_times[@]})
      fun_size=$(mean ${fun_sizes[@]} | int)
      [ $fun_size != ${fun_sizes[0]} ] && die "formula size missmatch at $exp"

      rel_time=$(mean ${rel_times[@]})
      rel_size=$(mean ${rel_sizes[@]} | int)
      [ $rel_size != ${rel_sizes[0]} ] && die "formula size missmatch at $exp"

      row+=($fun_time $fun_size $rel_time $rel_size)
    fi

    mkrow "${row[@]}"
    if [[ $nhead > $(wc -w <<< ${row[@]}) ]]
    then
      die "missing row items"
    fi
  done
done
