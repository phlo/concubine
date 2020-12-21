#!/bin/bash
#
# Run experiments from our benchmark array (see README.md).
#
# usage: $0 [<id> ...]

function die () {
  echo "[run.sh] error: $*" 1>&2
  exit 1
}

# make sure we'r in the experiments directory
[ -d count ] || die "not called from experiments directory"

. ../scripts/set-search-path.sh -f || die 'unable to set $PATH'

# check if runlim is available
! which runlim &> /dev/null && die "missing runlim"

# export runlim commands
RUNLIM='
  msg $MSG;
  exec 1>"$output".log 2>"$output".err;
  msg $MSG;
  runlim
    --single
    --time-limit=86400
    --real-time-limit=86400
    --space-limit=8000
'
export RUNLIM

# parse benchmark array
[ -z "$*" ] \
  && experiments=$(grep -o "^| \w\+\s\+|" README.md | awk '{print $2}') \
  || experiments=$*

# run experiments
for i in $experiments
do
  # split experiment into bash array {id, dir, cmd}
  IFS='|' read -r -a exp <<< \
    $(grep "^| $i\s\+|" README.md | sed -e 's/^.\s\+//' -e 's/\s\+.$//')

  [ "${#exp[@]}" = 0 ] && die "missing experiment $i"

  # remove leading / trailing whitespaces
  shopt -s extglob
  exp=("${exp[@]/#+([[:blank:]])/}") # remove leading
  exp=("${exp[@]/%+([[:blank:]])/}") # remove trailing

  # run
  export MSG="running ${exp[0]}: ${exp[1]}/${exp[2]}"
  pushd ${exp[1]} > /dev/null
  ./${exp[2]} # || exit 1 # TODO: kill whole run?
  popd > /dev/null
done
