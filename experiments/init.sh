#!/bin/bash
#
# Initialize experiments from our benchmark array (see README.md).
#
# usage: $0 [<id> ...]

function die () {
  echo "[init.sh] error: $*" 1>&2
  exit 1
}

# make sure we'r in the experiments directory
[ -d count_stat ] || die "$(basename $0) not called from experiments directory"

# create temporary log file
export INITIALIZED=$(mktemp --tmpdir init-XXX.log)
trap "rm -rf $INITIALIZED" EXIT

# parse benchmark array
[ -z "$*" ] \
  && experiments=$(grep -o "^| \w\+\s\+|" README.md | awk '{print $2}') \
  || experiments=$*

# init experiments
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

  # init
  [ ! -f ${exp[1]}/init.sh ] && continue
  exp[2]=${exp[2]/run\.sh/init.sh}
  export MSG="initialized ${exp[0]}: ${exp[1]}/${exp[2]}"
  pushd ${exp[1]} > /dev/null
  ./${exp[2]}
  popd > /dev/null
done
