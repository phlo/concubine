#!/bin/bash

function die () {
  echo "[check.sh] error: $*" 1>&2
  exit 1
}

[ -d count_stat ] || die "$(basename $0) not called from experiments directory"

dir=$(ls -d */)
pattern='error'
failed="$(
  ( \
    find $dir -name *.log -o -name *.err | xargs grep -l "$pattern"; \
    find $dir -name *.err | xargs grep -L '\[runlim\] status:\s\+ok'; \
    find $dir -size 0
  ) \
  | bash -c 'while read f; do echo ${f%\.*}; done' \
  | sort \
  | uniq \
  | sed 's/^(.*)$//g'
)"

function check_empty () {
  [ -z "$(cat $1)" ] && echo "  [$(basename $1)] empty"
}

function check_pattern () {
  while read -r match
  do
    [ ! -z "$match" ] && echo "  "$match
  done <<< $(grep -h "$pattern" $*)
}

function check_runlim () {
  local status=$(grep "^\[runlim\] status:" $1)
  [ -z "$status" ] \
    && echo "  [runlim] status: missing" \
    || [[ "$status" =~ ok$ ]] || echo "  "$status
}

for i in $failed
do
  echo ${i#\./}
  check_empty $i.err || (check_runlim $i.err; check_pattern $i.err)
  check_empty $i.log || check_pattern $i.log
  echo
done
