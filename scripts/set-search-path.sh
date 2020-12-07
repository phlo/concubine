#!/bin/bash
#
# Source this script to ensure all required executables are accessible through
# $PATH, or execute it to print the required value to stdout.
#
# usage: $0 [-f]
#
# Where '-f' prefers binaries under 'deps/install/bin' and 'build/bin'.

trap "unset check paths ret root sourced tmp; trap - RETURN" RETURN

root=$(realpath $(dirname $(dirname $BASH_SOURCE)))
paths="${root}/deps/install/bin:${root}/build/bin"

PATH=$(sed -e "s#:\?$paths:\?##g" <<< $PATH)

[ "$0" = "$BASH_SOURCE" ] && sourced=no || sourced=yes
[ "$1" = "-f" ] && tmp="${paths}:$PATH" || tmp="$PATH:${paths}"
[ $sourced = yes ] && ret=return || ret=exit

function check () {
  if ! PATH="$tmp" which $1 &> /dev/null
  then
    [[ "$PS1" == *"[ConcuBinE]"* ]] && PS1="${PS1#\[ConcuBinE\] }"
    echo "[$(basename $BASH_SOURCE)] error: missing $1" 1>&2
    $ret 1
  fi
}

for bin in boolector btormc cvc4 concubine
do
  check $bin || $ret
done

if [ $sourced = yes ]
then
  PATH="$tmp"
  [[ "$PS1" != *"[ConcuBinE]"* ]] && PS1="[ConcuBinE] $PS1"
else
  echo "$tmp"
fi
