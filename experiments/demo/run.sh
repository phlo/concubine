#!/bin/bash

LITMUS=store-buffer.litmus

if [ -z "$1" ]
then
   echo "[$0] error: missing number of test runs" >&2
   exit 1
fi

if ! [[ $1 =~ ^[0-9]+$ ]]
then
   echo "[$0] error: $1 ain't no number" >&2
   exit 1
fi

make $LITMUS > /dev/null

i=$1
x=0

while [ $i -gt 0 ]
do
  (./$LITMUS || false) >/dev/null 2>&1 || ((x=x+1))
  ((i=i-1))
done

echo "[$0] $x out of $1 failed"
