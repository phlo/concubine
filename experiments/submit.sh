#!/bin/sh
find . -name \*.err -o -name \*.log | xargs -n 1 cp /dev/null 
exec sbatch ./array.sh
