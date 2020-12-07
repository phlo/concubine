#!/bin/sh
#SBATCH -J pimsimt
#SBATCH -c 2
#SBATCH -a 1-259
#SBATCH -o /dev/null
#SBATCH -e /dev/null
echo "c array.sh: path:     $path"
echo "c array.sh: name:     $name"
echo "c array.sh: task:     $SLURM_ARRAY_TASK_ID"
echo "c array.sh: host:     `hostname`"
echo "c array.sh: uname:    `uname -a`"
echo "c array.sh: start:    `date`"
echo "c array.sh: noturbo:  `show-turbo-mode-disabled.sh`"
echo "c array.sh: governor: `show-scaling-governors.sh |awk '{print $NF}'|sort|uniq -c|sed -e 's,^ *,,'`"
echo "c array.sh: tmp:      `df -m /tmp/|tail -1|awk '{print $(NF-1)}'`"
./run $SLURM_ARRAY_TASK_ID
echo "c array.sh: end:      `date`"
