#!/bin/bash
S3=/Users/iizumimamichi/C-Weil-Hunt/v11-stage3; T=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
LP=$(cat $S3/link/leanpath-full.txt); j=$1
cd $S3/replay
echo "start $(date '+%H:%M:%S')" > $j.log
LEAN_SYSROOT=$T PATH=$T/bin:$PATH LEAN_PATH="$LP" /usr/bin/time -l $T/bin/leanchecker $(cat $j.txt | tr '\n' ' ') >> $j.log 2>&1
echo "rc=$? end $(date '+%H:%M:%S')" >> $j.log
