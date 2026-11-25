#!/bin/bash
# one module per process, release not on the path. A module is stopped (and recorded as GUARD)
# when system swap use exceeds base+6 GB or it runs longer than 300 s. The run continues.
S=/Users/iizumimamichi/C-Weil-Hunt/v11-stage3; T=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
cd $S/replay; LP=$(cat leanpath-norelease.txt); tag=$1; list=$2; out=serial-$tag.tsv
swap(){ sysctl -n vm.swapusage | sed -E 's/.*used = ([0-9]+)\..*/\1/'; }
printf "module\trc\treal_s\tmaxrss_bytes\tpeak_footprint_bytes\tnote\n" > $out
while read -r m; do [ -z "$m" ] && continue
  base=$(swap); note=""
  ( LEAN_SYSROOT=$T PATH=$T/bin:$PATH LEAN_PATH="$LP" /usr/bin/time -l $T/bin/leanchecker "$m" > cur-$tag.out 2>&1; echo "rc=$?" >> cur-$tag.out ) & W=$!
  n=0; while kill -0 $W 2>/dev/null; do sleep 1; n=$((n+1)); s=$(swap)
    if [ $n -ge 300 ]; then note="GUARD time ${n}s"; elif [ $((s-base)) -gt 6000 ]; then note="GUARD swap +$((s-base))MB at ${n}s"; fi
    if [ -n "$note" ]; then pkill -x leanchecker; break; fi; done; wait $W 2>/dev/null
  rc=$(grep -o "rc=[0-9]*" cur-$tag.out | cut -d= -f2); re=$(awk '/ real /{print $1}' cur-$tag.out); rs=$(awk '/maximum resident/{print $1}' cur-$tag.out); fp=$(awk '/peak memory footprint/{print $1}' cur-$tag.out)
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$m" "$rc" "$re" "$rs" "$fp" "$note" >> $out
  if [ -z "$note" ] && [ "$rc" != "0" ]; then cp cur-$tag.out fail-$tag.out; echo "STOP at $m" >> $out; exit 1; fi
  if [ -n "$note" ]; then sleep 5; fi
done < $list
echo "DONE" >> $out
