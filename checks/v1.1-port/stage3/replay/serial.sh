#!/bin/bash
# one module per process, release not on the path; stop at first failure or footprint > 8 GB
S=/Users/iizumimamichi/C-Weil-Hunt/v11-stage3; T=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
cd $S/replay; LP=$(cat leanpath-norelease.txt); tag=$1; list=$2; out=serial-$tag.tsv
printf "module\trc\treal_s\tmaxrss_bytes\tpeak_footprint_bytes\n" > $out
while read -r m; do [ -z "$m" ] && continue
  ( LEAN_SYSROOT=$T PATH=$T/bin:$PATH LEAN_PATH="$LP" /usr/bin/time -l $T/bin/leanchecker "$m" > cur-$tag.out 2>&1; echo "rc=$?" >> cur-$tag.out ) & W=$!
  n=0; while kill -0 $W 2>/dev/null; do sleep 1; n=$((n+1)); if [ $n -ge 900 ]; then pkill -f "bin/leanchecker $m"; echo "KILLED" >> cur-$tag.out; fi; done; wait $W 2>/dev/null
  rc=$(grep -o "rc=[0-9]*" cur-$tag.out | cut -d= -f2); re=$(awk '/ real /{print $1}' cur-$tag.out); rs=$(awk '/maximum resident/{print $1}' cur-$tag.out); fp=$(awk '/peak memory footprint/{print $1}' cur-$tag.out)
  printf "%s\t%s\t%s\t%s\t%s\n" "$m" "$rc" "$re" "$rs" "$fp" >> $out
  if [ "$rc" != "0" ] || [ "${fp:-0}" -gt 8000000000 ]; then cp cur-$tag.out fail-$tag.out; echo "STOP at $m" >> $out; exit 1; fi
done < $list
echo "DONE" >> $out
