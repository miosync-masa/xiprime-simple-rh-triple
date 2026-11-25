#!/bin/bash
# official leanchecker on a prefix, with LEAN_NUM_THREADS=1 so that the selected modules are
# replayed one after another. Guard: stop when swap grows by more than 8 GB or after $3 seconds.
S=/Users/iizumimamichi/C-Weil-Hunt/v11-stage3; T=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
cd $S/replay; LP=$(cat leanpath-norelease.txt); out=$1; shift; lim=$1; shift
swap(){ sysctl -n vm.swapusage | sed -E 's/.*used = ([0-9]+)\..*/\1/'; }
for m in "$@"; do base=$(swap); note=""
  ( LEAN_NUM_THREADS=1 LEAN_SYSROOT=$T PATH=$T/bin:$PATH LEAN_PATH="$LP" /usr/bin/time -l $T/bin/leanchecker -v "$m" > off-cur.out 2>&1; echo "rc=$?" >> off-cur.out ) & W=$!
  n=0; while kill -0 $W 2>/dev/null; do sleep 1; n=$((n+1)); s=$(swap)
    if [ $n -ge $lim ]; then note="GUARD time ${n}s"; elif [ $((s-base)) -gt 8000 ]; then note="GUARD swap +$((s-base))MB at ${n}s"; fi
    if [ -n "$note" ]; then pkill -x leanchecker; break; fi; done; wait $W 2>/dev/null
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$m" "$(grep -o 'rc=[0-9]*' off-cur.out | cut -d= -f2)" "$(grep -c '^replaying ' off-cur.out)" "$(awk '/ real /{print $1}' off-cur.out)" "$(awk '/maximum resident/{print $1}' off-cur.out)" "$(awk '/peak memory footprint/{print $1}' off-cur.out)" "$note" >> $out
  cp off-cur.out "off-$m.out"
done
