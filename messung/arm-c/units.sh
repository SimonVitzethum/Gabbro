#!/bin/bash
# usage: units.sh GABBRO_BIN OUTDIR     (run from the worktree root)
# For each of the 17 units agent A listed as failing on the system-call stub: rewrite its linux
# gates to aarch64 (to_aarch64.py), check, emit, cross-compile with -Wall -Wextra -Werror.
BIN=$1; OUT=$2; mkdir -p "$OUT"
: > "$OUT/summary.txt"
for n in 1114 149 150 155 156 160 163 164 172 173 174 181 182 183 74 90 96; do
  f=$(ls beispiele/$n-*.gab | head -1)
  b=$(basename "$f" .gab)
  python3 messung/arm-c/to_aarch64.py "$f" "$OUT/$b.gab"
  ck=ok; em=ok; cc=ok
  "$BIN" check "$OUT/$b.gab" > "$OUT/$b.check" 2>&1 || ck=FAIL
  "$BIN" emit "$OUT/$b.gab" > "$OUT/$b.c" 2> "$OUT/$b.emiterr" || em=FAIL
  if [ $em = ok ]; then
    fl=""
    case $n in 172|173|183) fl="-ffreestanding";; esac
    aarch64-linux-gnu-gcc -std=c11 -Wall -Wextra -Werror $fl -Ilaufzeit -c -o "$OUT/$b.o" "$OUT/$b.c" 2> "$OUT/$b.cc" || cc=FAIL
  else
    cc=-
  fi
  echo "$n $b check=$ck emit=$em a64gcc=$cc" >> "$OUT/summary.txt"
done
cat "$OUT/summary.txt"
