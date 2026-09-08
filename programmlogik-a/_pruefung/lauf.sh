#!/bin/bash
# runs every module in all/ through lean, P at a time; one line per file in lauf.log
cd "$(dirname "$0")/all"
export PATH=$HOME/.elan/bin:$PATH
export LP=../../.lake/build/lib/lean
: > ../lauf.log
one() {
  f="$1"; start=$(date +%s)
  out=$(LEAN_PATH=$LP timeout 600 lean "$f" 2>&1)
  errs=$(echo "$out" | grep -cE "(^|: )error(:|\()")
  sorries=$(echo "$out" | grep -c "declaration uses .sorry.")
  { echo "== $f: errors $errs, sorry $sorries, secs $(( $(date +%s) - start ))"
    echo "$out" | grep -A3 -E "(^|: )error(:|\()" | head -12; } >> ../lauf.log
}
export -f one
ls *.lean | xargs -P "${P:-4}" -I{} bash -c 'one {}'
echo DONE >> ../lauf.log
