#!/bin/bash
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH
LP=../.lake/build/lib/lean
for f in "$@"; do
  out=$(LEAN_PATH=$LP timeout 150 lean "$f" 2>&1)
  errs=$(echo "$out" | grep -c "error:")
  sorries=$(echo "$out" | grep -c "declaration uses .sorry.")
  echo "== $f: errors $errs, sorry $sorries"
  echo "$out" | grep -A4 "error:" | head -${MAXL:-40}
done
