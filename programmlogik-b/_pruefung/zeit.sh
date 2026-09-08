#!/bin/bash
# zeit.sh <module.lean> -- per-pipeline-step milliseconds, summed over the file's theorems
f="$1"
cd "$(dirname "$0")/all"
sed 's/gabbro_auto \[/gabbro_pipeline_b [/; s/\] using shapeOf$/] using shapeOf <;> sorry/' "$f" > ../zeit.lean
LEAN_PATH=../../.lake/build/lib/lean timeout 900 ~/.elan/bin/lean ../zeit.lean 2>&1 \
  | grep -o 'GTIME s[0-9]* [0-9]*' \
  | awk '{s[$2]+=$3; c[$2]++} END{for(k in s) printf "%s %8d ms %4d\n", k, s[k], c[k]}' | sort
