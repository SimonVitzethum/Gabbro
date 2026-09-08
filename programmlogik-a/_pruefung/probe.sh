#!/bin/bash
# probe.sh <module.lean> [theorem] -- shows what gabbro_auto leaves (gabbro_auto?)
f="$1"; th="${2:-}"
cd "$(dirname "$0")/all"
if [ -n "$th" ]; then
  awk -v th="$th" '/^theorem /{cur=$2} { if (cur==th) sub(/gabbro_auto \[/, "gabbro_auto? ["); print }' "$f" > ../probe.lean
else
  sed 's/gabbro_auto \[/gabbro_auto? [/' "$f" > ../probe.lean
fi
LEAN_PATH=../../.lake/build/lib/lean timeout 300 ~/.elan/bin/lean ../probe.lean 2>&1 | grep -v "linter\|Hint\|\[apply\]\|not explicitly referenced\|^$"
