#!/bin/bash
# Every OWED unit's template must compile to GOALS, not to an error (GabbroV lane, 2026-09-29).
#
# `gabbro prove --template` writes the file a person starts from. A template that does not parse or
# does not elaborate sends the person to fix the generator's file instead of writing their own
# argument -- found when the second pass of `gabbro_auto2` was written at the wrong column for a
# split (`55`): Lean answered `unexpected identifier; expected command`.
#
# For each unit named on the command line (default: the corpus files `gabbro prove` calls OWED):
# `gabbro prove` (which builds the Duty file), then the template through Lean with the person's
# `sorry` in place. The only permitted message is `declaration uses 'sorry'`; any `error` fails.
# Counts, never stops at the first failure.
cd "$(dirname "$0")/.." || exit 2
G=${GABBRO:-target/release/gabbro}
[ -x "$G" ] || { echo "no $G -- cargo build --release first"; exit 2; }
free -g | sed -n 2p
export PATH="$HOME/.elan/bin:$PATH"
if [ $# -gt 0 ]; then units=("$@"); else
  units=()
  for f in beispiele/*.gab messung/fragmente/*.gab messung/caprock/*.gab messung/proben/probe-*.gab; do
    "$G" prove "$f" 2>&1 | grep -q '^ *OWED' && units+=("$f")
  done
fi
W=.claude/muse-arbeit/kratz/vorlagen; mkdir -p "$W"
rot=0; n=0
for f in "${units[@]}"; do
  n=$((n+1)); name=$(basename "$f" .gab)
  "$G" prove "$f" >/dev/null 2>&1
  "$G" prove --template "$f" 2>/dev/null > "$W/$name.lean"
  # the poison probe: `VORLAGE_GIFT=1` indents the lines after the pipeline one step too far --
  # the very defect this instrument was written for -- and the run must then FAIL
  if [ -n "$VORLAGE_GIFT" ]; then sed -i 's/^  all_goals (try (gabbro_pipeline/    all_goals (try (gabbro_pipeline/' "$W/$name.lean"; fi
  aus=$(cd programmlogik && LEAN_PATH=$PWD/.lake/build/lib/lean:$PWD/.lake/build/duty lean "$OLDPWD/$W/$name.lean" 2>&1)
  if echo "$aus" | grep -q 'error'; then
    echo "  FAIL $f"; echo "$aus" | grep 'error' | head -3 | cut -c1-200; rot=$((rot+1))
  else echo "  ok   $f"; fi
done
echo "templates checked: $n, with an error: $rot"
[ "$rot" = 0 ]
