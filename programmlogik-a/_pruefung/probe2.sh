#!/bin/bash
# probe2.sh <module.lean> '<extra tactic>' -- gabbro_pipeline, then the extra tactic, then trace
f="$1"; extra="$2"
cd "$(dirname "$0")/all"
python3 - "$f" "$extra" > ../probe2.lean <<'PY'
import sys,re
f,extra=sys.argv[1],sys.argv[2]
s=open(f).read()
def rep(m):
    return "gabbro_pipeline [%s] using %s\n  %s\n  trace_state\n  all_goals sorry" % (m.group(1), m.group(2), extra)
s=re.sub(r'gabbro_auto \[(.*)\] using (\w+)', rep, s)
sys.stdout.write(s)
PY
LEAN_PATH=../../.lake/build/lib/lean timeout 600 ~/.elan/bin/lean ../probe2.lean 2>&1 | grep -v "linter\|Hint\|\[apply\]\|not explicitly referenced\|^$"
