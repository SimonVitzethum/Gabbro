#!/bin/bash
# Single-module checks (owner rule 2026-11-02): the modules changed since BASE plus every module that
# imports them, one `lake build <Module>` at a time in dependency order, in the single-module scope.
# Usage: einzeln.sh BASE [--no-importers]   (run from anywhere; works in ../grammatik)
# Parser probe modules (Grammatik.Parser.*Proben*) are skipped: they are checked only in the round's integration build.
cd "$(dirname "$0")/../grammatik"
BASE=$1; MODE=$2
python3 - "$BASE" "$MODE" > ../.scratch-einzeln.order <<'PY'
import sys, subprocess, re, os
base, mode = sys.argv[1], sys.argv[2]
changed = subprocess.run(["git","diff","--name-only",base,"--","."],capture_output=True,text=True).stdout.split()
changed = {c[len("grammatik/"):] if c.startswith("grammatik/") else c for c in changed}
mods = {}
for root,_,fs in os.walk("Grammatik"):
    for f in fs:
        if f.endswith(".lean"):
            p=os.path.join(root,f); m=p[:-5].replace("/",".")
            imps=[]
            for line in open(p,encoding="utf-8"):
                mm=re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(Grammatik\S*)",line)
                if mm: imps.append(mm.group(1))
            mods[m]=imps
seed={c[:-5].replace("/",".") for c in changed if c.endswith(".lean") and c.startswith("Grammatik/")}
seed&=set(mods)
rev={m:[] for m in mods}
for m,imps in mods.items():
    for i in imps:
        if i in rev: rev[i].append(m)
todo=set(seed)
if mode!="--no-importers":
    stack=list(seed)
    while stack:
        x=stack.pop()
        for y in rev[x]:
            if y not in todo: todo.add(y); stack.append(y)
order=[];seen=set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in mods.get(m,[]):
        if i in todo: visit(i)
    order.append(m)
for m in sorted(todo): visit(m)
def olean(m): return ".lake/build/lib/lean/"+m.replace(".","/")+".olean"
def src(m): return m.replace(".","/")+".lean"
dirty=set()
for m in order:
    o=olean(m)
    if not os.path.exists(o) or os.path.getmtime(src(m))>os.path.getmtime(o) or any(i in dirty for i in mods[m]) \
       or any(os.path.exists(olean(i)) and os.path.getmtime(olean(i))>os.path.getmtime(o) for i in mods[m]):
        dirty.add(m)
for m in order:
    if m in dirty and not ("Proben" in m and m.startswith("Grammatik.Parser")) and m != "Grammatik": print(m+"\t"+" ".join(mods[m]))
PY
N=$(wc -l < ../.scratch-einzeln.order); echo "modules: $N"
L=/home/simon/.cache/gabbro-stage0-build.slot
i=0; failed=" "; nf=0
while IFS=$'\t' read -r M IMPS; do
  i=$((i+1)); [ $((i % 50)) -eq 0 ] && echo "[$i/$N] $M"
  skip=""; for x in $IMPS; do case "$failed" in *" $x "*) skip=$x;; esac; done
  if [ -n "$skip" ]; then failed="$failed$M "; continue; fi
  out=$(flock $L-1.lock env -u ELAN_TOOLCHAIN systemd-run --user --scope -q -p AllowedCPUs=0-11 -p CPUQuota=400% -p MemoryMax=5G -p MemoryHigh=4G -p MemorySwapMax=0 env LEAN_NUM_THREADS=4 lake build "$M" 2>&1); rc=$?
  if [ $rc -ne 0 ] || echo "$out" | grep -q "^error"; then
    nf=$((nf+1)); failed="$failed$M "
    echo "FAIL [$i/$N] $M"; echo "$out" | grep "^error" | grep -v "build failed" | cut -c1-240 | head -8
  fi
done < ../.scratch-einzeln.order
echo "DONE $N modules, $nf failed (dependents skipped)"
