#!/bin/bash
# **Is the reachability wall of Gate 2 the SOLVER, or is it the ENCODING?**
#
# `messung/GABBROV-AUFTRAG.md` §2.5 measured `L05` through Z3 at growing unrolling depths
# and found the answers stop non-monotonically: bounds 2-19, 21, 24, 32 and 48 answer in
# under 0.4 s, while **20, 22 and 64 time out at 60 s**. The report's own conclusion is that
# a solver answering at 21 and not at 20 gives no bound to plan with.
#
# This script asks the next question, and it has two halves that answer it twice over.
#
#   PART 1 -- the SAME file, the SAME bound, a different `random_seed`. If the wall moves
#             when only the seed moves, it is not a wall: it is a coin.
#   PART 2 -- the same OBLIGATION without any unrolling at all. `cdt_wohlgeformt` has a
#             bound-free characterisation as a RANK, and the negated goal needs no depth
#             either -- see `gen-rank.py`, which carries the argument.
#
# Two controls, because either part alone is satisfiable by accident:
#   A -- the rank file with `s = WURZEL` must say `unsat`. Without it a `sat` proves nothing.
#   B -- the PREMISE alone must be satisfiable. An unsatisfiable premise makes every
#        verification condition `unsat` and every obligation `passed`, which is `GABBROV.md`
#        §5's vacuity one level down.
#
#     ./messung/gabbrov/ohne-schranke/lauf.sh
#
# **`LC_ALL=C`, and it is not decoration** -- the same reason `lauf-L05.sh` carries it: a
# decimal comma is not a number to `printf`, and a script that prints `0.000s` beside real
# answers is a measuring instrument reporting a constant.
set -u
export LC_ALL=C

W="$(cd "$(dirname "$0")/../../.." && pwd)"
S="$(cd "$(dirname "$0")" && pwd)"
Z="${Z3:-/opt/verus/z3}"

if [ ! -x "$Z" ]; then
    echo "ABBRUCH: no z3 at \`$Z\` -- set \$Z3. NOTHING was measured."
    exit 2
fi
if [ ! -f "$W/messung/gabbrov/erzeuge-L05.py" ]; then
    echo "ABBRUCH: \`erzeuge-L05.py\` not found -- part 1 needs the ORIGINAL encoding to"
    echo "  vary the seed of. NOTHING was measured."
    exit 2
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "== $("$Z" --version) =="
echo
echo "PART 1 -- the same bound under different solver seeds"
echo "  (seed 0 is the default, i.e. what \`lauf-L05.sh\` measured)"
for k in 20 22; do
    for seed in 0 1 2 7; do
        f="$TMP/L05-$k-$seed.smt2"
        python3 "$W/messung/gabbrov/erzeuge-L05.py" "$k" > "$f" || exit 2
        sed -i "2i (set-option :smt.random_seed $seed)\n(set-option :sat.random_seed $seed)" "$f"
        t0=$(date +%s.%N)
        ans=$("$Z" -memory:4096 "$f" 2>&1 | head -1)
        t1=$(date +%s.%N)
        printf "  bound=%-3s seed=%-3s answer=%-9s time=%6.2fs\n" \
               "$k" "$seed" "$ans" "$(echo "$t1 - $t0" | bc)"
    done
done

echo
echo "PART 2 -- the same obligation with NO unrolling, at the bounds that died"
echo "  and at the number the corpus actually asks for (F01.gab:56, NSLOTS = 80256)"
for N in 20 22 64 4096 80256; do
    f="$TMP/rank-$N.smt2"
    python3 "$S/gen-rank.py" "$N" > "$f" || exit 2
    sz=$(wc -c < "$f")
    t0=$(date +%s.%N)
    ans=$("$Z" -memory:4096 "$f" 2>&1 | head -1)
    t1=$(date +%s.%N)
    printf "  N=%-8s bytes=%-6s answer=%-8s time=%6.3fs\n" \
           "$N" "$sz" "$ans" "$(echo "$t1 - $t0" | bc)"
done

echo
echo "CONTROL A -- the same file with s = WURZEL. It MUST say \`unsat\`."
for N in 20 80256; do
    f="$TMP/rankw-$N.smt2"
    python3 "$S/gen-rank.py" "$N" --wurzel > "$f" || exit 2
    t0=$(date +%s.%N); ans=$("$Z" -memory:4096 "$f" 2>&1 | head -1); t1=$(date +%s.%N)
    printf "  N=%-8s answer=%-8s time=%6.3fs\n" "$N" "$ans" "$(echo "$t1 - $t0" | bc)"
done

echo
echo "CONTROL B -- is the PREMISE alone satisfiable? An \`unsat\` premise passes everything."
for N in 20 80256; do
    f="$TMP/probe-$N.smt2"
    python3 "$S/gen-probe.py" "$N" > "$f" || exit 2
    t0=$(date +%s.%N); ans=$("$Z" -memory:4096 "$f" 2>&1 | head -1); t1=$(date +%s.%N)
    printf "  N=%-8s answer=%-8s time=%6.3fs\n" "$N" "$ans" "$(echo "$t1 - $t0" | bc)"
done

echo
echo "  (60 s is the file's own timeout. \`unknown\` at that mark is a TIMEOUT and is"
echo "   UNDECIDED -- never a negative answer.)"
