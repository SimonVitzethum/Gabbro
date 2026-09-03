#!/bin/bash
# Drive `L05` through Z3 at growing bounds and print answer + wall time.
#
#     ./messung/gabbrov/lauf-L05.sh 2 4 8 16 20 21 22 24 32 48 64
#     ./messung/gabbrov/lauf-L05.sh --frisch 2 4 8 12
#
# `--frisch` adds the one premise that repairs the obligation (`s = WURZEL`), and the point
# of that run is that the premise contradicts what `unlink` is for.
#
# **`LC_ALL=C`, and it is not decoration.** A decimal comma is not a number to `printf`, and
# the pinned-locale requirement `pruefe-waechter.py` puts on every guardian applies to a
# measuring script just as much: the first version of this file printed
# `Invalid number` for every row and reported `0.000s` beside real answers.
set -u
export LC_ALL=C

W="$(cd "$(dirname "$0")/../.." && pwd)"
Z="${Z3:-/opt/verus/z3}"

if [ ! -x "$Z" ]; then
    echo "ABBRUCH: no z3 at \`$Z\` -- set \$Z3. NOTHING was measured."
    exit 2
fi

FLAG=""
if [ "${1:-}" = "--frisch" ]; then FLAG="--mit-frischer-wurzel"; shift; fi
if [ $# -eq 0 ]; then
    echo "ABBRUCH: no bound given -- NOTHING was measured."
    exit 2
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "== L05 through $("$Z" --version) =="
for k in "$@"; do
    f="$TMP/L05-$k.smt2"
    python3 "$W/messung/gabbrov/erzeuge-L05.py" "$k" $FLAG > "$f" || exit 2
    sz=$(wc -c < "$f")
    t0=$(date +%s.%N)
    ans=$("$Z" "$f" 2>&1 | head -1)
    t1=$(date +%s.%N)
    printf "  bound=%-5s bytes=%-9s answer=%-8s time=%6.2fs\n" \
           "$k" "$sz" "$ans" "$(echo "$t1 - $t0" | bc)"
done
echo "  (the file's own timeout is 60 s; \`unknown\` at that mark is a timeout and is"
echo "   reported as one -- it is UNDECIDED and not a negative answer.)"
