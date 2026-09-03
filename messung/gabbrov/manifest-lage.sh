#!/bin/bash
# **Does the manifest exist for the ten fragments the 66 obligations were counted from?**
#
# `dokumente/GABBROV.md` §2 rests the whole design on one sentence: *"GabbroV does not read
# the Gabbro program. It reads the manifest."* This script asks what the manifest actually
# holds for `messung/fragmente/F01..F10`, which is the corpus `PFLICHTEN.md` counts.
#
# It exists because `messung/GABBROV-AUFTRAG.md` §4 asks for the obligation TEXT in the
# manifest line, and a richer format over an absent register is a better-labelled emptiness.
# *The population is the prior question, and nobody had asked it.*
#
#     ./messung/gabbrov/manifest-lage.sh
#
# The counterpart figure comes from `./instrumente/zaehle-pflichten.py --gabbrov`, and the
# two are printed side by side on purpose: a gap between them is the finding.
set -u
export LC_ALL=C

W="$(cd "$(dirname "$0")/../.." && pwd)"
G="${GABBRO:-$W/target/debug/gabbro}"

if [ ! -x "$G" ]; then
    echo "ABBRUCH: no gabbro at \`$G\` -- build it first, or set \$GABBRO."
    echo "  NOTHING was measured; this is not a report that the manifest is empty."
    exit 2
fi
FRAGMENTS=("$W"/messung/fragmente/F*.gab)
if [ ! -e "${FRAGMENTS[0]}" ]; then
    echo "ABBRUCH: no fragment under \`messung/fragmente/F*.gab\`. NOTHING was measured."
    exit 2
fi

# **The version gate -- and it stands BEFORE anything is counted** (2026-09-03).
#
# `pflichten.rs::MANIFESTFASSUNG` writes `-- manifest-version N` on line one. A reader that
# does not look at it does not fail on a newer format; it MISREADS one, and here that would
# look like a manifest that simply holds fewer lines. *That is the finding this script exists
# to report, so it is exactly the value it must not be able to fake.*
FASSUNGEN_BEKANNT="1"

echo "== \`gabbro pflichten\` over the ten fragments =="
tot=0
ohne=0
for f in "${FRAGMENTS[@]}"; do
    n=$(basename "$f")
    out=$("$G" pflichten "$f" 2>&1)
    fassung=$(echo "$out" | sed -n 's/^-- manifest-version \([0-9][0-9]*\)$/\1/p' | head -1)
    if [ -n "$fassung" ] && ! echo " $FASSUNGEN_BEKANNT " | grep -q " $fassung "; then
        echo "ABBRUCH: \`$n\` carries manifest version $fassung; this reader knows"
        echo "  $FASSUNGEN_BEKANNT. NOTHING was measured -- a reader that guesses at an unknown"
        echo "  format reports a number, and a number from a misread format is worse than none."
        exit 2
    fi
    if echo "$out" | grep -q 'no register'; then
        errs=$(echo "$out" | grep -c '^error:')
        ohne=$((ohne + 1))
        printf "  %-8s NO REGISTER   %2d checker error(s)\n" "$n" "$errs"
    else
        c=$(echo "$out" | grep -oE '^== [0-9]+ obligations' | grep -oE '[0-9]+' | head -1)
        tot=$((tot + ${c:-0}))
        printf "  %-8s register      %2s obligation(s)\n" "$n" "${c:-0}"
    fi
done
echo "  ------------------------------------------------------"
printf "  fragments with NO manifest at all              %2d of %d\n" "$ohne" "${#FRAGMENTS[@]}"
printf "  obligation lines reaching a manifest           %2d\n" "$tot"
echo -n "  GabbroV's obligation population               "
"$W/instrumente/zaehle-pflichten.py" --gabbrov 2>/dev/null \
    | grep -oE 'GabbroV obligation population +[0-9]+' | grep -oE '[0-9]+$' \
    || echo "?"
echo
echo "  A fragment with a standing checker error emits NO register, so its obligations are"
echo "  unreachable by the tool \`GABBROV.md\` §2 describes. \`messung/fragmente/README.md\`"
echo "  books the standing errors as the corpus's YIELD -- that is deliberate. What is not"
echo "  written anywhere is what it costs the manifest."
