#!/usr/bin/env bash
# instrumente/pruefe-nebenlaeufig-zwilling.sh -- a CONCURRENT driver, RUN, against
# a HANDWRITTEN C version of the same program (server lane, TODO section 0e,
# acceptance point 2).
#
# THE QUESTION. `pruefe-emission.sh` runs emitted C and compares it against
# hand-computed expectations. That answers "does the emitted C compute what we
# worked out on paper". This instrument asks the harder half: **does the emitted C
# of a CONCURRENT program compute what a C programmer writing the same program by
# hand computes** -- where "the same program" is read off the .gab source, not off
# the emitted file.
#
#   source            messung/proben/nebenlaeufig/sperre-rueckgabe.gab
#   emitted side      gabbro emit <source>
#   handwritten side  messung/proben/nebenlaeufig/sperre-rueckgabe-hand.c
#   one driver        messung/proben/nebenlaeufig/treiber.c  (over either side)
#
# The probe is a read under its lock, RETURNED, while a second thread writes the
# same carrier under the same lock. Both sides must answer 448 (64 reads, each
# seeing its own 7) after 193 lock acquisitions, at -O0 and at -O2, in every
# repetition.
#
# WHAT THIS FOUND, the first time it ran (2026-09-28). The emitted C answered
# **0** where the handwritten twin answered **448**: `return z;` inside
# `locks L { … }` was lowered as *release, then read* -- an unguarded read of a
# guarded carrier, in a program the checker accepts as race-free. The emitter now
# holds the value in a local before the releases (`emit.rs`, the `Return` arm);
# gift 1 below puts the old order back, and it must turn this run red.
#
# WHY THE OVERLAP WITNESS IS PART OF THE VERDICT. Two threads that never contend
# have run sequentially, and a sequential run of a concurrent program proves
# nothing about concurrency -- it is the same empty population as a guardian with
# no input (W17). The driver counts every acquisition that found the lock held;
# zero of them over every repetition is a RED, not a pass. Gift 3 is exactly that
# case: a handwritten twin that calls its two roots one after the other answers
# 448 too, and only the overlap witness catches it.
#
# Usage: instrumente/pruefe-nebenlaeufig-zwilling.sh [--gift N|all] [--runs R] [--keep]
set -u

# **`LC_ALL=C`** -- `cc` reports in the user's language otherwise, and the error
# text below is read, not only its exit code (the fifth requirement of
# `pruefe-waechter.py`; the specimen is in `pruefe-emission.sh`'s head).
export LC_ALL=C

# **Whoever leaves mid-run says WHERE** -- the shared form out of `abschnitt.sh`. Without it
# this instrument's own refusals would be the class it is built against: a run that ends
# before its last measurement and a return code that does not say so.
. "$(dirname "$0")/abschnitt.sh"
trap abschnitt_ende EXIT

W="$(cd "$(dirname "$0")/.." && pwd)"
GIFT=""
KEEP=0
LAEUFE=5
while [ $# -gt 0 ]; do
    case "$1" in
        --gift) shift; GIFT="$1" ;;
        --runs) shift; LAEUFE="$1" ;;
        --keep) KEEP=1 ;;
        *) echo "pruefe-nebenlaeufig-zwilling.sh: unknown argument '$1'" >&2; exit 2 ;;
    esac
    shift
done

# **The scratch directory and its trap stand HERE, before the first refusal.**
# `pruefe-waechter.py` counts every printing site that lies behind a guardian's
# first non-zero exit -- the surface a truncated run can swallow -- and a print
# behind the `EXIT` trap is covered, because the trap runs on every path out.
# Pulling these two lines to the top of the file is what takes this instrument's
# contribution to that ratchet to zero.
ARB="$(mktemp -d "${TMPDIR:-/tmp}/gabbro-zwilling.XXXXXX")"
if [ "$KEEP" = 0 ]; then
    trap 'abschnitt_ende; rm -rf "$ARB"' EXIT
fi

QUELLE="$W/messung/proben/nebenlaeufig/sperre-rueckgabe.gab"
HAND="$W/messung/proben/nebenlaeufig/sperre-rueckgabe-hand.c"
TREIBER="$W/messung/proben/nebenlaeufig/treiber.c"
FADEN="$ARB/faden_laufzeit.c"   # generated below (template `faden.laufzeit`, C-free lane)
# What the SOURCE says the answer is: K = 64 reads of the value 7 each, summed
# under the lock, and 64*2 + 64 + 1 = 193 acquisitions (the reader takes it twice
# per round, the writer once, and `lauf` once after the join).
ERWARTET="448 193"
# The busy-loop count of the driver's delay. It is large enough that two threads
# really overlap and that a read outside its section really loses the race; it
# creates neither of the two.
BREMSE=20000

nicht_gelaufen() {
    echo "NEBENLAEUFIG-ZWILLING: NOT RUN -- $1"
    echo "  A missing tool is not a passed test: this run measured NOTHING."
    exit 2
}

stufe_still "Kopf: Werkzeuge, Quellen und das gebaute Binaerprogramm"
command -v cc > /dev/null 2>&1 || nicht_gelaufen "no cc on this machine"
[ -f "$QUELLE" ]  || nicht_gelaufen "no probe source at $QUELLE"
[ -f "$HAND" ]    || nicht_gelaufen "no handwritten twin at $HAND"
[ -f "$TREIBER" ] || nicht_gelaufen "no driver at $TREIBER"
[ -f "$FADEN" ]   || nicht_gelaufen "no thread runtime at $FADEN"
[ "$(uname -m)" = x86_64 ] || nicht_gelaufen "the thread runtime is x86_64 (raw clone)"

# **Which binary, and is it newer than the sources?** One register, one file:
# `instrumente/binaer.sh` -- the trap it stands against bit this instrument first.
. "$(dirname "$0")/binaer.sh"
GABBRO="$(gabbro_binaer "$W")" || nicht_gelaufen "$GABBRO"
# **The thread runtime and the binding are generated, not copied** (C-free lane,
# 2026-09-30): `laufzeit/faden.c` and `bibliothek/linux/linux.c` are gone.
"$GABBRO" runtime threads > "$ARB/faden_laufzeit.c" || nicht_gelaufen "gabbro runtime threads failed"
"$GABBRO" emit "$W/bibliothek/linux/linux.gab" > "$ARB/linux_bind.c" || nicht_gelaufen "the binding does not emit"

# -- the mutations (`--gift`) --------------------------------------------------
#
# Each one must turn the run red, and no two of them are caught by the same
# check:
#
#   1 the EMITTED side goes back to the pre-2026-09-28 lowering: the release
#     moves in front of the read of the returned value. Caught by the compared
#     answer -- this is the defect the instrument was built for.
#   2 the HANDWRITTEN side sums twice the value. Caught by the compared answer,
#     and it is the direction that matters: it proves the twin carries the claim
#     instead of mirroring whatever the emitted side says.
#   3 the HANDWRITTEN side runs its two roots sequentially instead of as threads.
#     The answer is UNCHANGED (448) -- caught only by the overlap witness.
#   4 the EMITTED side drops the lock around the post-join read in `lauf`. The
#     answer is unchanged; the acquisition count is 192 instead of 193. Caught by
#     the counted lock discipline, which is why that count is in the compared
#     line at all.
gifte() { echo "1 2 3 4"; }

# Mutate the emitted C back to "release, then read" (gift 1). Everything else
# about the file stays as it is, so what is measured is the ORDER and nothing
# else.
gift1() {
    perl -0777 -pe 's/([A-Za-z_][A-Za-z_0-9 ]*) _rueck = (.*?);\n(\s*)([A-Za-z_0-9]+_gib\(\);)\n(\s*)return _rueck;/$4\n$5$1 _rueck = $2;\n$5return _rueck;/g' "$1"
}

baue() {   # $1 = arb, $2 = seite (emit|hand), $3 = opt, $4 = gift
    local arb="$1" seite="$2" opt="$3" gift="$4"
    local einheit="$arb/$seite.c"
    if [ "$seite" = emit ]; then
        "$GABBRO" emit "$QUELLE" > "$einheit" 2> "$arb/emit.err" || {
            echo "RED: gabbro emit failed"
            sed 's/^/    /' "$arb/emit.err"
            return 1
        }
        if [ "$gift" = 1 ]; then
            gift1 "$einheit" > "$einheit.gift" && mv "$einheit.gift" "$einheit"
            grep -q '_gib();' "$einheit" || { echo "RED: gift 1 changed nothing"; return 1; }
        fi
        if [ "$gift" = 4 ]; then
            # The post-join read in `lauf` loses its lock: one acquisition fewer.
            perl -0777 -i -pe 's/    L_nimm\(\);\n    \{\n        \{\n(\s*uint32_t _rueck = sicht_speicher[^\n]*\n)\s*L_gib\(\);\n(\s*return _rueck;\n)\s*\}\n    \}\n    L_gib\(\);/$1$2/' "$einheit"
        fi
    else
        cp "$HAND" "$einheit"
        if [ "$gift" = 2 ]; then
            sed -i 's/hand_sicht\[0\].wert + v;/hand_sicht[0].wert + 2 * v;/' "$einheit"
        fi
        if [ "$gift" = 3 ]; then
            # No threads at all: the roots run one after the other, so nothing
            # ever contends. The ANSWER does not move.
            #
            # **`perl -0777` and not `sed`** -- the call spans two lines in the
            # twin, and a line-based mutation silently changed nothing. The first
            # run of this gift reported NOT CAUGHT for exactly that reason, which
            # is a finding about the harness and not about the tree: *a mutation
            # that does not apply proves nothing, and it looks like a pass.*
            perl -0777 -i -pe 's/gabbro_faden_start\((leser|nullt),.*?\)\s*!= 0/($1(), 0) != 0/gs' "$einheit"
            # The two stacks are nobody's now, and `-Werror=unused-variable`
            # would end this gift at the COMPILER. *A mutation caught before the
            # run says nothing about the run* (the `@FADEN@` lesson of
            # `pruefe-emission.sh`), so the declarations are silenced and the
            # gift has to be caught where it belongs: at the overlap witness.
            perl -0777 -i -pe 's/(static unsigned char hand_stapel_\w+\[65536\])/$1 __attribute__((unused))/g' "$einheit"
            grep -q 'leser(), 0' "$einheit" || { echo "RED: gift 3 changed nothing"; return 1; }
        fi
    fi
    sed -e "s|@ERZEUGT@|$seite.c|" -e "s|@FADEN@|$FADEN|" "$TREIBER" > "$arb/$seite-treiber.c"
    # **The binding is a SECOND translation unit** (TODO section 0e K8):
    # `laufzeit/faden.c` calls `gabbro_os_klon` now, and
    # `bibliothek/linux/linux.c` sets `_POSIX_C_SOURCE` before any header --
    # which only works at the top of a unit of its own. *Measured: pasted into
    # this one it is a redefinition and `-Werror` ends the run.*
    if ! cc -std=c11 "-$opt" -Wall -Wextra -Werror "-DGABBRO_BREMSE=${BREMSE}u" \
            -I"$arb" -I"$W/laufzeit" -pthread -o "$arb/$seite-$opt" \
            "$arb/$seite-treiber.c" "$ARB/linux_bind.c" 2> "$arb/cc.err"; then
        echo "RED: $seite at -$opt did not compile"
        head -12 "$arb/cc.err" | sed 's/^/    /'
        return 1
    fi
    return 0
}

# -- one verdict over one configuration ---------------------------------------
beurteile() {   # $1 = arb, $2 = gift ; prints findings and a FEHLER= line
    local arb="$1" gift="$2" fehler=0 seite opt i
    local zeilen=0
    for seite in emit hand; do
        for opt in O0 O2; do
            if ! baue "$arb" "$seite" "$opt" "$gift"; then
                fehler=$((fehler+1))
                continue
            fi
            local ueberlappt=0
            for i in $(seq 1 "$LAEUFE"); do
                local aus rc=0
                aus="$(timeout 60 "$arb/$seite-$opt" 2>&1)" || rc=$?
                if [ "$rc" != 0 ]; then
                    echo "RED: $seite at -$opt, run $i did not finish (rc $rc)"
                    fehler=$((fehler+1))
                    continue
                fi
                local erste zweite
                erste="$(printf '%s\n' "$aus" | sed -n 1p)"
                zweite="$(printf '%s\n' "$aus" | sed -n 2p)"
                zeilen=$((zeilen+1))
                echo "LINE $seite -$opt $i: $erste | $zweite"
                if [ "$erste" != "$ERWARTET" ]; then
                    echo "RED: $seite at -$opt, run $i answered '$erste', the source says '$ERWARTET'"
                    fehler=$((fehler+1))
                fi
                case "$zweite" in
                    "overlap 0") ;;
                    overlap*) ueberlappt=$((ueberlappt+1)) ;;
                    *) echo "RED: $seite at -$opt, run $i printed no overlap line"; fehler=$((fehler+1)) ;;
                esac
            done
            if [ "$ueberlappt" = 0 ]; then
                echo "RED: $seite at -$opt never contended in $LAEUFE runs -- a sequential"
                echo "     run of a concurrent program measures nothing about concurrency"
                fehler=$((fehler+1))
            else
                echo "OVERLAP $seite -$opt: $ueberlappt of $LAEUFE runs contended"
            fi
        done
    done
    echo "ZEILEN=$zeilen"
    echo "FEHLER=$fehler"
}

if [ -z "$GIFT" ]; then
    stufe "the emitted C of a concurrent program against a HANDWRITTEN C twin"
    echo "   source        $QUELLE"
    echo "   twin          $HAND"
    echo "   driver        $TREIBER (delay $BREMSE, thread runtime laufzeit/faden.c)"
    echo "   the source's answer: $ERWARTET (sum of 64 guarded reads, lock acquisitions)"
    ergebnis="$(beurteile "$ARB" "")"
    printf '%s\n' "$ergebnis" | grep -E '^(LINE|OVERLAP)' | sed 's/^/   /'
    printf '%s\n' "$ergebnis" | grep '^RED' || true
    n="$(printf '%s\n' "$ergebnis" | sed -n 's/^FEHLER=//p')"
    z="$(printf '%s\n' "$ergebnis" | sed -n 's/^ZEILEN=//p')"
    echo
    if [ "$n" = 0 ] && [ "$z" -gt 0 ]; then
        echo "GREEN: emitted and handwritten agree on $z of $z runs (2 sides x 2 optimisation"
        echo "       levels x $LAEUFE repetitions), both answered what the source says, and both"
        echo "       were observed to contend."
        abschnitt_fertig
        exit 0
    fi
    [ "$z" -gt 0 ] || echo "RED: not one run produced a line -- an empty population is no verdict"
    echo "RED: $n finding(s) over $z run line(s)."
    abschnitt_fertig
    exit 1
fi

# -- the poison runs (the Sprechprobe of this instrument) ----------------------
stufe_still "Sprechprobe: die Giftlaeufe"
if [ "$GIFT" = all ]; then
    LISTE="$(gifte)"
else
    LISTE="$GIFT"
fi
gefangen=0
gesamt=0
for g in $LISTE; do
    gesamt=$((gesamt+1))
    arb="$ARB/g$g"
    mkdir -p "$arb"
    ergebnis="$(beurteile "$arb" "$g")"
    n="$(printf '%s\n' "$ergebnis" | sed -n 's/^FEHLER=//p')"
    if [ "$n" = 0 ]; then
        echo "GIFT $g: NOT CAUGHT -- the instrument stayed green under the mutation"
        printf '%s\n' "$ergebnis" | grep -E '^(LINE|OVERLAP)' | head -4 | sed 's/^/    /'
    else
        echo "GIFT $g: caught ($n finding(s))"
        printf '%s\n' "$ergebnis" | grep '^RED' | head -3 | sed 's/^/    /'
        gefangen=$((gefangen+1))
    fi
done
echo
echo "gifts: $gefangen of $gesamt caught"
abschnitt_fertig
[ "$gefangen" = "$gesamt" ] || exit 1
exit 0
