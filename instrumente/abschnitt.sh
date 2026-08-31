# **Whoever leaves mid-run says WHERE** -- the shell half of `instrumente/abschnitt.py`.
#
# `messung/RUECKLAUFWERTE.md` measured the class the empty tree cannot reach: a precondition
# that breaks MID-RUN. 251 exit sites lie behind a first one; 92 of them leave a partial
# measurement that looks like a whole one. **`pruefe-emission.sh` died on 2026-08-31 in the
# fourth of ten stages with `exit 1`; stages 9 and 10 never ran, and not one line said so.**
#
# > *An empty population is a green judgement over nothing (W17). A TRUNCATED one looks like
# > a judgement over everything.*
#
# USAGE -- three edits, and none of them per stage body:
#
#     . "$(dirname "$0")/abschnitt.sh"
#     trap 'abschnitt_ende; rm -rf "$TMP"' EXIT      # BEFORE the cleanup, and first
#     stufe "Stufe 9: jede Datei uebersetzt"          # instead of `echo "== … =="`
#     ...
#     abschnitt_fertig                                # before the last, complete exit
#
# **Why `stufe` and not a capture of the output**, as the Python half does: a shell cannot
# tee its own stdout and still be sure the tee has flushed when the `EXIT` trap runs. *A
# mechanism that sometimes reports the wrong stage is worse than none* -- it would be the
# same class as the thing it is built against. So the shell says it outright.
#
# **`abschnitt_ende` must run FIRST in the trap**, because it reads `$?`.

LETZTE_STUFE="Kopf (vor dem ersten Abschnitt)"
GANZ_DURCH=0

# Print a section heading AND remember it. Same output as the `echo` it replaces.
stufe() {
    LETZTE_STUFE="$1"
    echo "== $1 =="
}

# Remember a heading without printing it -- for a stage whose own header is composed.
stufe_still() {
    LETZTE_STUFE="$1"
}

# **From here on nothing more is measured.** Before the last, complete exit.
abschnitt_fertig() {
    GANZ_DURCH=1
}

abschnitt_ende() {
    local rc=$?
    if [ "$rc" != 0 ] && [ "$GANZ_DURCH" = 0 ]; then
        echo
        echo "== ABGESCHNITTEN in: $LETZTE_STUFE -- Ruecklaufwert $rc =="
        echo "   Was DAHINTER steht, wurde NICHT gemessen -- weder ja noch nein. Dieser Lauf"
        echo "   endete VOR seiner letzten Messung, und sein Ruecklaufwert sagt das nicht:"
        echo "   eine \`1\` liest sich als Befund und ist hier zugleich ein Abbruch fuer alles"
        echo "   dahinter. **Eine halbe Messung sieht aus wie eine ganze.**"
        echo "   messung/RUECKLAUFWERTE.md, Abschnitt *Der Schnitt mitten im Lauf*."
    fi
    return $rc
}
