#!/usr/bin/env bash
# **R19: Commit-Nachrichten nur ueber Datei.**
#
# Der Backtick-Zwilling ist zweimal aufgetreten -- eine Nachricht mit `…`, $(…) oder einem
# fuehrenden # kam durch die Shell veraendert im Log an, und zweimal habe ich es erst nach
# dem Push gemerkt. Solange die Wahl zwischen Heredoc und -F besteht, bleibt es eine
# Aufmerksamkeitssache; also faellt die Wahl weg.
#
# Aufruf: Nachricht nach arbeitsprotokoll/.commitmsg schreiben, dann `./commit.sh`.
# `./commit.sh --sprechprobe` faehrt die Probe in beide Richtungen.
set -euo pipefail
W="$(cd "$(dirname "$0")" && pwd)"
MSG="$W/arbeitsprotokoll/.commitmsg"

if [ "${1:-}" = "--sprechprobe" ]; then
    # **`--hard` hat am 2026-08-16 uncommittete Arbeit vernichtet.** Die Probe legte einen
    # leeren Commit an und nahm ihn mit `git reset --hard HEAD~1` zurueck -- und riss dabei
    # eine ganze, noch nicht committete Umbauarbeit mit (acht `git mv`, alle Pfadanpassungen,
    # zwei aufgeraeumte Dokumente). Ueberlebt hat nur eine UNVERSIONIERTE Datei.
    #
    # Zwei Riegel statt eines, weil einer schon einmal nicht gereicht hat:
    #   1. die Probe laeuft nur auf sauberem Baum (wie `mutiere-pruefer.py`),
    #   2. sie nimmt den Commit mit `--soft` zurueck, nicht mit `--hard`.
    if ! git -C "$W" diff --quiet || ! git -C "$W" diff --cached --quiet; then
        echo "  R19-Sprechprobe: der Baum ist nicht sauber -- erst committen."
        echo "  (Diese Probe legt einen Commit an und nimmt ihn zurueck; auf schmutzigem"
        echo "   Baum hat genau das schon einmal Arbeit vernichtet.)"
        exit 2
    fi
    mkdir -p "$W/arbeitsprotokoll"
    cat > "$MSG" <<'PROBE'
Sprechprobe: `backticks`, $(kommando), fuehrendes Doppelkreuz
# diese Zeile ist Text, kein Kommentar
PROBE
    git -C "$W" commit -q --allow-empty -F "$MSG" --cleanup=verbatim
    if diff <(git -C "$W" log -1 --format=%B | head -c -1) "$MSG" > /dev/null; then
        echo "  Sonderzeichen: byteidentisch angekommen"
        ERG=0
    else
        echo "  Sonderzeichen: VERAENDERT -- R19 haelt nicht"
        diff <(git -C "$W" log -1 --format=%B) "$MSG" || true
        ERG=1
    fi
    git -C "$W" reset -q --soft HEAD~1
    git -C "$W" reset -q
    # **Die Gegenrichtung ist die GEFAHR, gegen die R19 steht**, nicht eine Git-Option:
    # dieselbe Nachricht INLINE durch die Shell. Genau das ist zweimal passiert.
    #
    # (Erste Fassung dieser Probe pruefte, ob `-F` ohne `--cleanup=verbatim` die #-Zeile
    #  streift. Tut es nicht -- `-F` benutzt den `whitespace`-Modus. Eine Gegenprobe, die
    #  eine falsche Annahme prueft, ist keine.)
    git -C "$W" reset -q --soft HEAD~1
    git -C "$W" reset -q
    ROH="$(cat "$MSG")"
    VERSTUEMMELT="$(eval "echo \"$ROH\"" 2>/dev/null || true)"
    if [ "$VERSTUEMMELT" = "$ROH" ]; then
        echo "  Gegenprobe:    UEBERSEHEN -- die Shell laesst die Sonderzeichen unveraendert?"
        ERG=1
    else
        echo "  Gegenprobe:    inline durch die Shell WIRD sie veraendert -- genau dagegen R19"
    fi
    echo "== R19: $([ $ERG = 0 ] && echo 'ALL PASS' || echo 'FEHLER') =="
    exit $ERG
fi

[ -s "$MSG" ] || { echo "R19: $MSG ist leer -- die Nachricht kommt aus der Datei."; exit 2; }
grep -q "Co-Authored-By" "$MSG" || printf '\nCo-Authored-By: Claude Opus 5 <noreply@anthropic.com>\n' >> "$MSG"
git -C "$W" commit -q -F "$MSG" --cleanup=verbatim
git -C "$W" log -1 --format='%h %s'
