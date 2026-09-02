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
    # **KEIN zweiter Reset hier.** Die Gegenprobe unten legt keinen Commit an -- sie
    # prueft, was die SHELL mit der Nachricht macht. Meine erste Fassung setzte trotzdem
    # einen Reset und schob HEAD einen Commit ZU WEIT zurueck; der Baum sah danach aus, als
    # waere die Aufraeumarbeit geloescht (sie war es nicht -- der Commit lag im Objektspeicher,
    # nur HEAD stand falsch).
    #
    # *Zweimal derselbe Fehler in derselben Datei am selben Tag: ein Werkzeug, das HEAD
    # bewegt, wird nach jeder Aenderung gefahren, nicht nur gelesen.*
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

# **Der Riegel gegen den gefressenen Merge** (2026-09-01, zweimal an EINEM Abend).
#
# `git stash` in einem offenen Merge nimmt die Dateien mit und laesst `MERGE_HEAD` fallen.
# `git stash pop` bringt die Dateien zurueck -- den zweiten Elternteil nicht. Der Baum sieht
# unveraendert aus, und der naechste Commit ist ein gewoehnlicher, mit der ganzen
# Zweighistorie verloren.
#
# **Beide Male wusste ich die Regel und habe sie trotzdem gebrochen** -- einmal um Anker
# gegen `master` zu messen, einmal um zu pruefen, ob ein Waechter vorher rot war. *Eine
# Regel im Kopf ist ein Diktat; eine Regel im Werkzeug ist eine Struktur.*
#
# Der Riegel prueft das EINZIGE Merkmal, das beide Faelle teilen und das kein normaler
# Commit hat: eine Nachricht, die mit `merge:` beginnt, ohne dass ein Merge laeuft.
#
# **And the path is ASKED for, not assembled** (2026-09-02). It read `$W/.git/MERGE_HEAD`,
# and in a LINKED WORKTREE `.git` is a FILE (`gitdir: …/.git/worktrees/<name>`), so that
# path never exists -- the bar fired on every `merge:` message an agent ever wrote and
# refused a merge that was open and correct. *It erred in the safe direction, which is
# exactly why it could stand there unnoticed:* a guard that always says no looks like a
# guard that works. CLAUDE.md puts every agent in a worktree, so this was the ordinary case
# and not the exotic one.
GITDIR="$(git -C "$W" rev-parse --git-dir)"
if head -1 "$MSG" | grep -q '^merge:' && [ ! -f "$GITDIR/MERGE_HEAD" ]; then
    echo "ABBRUCH: die Nachricht beginnt mit \`merge:\`, aber \`MERGE_HEAD\` fehlt."
    echo "  Dieser Commit haette EINEN Elternteil -- der Zweig waere nicht zusammengefuehrt,"
    echo "  sondern seine Aenderungen als eigene Arbeit eingetragen."
    echo "  Ursache in beiden bisherigen Faellen: \`git stash\` im offenen Merge."
    echo "  Heilung: \`git reset --hard HEAD && git merge --no-ff --no-commit <zweig>\`,"
    echo "  dann die Konfliktloesung neu -- der Zweig traegt alles."
    exit 2
fi
grep -q "Co-Authored-By" "$MSG" || printf '\nCo-Authored-By: Claude Opus 5 <noreply@anthropic.com>\n' >> "$MSG"
git -C "$W" commit -q -F "$MSG" --cleanup=verbatim
git -C "$W" log -1 --format='%h %s'
