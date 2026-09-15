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
# **Der Lean-Riegel: es wird nur committet, was Lean gerade durchgebaut hat.**
#
# *Gesetzt am 2026-09-15 auf Wunsch des Ordners.* Ein Merge, der einzeln gruen war und im
# Zusammentreffen bricht, ist an EINEM Tag zweimal vorgekommen (die Gerätezeilen gegen den
# Kongruenzbeweis; der Exporter gegen die erzeugten Pflichtdateien). Beide Male hat es NUR
# der Bau gezeigt -- der Diff sah sauber aus, die Konfliktmarken standen in Dokumenten.
# *Eine Regel im Kopf ist ein Diktat; eine Regel im Werkzeug ist eine Struktur.*
#
# Der Riegel laeuft in ALLEN DREI Umgebungen, in denen dieses Skript benutzt wird, und er
# sucht sich die passende selbst:
#   1. Klon einer Bahn  -> `./lean-bau` (die Warteschlange; die Bahn darf `lake` nicht rufen)
#   2. auf `fisch`      -> `lake build` in `grammatik/`, ueber `lean-slot` wenn vorhanden
#   3. Orchestrator     -> `grammatik/` per rsync auf `fisch` und dort bauen
#
# **Wo KEINE der drei geht, ist das kein gruener Bau, sondern gar keiner** -- dann bricht
# der Commit ab und nennt den Befehl, der fehlt. Der Ausweg ist benannt und hinterlaesst
# eine Spur: `GABBRO_OHNE_LEAN="<Grund>" ./commit.sh` traegt den Grund als Zeile in die
# Nachricht ein. *Ein Ausgang, der im Diff verschwindet, waere die Luecke, gegen die der
# Riegel steht; einer, der sich selbst aufschreibt, ist einer.*
lean_riegel() {
    if [ -n "${GABBRO_OHNE_LEAN:-}" ]; then
        echo "  Lean-Riegel UMGANGEN: $GABBRO_OHNE_LEAN"
        printf '\nLean-Bau: NICHT gefahren -- %s\n' "$GABBRO_OHNE_LEAN" >> "$MSG"
        return 0
    fi
    if [ -x "$W/lean-bau" ]; then
        AUS="$(cd "$W" && ./lean-bau 2>&1)"
        echo "$AUS" | grep -q "Build completed successfully" && return 0
        echo "$AUS" | tail -12; return 1
    fi
    if command -v lake >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/lake" ]; then
        LAKE="$(command -v lake || echo "$HOME/.elan/bin/lake")"
        SLOT="$HOME/gabbro-muse/bin/lean-slot"
        if [ -x "$SLOT" ]; then AUS="$("$SLOT" bash -c "cd '$W/grammatik' && '$LAKE' build 2>&1")"
        else AUS="$(cd "$W/grammatik" && "$LAKE" build 2>&1)"; fi
        echo "$AUS" | grep -q "Build completed successfully" && return 0
        echo "$AUS" | grep -E "error" | head -8; return 1
    fi
    H=ki-pc-fisch-101
    ssh -o BatchMode=yes -o ConnectTimeout=20 "$H" true 2>/dev/null || {
        echo "  weder ./lean-bau noch lake hier, und $H antwortet nicht"; return 2; }
    rsync -rlpgoD --delete --exclude '.lake/' "$W/grammatik/" "$H:gabbro-muse/merge-bau/grammatik/" >/dev/null || return 2
    AUS="$(ssh -o BatchMode=yes "$H" 'cd ~/gabbro-muse/merge-bau/grammatik && ~/gabbro-muse/bin/lean-slot bash -c "timeout 3000 ~/.elan/bin/lake build 2>&1" | grep -E "error|Build completed" | tail -6')"
    echo "$AUS" | grep -q "Build completed successfully" && return 0
    echo "$AUS"; return 1
}
# **`set -e` ist hier eine Falle, und zwar meine eigene gewesen:** ein Funktionsaufruf in
# gewoehnlicher Position bricht das Skript bei Rueckgabe != 0 ab, BEVOR der Wert gelesen
# wird -- der Riegel haette dann statt seiner Meldung nur einen stummen Ausgang erzeugt.
# In einer `if`-Bedingung ist `set -e` ausgesetzt; genau darum steht der Aufruf so da.
echo "  Lean-Riegel: baue grammatik/ ..."
if lean_riegel; then LR=0; else LR=$?; fi
if [ $LR = 1 ]; then
    echo "ABBRUCH: der Lean-Bau ist ROT -- es wird nichts committet."
    echo "  Ein Commit auf rotem Bau vererbt den Bruch an jeden, der danach misst."
    exit 2
elif [ $LR = 2 ]; then
    echo "ABBRUCH: der Lean-Bau wurde NICHT GEFAHREN -- und das ist kein gruener Bau."
    echo "  Heilung: auf fisch bauen, oder mit Grund umgehen:"
    echo "  GABBRO_OHNE_LEAN=\"<warum>\" ./commit.sh"
    exit 2
fi
grep -q "Co-Authored-By" "$MSG" || printf '\nCo-Authored-By: Claude Opus 5 <noreply@anthropic.com>\n' >> "$MSG"
git -C "$W" commit -q -F "$MSG" --cleanup=verbatim
git -C "$W" log -1 --format='%h %s'
