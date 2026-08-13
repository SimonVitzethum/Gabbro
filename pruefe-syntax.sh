#!/usr/bin/env bash
# Haelt die Beispiele gegen SYNTAX.md. Mit Sprechprobe in BEIDE Richtungen --
# ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer.
set -uo pipefail
cd "$(dirname "$0")"

# Woerter, die es laut SYNTAX.md ABSICHTLICH nicht gibt.
VERBOTEN='\bwhile\b|\bfor\b|\bgoto\b|\bunion\b|\bswitch\b|_ =>|\bvoid\*'
# Deutsche Schluesselwoerter aus der Zeit vor E1 -- zwei Oberflaechen sind ein Riss.
ALTDEUTSCH='\bwirkung\b|\bbenoetigt\b|\buebergang\b|\bgattert\b|\bsprechprobe\b|\buntergrenze\b|\bgegenprobe\b|\bklasse\b|\bfelder\b|\berhaelt\b|\bmaskiert\b|\bwechsle\b|\bentfernt\b|\bdecrement\b|\beinheit\b|\broh fn\b|\blaeuft\b'

# Kommentare raus: ein Kommentar, der die verbotene Form ERKLAERT, ist kein Verstoss.
bloecke() { awk '/^```gabbro/{f=1;next}/^```$/{f=0}f' "$@" | sed 's/--.*$//'; }

pruefe() {                      # $1..: Dateien
  local rc=0 t
  t=$(bloecke "$@" | grep -nE "$VERBOTEN") && { echo "  VERBOTEN:"; echo "$t"; rc=1; }
  t=$(bloecke "$@" | grep -nE "$ALTDEUTSCH") && { echo "  ALTDEUTSCH:"; echo "$t"; rc=1; }
  return $rc
}

# F19: bis 2026-08-13 sah der Waechter NUR Codebloecke -- und behauptete trotzdem
# "keine zweite Schluesselwortsprache". `wechsle` stand derweil in SPRACHE.md:300, in PROSA.
# Ein Pruefer, der mehr behauptet, als sein Muster trifft, ist ein falsches Gruen.
# HISTORIE.md ist ausgenommen: sie DOKUMENTIERT die alten Woerter, das ist ihr Zweck.
prosa() { grep -vh '^\s*```' "$@" | grep -oE '`[a-zA-Z_ ]+`' ; }
pruefe_prosa() {
  local t
  t=$(prosa "$@" | grep -nE "$ALTDEUTSCH") && { echo "  ALTDEUTSCH IN PROSA:"; echo "$t"; return 1; }
  return 0
}

echo "== Beispiele gegen SYNTAX.md =="
if pruefe SPRACHE.md SYNTAX.md PLAN.md README.md && \
   pruefe_prosa SPRACHE.md SYNTAX.md PLAN.md README.md TODO.md P0-1-REVOKE.md; then
  echo "  keine verbotene Form in Beispielen, keine zweite Schluesselwortsprache in Prosa"
else
  echo "== SYNTAX: FEHLER =="; exit 1
fi

# --- Sprechprobe: der Pruefer MUSS bei jeder Verletzung fallen ---
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
n=0
for gift in 'while (x) { }' 'let a = wirkung;' 'goto ende;' 'traverse t over s by decrement { }'; do
  printf '```gabbro\n%s\n```\n' "$gift" > "$tmp/g.md"
  if pruefe "$tmp/g.md" >/dev/null; then
    echo "SPRECHPROBE GESCHEITERT: >>$gift<< kam durch"; exit 1
  fi
  n=$((n+1))
done
# ... und bei einem sauberen Block NICHT fallen
printf '```gabbro\ntraverse siblings of p over chain(a,b) in slots by unvisited { }\n```\n' > "$tmp/ok.md"
pruefe "$tmp/ok.md" >/dev/null || { echo "SPRECHPROBE GESCHEITERT: sauberer Block fiel durch"; exit 1; }
# Sprechprobe fuer den PROSA-Zweig -- er ist neu und darf nicht stumm sein.
printf 'Das Primitiv heisst `wechsle` und ist alt.\n' > "$tmp/p.md"
pruefe_prosa "$tmp/p.md" >/dev/null && { echo "SPRECHPROBE GESCHEITERT: Prosa-Zweig ist stumm"; exit 1; }
printf 'Das Primitiv heisst `switch_to`.\n' > "$tmp/pok.md"
pruefe_prosa "$tmp/pok.md" >/dev/null || { echo "SPRECHPROBE GESCHEITERT: saubere Prosa fiel durch"; exit 1; }
echo "Sprechprobe: $n Gifte in Beispielen gefangen, Prosa-Zweig spricht, Sauberes durchgelassen."
echo "== SYNTAX: ALL PASS =="
