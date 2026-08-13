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

echo "== Beispiele gegen SYNTAX.md =="
if pruefe SPRACHE.md SYNTAX.md PLAN.md README.md; then
  echo "  keine verbotene Form, keine zweite Schluesselwortsprache"
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
echo "Sprechprobe: $n Gifte gefangen, sauberer Block durchgelassen."
echo "== SYNTAX: ALL PASS =="
