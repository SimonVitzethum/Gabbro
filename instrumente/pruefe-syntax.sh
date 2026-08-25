#!/usr/bin/env bash
# Haelt die Beispiele gegen dokumente/SYNTAX.md. Mit Sprechprobe in BEIDE Richtungen --
# ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer.
set -uo pipefail

# **`LC_ALL=C` -- und das ist kein Schoenheitsfehler.** Fremde Werkzeuge melden im
# Gebietsschema des Benutzers: unter `de_DE.UTF-8` sagt der Binder `Mehrfachdefinition von`
# statt `multiple definition`, und ein `grep -q` darauf trifft nicht. Dieselbe Klasse wie
# `W16` -- ein Werkzeug, das sein eigenes Gebietsschema misst und dabei plausibel aussieht.
export LC_ALL=C

cd "$(dirname "$0")/.."

# Woerter, die es laut dokumente/SYNTAX.md ABSICHTLICH nicht gibt.
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
# "keine zweite Schluesselwortsprache". `wechsle` stand derweil in dokumente/SPRACHE.md:300, in PROSA.
# Ein Pruefer, der mehr behauptet, als sein Muster trifft, ist ein falsches Gruen.
# dokumente/HISTORIE.md ist ausgenommen: sie DOKUMENTIERT die alten Woerter, das ist ihr Zweck.
prosa() { grep -vh '^\s*```' "$@" | grep -oE '`[a-zA-Z_ ]+`' ; }
pruefe_prosa() {
  local t
  t=$(prosa "$@" | grep -nE "$ALTDEUTSCH") && { echo "  ALTDEUTSCH IN PROSA:"; echo "$t"; return 1; }
  return 0
}

echo "== Beispiele gegen dokumente/SYNTAX.md =="
if pruefe dokumente/SPRACHE.md dokumente/SYNTAX.md dokumente/PLAN.md README.md dokumente/BEWEIS.md dokumente/MESSUNGEN.md dokumente/FRAGMENTE.md dokumente/MEMO-GLEITKOMMA.md && \
   pruefe_prosa dokumente/SPRACHE.md dokumente/SYNTAX.md dokumente/PLAN.md README.md TODO.md dokumente/BEWEIS.md dokumente/MESSUNGEN.md dokumente/FRAGMENTE.md dokumente/MEMO-GLEITKOMMA.md; then
  echo "  keine verbotene Form in Beispielen, keine zweite Schluesselwortsprache in Prosa"
else
  echo "== SYNTAX: FEHLER =="; exit 1
fi

# --- Ist die Grammatik GESCHLOSSEN? Ein benutztes, nie definiertes Nichtterminal
# --- ist ein Loch, das beim Lesen nicht auffaellt: die EBNF sieht vollstaendig aus.
ebnf_geschlossen() {
  python3 - "$1" <<'PY'
import re, sys, pathlib
d = pathlib.Path(sys.argv[1]).read_text()
e = "\n".join(re.findall(r'```ebnf\n(.*?)```', d, re.S))
defs = set(re.findall(r'^\s*([a-z][a-z0-9_]*)\s*=', e, re.M))
b = re.sub(r'\(\*.*?\*\)', '', re.sub(r'^\s*[a-z][a-z0-9_]*\s*=', '', e, flags=re.M), flags=re.S)
b = re.sub(r'"[^"]*"', '', b); b = re.sub(r'\?.*?\?', '', b, flags=re.S)
offen = sorted(set(re.findall(r'\b([a-z][a-z0-9_]*)\b', b)) - defs)
print(f"  EBNF: {len(defs)} Regeln definiert, {len(offen)} offen" + (": " + ", ".join(offen) if offen else ""))
sys.exit(1 if offen else 0)
PY
}
if ! ebnf_geschlossen dokumente/SYNTAX.md; then echo "== SYNTAX: FEHLER (Grammatik nicht geschlossen) =="; exit 1; fi

if ! ./instrumente/pruefe-wortschatz.py dokumente/SYNTAX.md; then echo "== SYNTAX: FEHLER (Wortschatz deckt die EBNF nicht) =="; exit 1; fi

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
# Sprechprobe fuer den EBNF-Zweig
printf '```ebnf\na = b ;\n```\n' > "$tmp/e.md"
ebnf_geschlossen "$tmp/e.md" >/dev/null && { echo "SPRECHPROBE GESCHEITERT: EBNF-Zweig ist stumm"; exit 1; }
printf '```ebnf\na = "x" ;\n```\n' > "$tmp/eok.md"
ebnf_geschlossen "$tmp/eok.md" >/dev/null || { echo "SPRECHPROBE GESCHEITERT: geschlossene EBNF fiel durch"; exit 1; }
echo "Sprechprobe: $n Gifte in Beispielen gefangen, Prosa-Zweig spricht, Sauberes durchgelassen."
echo "== SYNTAX: ALL PASS =="

# **Null Warnungen, und zwar geprueft statt erinnert.** Dreimal in drei Laeufen habe ich
# GROSSSCHREIBUNG in einen Testnamen geschrieben und die Warnung hinterher weggeraeumt --
# beim dritten Mal war sie schon gepusht. Eine Warnung, die bei jedem Bau mitlaeuft, tarnt
# die naechste echte; ein Fehler, den man dreimal macht, gehoert in die Waechterkette.
echo "== Warnungen =="
# **Mit Frist**, seit dem 2026-08-20: ein `cargo build`, der nicht endet, sieht in einer
# Waechterkette aus wie einer, der noch baut. Am selben Tag standen deswegen einundzwanzig
# `pruefe-emission.sh` nebeneinander. *Eine ueberschrittene Frist ist ein BEFUND, kein Warten.*
FRIST=${FRIST:-900}
W=$(timeout "$FRIST" cargo build --tests 2>&1 | grep -cE "^warning: " || true)
if [ "$W" != "0" ]; then
  echo "  $W WARNUNG(EN) -- der Endzustand verlangt null:"
  timeout "$FRIST" cargo build --tests 2>&1 | grep -E "^warning: " | head -5
  echo "== SYNTAX: FEHLER (Warnungen im Bau) =="
  exit 1
fi
echo "  keine"
