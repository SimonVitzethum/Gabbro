#!/usr/bin/env bash
# **Der Grenzdurchstich, in einem Lauf.** Rust ruft eine Gabbro-Einheit ueber `extern "C"`.
#
#   .gab -> gabbro pruefe -> gabbro emit -> cc -> ar -> cargo -> gebunden -> AUSGEFUEHRT
#
# **Jede Frage hat ihre Gegenprobe.** Ein Pruefstand, der nur die eine Richtung zeigt, misst
# sich selbst: „verklemmt" heisst nur dann etwas ueber die Grenze, wenn derselbe Aufbau mit
# rangtreuem Nachbarn NICHT verklemmt.
set -uo pipefail
W="$(cd "$(dirname "$0")/../.." && pwd)"
H="$W/messung/grenze"
G="$W/target/debug/gabbro"
export PATH="$HOME/.cargo/bin:$PATH"

command -v cc  >/dev/null || { echo "KEIN CC -- dieser Lauf hat NICHTS gemessen"; exit 1; }
command -v cargo >/dev/null || { echo "KEIN CARGO -- dieser Lauf hat NICHTS gemessen"; exit 1; }
[ -x "$G" ] || { echo "KEIN gabbro unter $G -- erst bauen"; exit 1; }

echo "== 0. Was Gabbro ueber die Einheit sagt =="
"$G" pruefe "$H/grenze.gab" || exit 1
echo
echo "== 0b. Gegenprobe: dieselbe Datei mit vertauschten Sperren MUSS fallen =="
# **Mit `.gab`-Endung, und die Ausgabe wird GEFANGEN statt gerohrt.** Ohne die Endung
# liest der Pruefer die Datei nicht; und `set -o pipefail` machte aus dem erwarteten
# Ruecklaufwert 1 einen gefallenen `if`-Zweig. *Zwei Wege, auf denen die Gegenprobe
# still gruen aussieht, ohne etwas gemessen zu haben.*
T="$(mktemp --suffix=.gab)"; trap 'rm -f "$T"' EXIT
python3 - "$H/grenze.gab" "$T" <<'PY'
import sys, pathlib
q = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
n = q.replace("    locks A {\n      locks B {", "    locks B {\n      locks A {")
assert n != q, "der Sperrblock steht nicht mehr so da -- die Gegenprobe misst nichts"
pathlib.Path(sys.argv[2]).write_text(n, encoding="utf-8")
PY
GP="$("$G" pruefe "$T" 2>&1)" || true
if printf '%s' "$GP" | grep -q 'H006'; then
    echo "  ok -- H006 faellt. Das Gruen oben ist GEMESSEN, nicht still."
else
    echo "  GESCHEITERT -- die Sperrordnung wird an dieser Datei gar nicht geprueft."
    echo "  Dann sagt das Gruen oben nichts, und Frage 4 misst nichts."; exit 1
fi
echo
echo "== 1. Erzeugen =="
"$G" emit "$H/grenze.gab" > "$H/grenze.c" || exit 1
echo "  ok ($(grep -c '' "$H/grenze.c") Zeilen C)"
echo
echo "== 2. Bauen (cc fuer das C, cargo fuer den Rust, statisch gebunden) =="
( cd "$H/rust" && cargo build --release --offline ) || exit 1
( cd "$H/rust" && RUSTFLAGS="-C panic=abort" cargo build --release --offline --target-dir target-abort ) || exit 1
P="$H/rust/target/release/pruefstand"

fehler=0
for f in f1 f2 drift; do
    timeout 60 "$P" "$f" || { echo "  ($f endete mit $?)"; }
done

echo
echo "=================== FRAGE 3 -- Panik durch einen C-Rahmen ==================="
for bau in "unwind:$P" "abort:$H/rust/target-abort/release/pruefstand"; do
    strat="${bau%%:*}"; bin="${bau#*:}"
    aus="$(timeout 60 "$bin" f3 2>&1)"; rc=$?
    echo "  panic = $strat  ->  Ruecklaufwert $rc$( [ $rc -eq 134 ] && echo '  (SIGABRT)' )"
    echo "$aus" | grep -qE 'cannot unwind|abort' && echo "      Meldung: panic in a function that cannot unwind"
    if echo "$aus" | grep -q 'Rahmen verlassen'; then
        echo "      der C-Rahmen wurde VERLASSEN"
    else
        echo "      der C-Rahmen wurde NIE VERLASSEN -- kein Aufraeumen, kein Rueckgabewert"
    fi
done

echo
echo "=================== FRAGE 4 -- der Pruefstein ==================="
for lauf in f4a f4b f4c; do
    timeout 60 "$P" "$lauf"; rc=$?
    case "$lauf:$rc" in
        f4a:9|f4b:9) ;;                       # erwartet: verklemmt
        f4c:0) ;;                             # erwartet: laeuft durch
        *) echo "  UNERWARTET: $lauf endete mit $rc"; fehler=1 ;;
    esac
done
echo
[ $fehler -eq 0 ] && echo "== Der Pruefstand hat gemessen, was er messen sollte ==" \
                  || echo "== Ein Lauf ging anders aus als gebucht =="
exit $fehler
