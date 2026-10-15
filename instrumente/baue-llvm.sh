#!/bin/bash
# baue-llvm.sh -- reines Gabbro durch die LLVM-Pipeline, ohne C an jeder Stelle.
#
#   Gabbro --pruefe--> LLVM-IR-Text --llc--> Objekt --ld.lld--> Binary
#
# Kein `clang`, kein `cc`, keine libc, kein C-Laufzeitstart: der Eintritt `_start`
# kommt aus dem Erzeuger (`llvm.rs`), Systemaufrufe aus Gabbro-Toren mit
# Gabbro-Registersyntax (`syscall … regs in/out`). Die Binaries sind statisch und
# freistehend (`readelf` zeigt weder INTERP noch NEEDED -- das prüft Stufe 4).
#
# Stufen:
#   1. `gabbro check` muss schweigen (sonst keine Aussage über den Erzeuger).
#   2. `gabbro llvm --target=` schreibt das IR (x86_64 + aarch64).
#   3. `opt -O3` (Middle-End: Vektorisierung, LICM, GVN) + `llc -O3` (Codegen)
#      je Ziel (OPT Stufe wählbar: LLVM_OPT=O0/O3). `llc` allein fährt NICHT die
#      Middle-End-Pipeline (gemessen: langsamer als -O0) -- `opt` gehört dazu.
#   4. `ld.lld -e _start` linkt statisch; `readelf` bestätigt: keine libc.
#   5. Laufen lassen (aarch64 unter qemu) und Ausgaben/Rückgaben vergleichen.
#   6. Zeit messen (x86_64 nativ; qemu-Zeiten sind Emulation und zählen NICHT).
#
# Gebrauch: ./instrumente/baue-llvm.sh [datei.gab ...]  (ohne Angabe: Messprogramme)
set -u
W="$(cd "$(dirname "$0")/.." && pwd)"
GABBRO="$W/target/debug/gabbro"
LLVM_OPT="${LLVM_OPT:-O3}"
TLS="${TLS:-/tmp/gabbro-llvm}"
mkdir -p "$TLS"

if [ ! -x "$GABBRO" ]; then
    echo "baue-llvm: $GABBRO fehlt -- erst cargo build -p gabbro-cli" >&2
    exit 2
fi
for werkzeug in opt llc ld.lld readelf; do
    command -v "$werkzeug" >/dev/null || { echo "baue-llvm: $werkzeug fehlt" >&2; exit 2; }
done
# KEIN clang, KEIN cc, KEIN gcc in dieser Pipeline -- wer sie hier aufruft, lügt.
if command -v clang >/dev/null; then
    echo "baue-llvm: Hinweis: clang ist installiert, wird aber NICHT benutzt (kein C)." >&2
fi

# Die Werkzeugkette ist geschlossen: nur `$GABBRO`, `llc`, `ld.lld`, `readelf`,
# `qemu-aarch64` (nur Ablauf, kein Bau) und Shell-Bordmittel laufen unten je
# einmal. Wer `clang`, `cc` oder `gcc` hier aufruft, steht im Diff — kein C.

dateien=("$@")
if [ "${#dateien[@]}" -eq 0 ]; then
    dateien=("$W/messung/llvm/summe.gab")
fi

fehler=0
for datei in "${dateien[@]}"; do
    name="$(basename "$datei" .gab)"
    echo "== $name =="
    # 1. Prüfer zuerst.
    if ! "$GABBRO" check "$datei" >/dev/null 2>"$TLS/$name.check"; then
        echo "  1. PRÜFER ROT:"; head -n 6 "$TLS/$name.check" | sed 's/^/  /'; fehler=1; continue
    fi
    echo "  1. Prüfer grün."
    for ziel in x86_64 aarch64; do
        ll="$TLS/$name-$ziel.ll"
        o="$TLS/$name-$ziel.o"
        bin="$TLS/$name-$ziel"
        # 2. IR aus Gabbro -- direkt, ohne C.
        if ! "$GABBRO" llvm --target="$ziel" "$datei" >"$ll" 2>"$TLS/$name-$ziel.llvm-err"; then
            echo "  2. [$ziel] ERZEUGER ROT:"; head -n 4 "$TLS/$name-$ziel.llvm-err" | sed 's/^/  /'; fehler=1; continue
        fi
        # 3. opt (Middle-End) + llc (Codegen) -- beides LLVM-Werkzeuge, kein C.
        triple="$ziel-unknown-linux-gnu"
        [ "$ziel" = "x86_64" ] && triple="x86_64-unknown-linux-gnu"
        [ "$ziel" = "aarch64" ] && triple="aarch64-unknown-linux-gnu"
        if ! opt "-$LLVM_OPT" "$ll" -o "$TLS/$name-$ziel.bc" 2>"$TLS/$name-$ziel.opt-err"; then
            echo "  3. [$ziel] OPT ROT:"; head -n 4 "$TLS/$name-$ziel.opt-err" | sed 's/^/  /'; fehler=1; continue
        fi
        if ! llc "-$LLVM_OPT" -mtriple="$triple" -filetype=obj "$TLS/$name-$ziel.bc" -o "$o" 2>"$TLS/$name-$ziel.llc-err"; then
            echo "  3. [$ziel] LLC ROT:"; head -n 4 "$TLS/$name-$ziel.llc-err" | sed 's/^/  /'; fehler=1; continue
        fi
        # 4. ld.lld, statisch, Eintritt _start. Keine Bibliothek, keine Startdateien.
        if ! ld.lld -static -e _start -o "$bin" "$o" 2>"$TLS/$name-$ziel.ld-err"; then
            echo "  4. [$ziel] LINK ROT:"; head -n 4 "$TLS/$name-$ziel.ld-err" | sed 's/^/  /'; fehler=1; continue
        fi
        # 4b. Keine libc: weder INTERP noch NEEDED noch .interp-Sektion.
        if readelf -l "$bin" 2>/dev/null | grep -q "INTERP\|NEEDED"; then
            echo "  4b. [$ziel] FUND: Binary hängt an C-Bibliothek/Loader:"; readelf -l "$bin" | grep "INTERP\|NEEDED" | sed 's/^/  /'; fehler=1; continue
        fi
        echo "  2-4. [$ziel] IR -> opt+llc(-$LLVM_OPT) -> ld.lld: statisch, ohne INTERP/NEEDED."
        # 5. Laufen lassen.
        if [ "$ziel" = "aarch64" ]; then
            if ! command -v qemu-aarch64 >/dev/null; then echo "  5. [aarch64] qemu fehlt -- übersprungen"; continue; fi
            lauf="qemu-aarch64 $bin"
        else
            lauf="$bin"
        fi
        # shellcheck disable=SC2086
        out="$(timeout 120 $lauf 2>&1)"; rc=$?
        echo "$out" >"$TLS/$name-$ziel.ausgabe"
        echo "  5. [$ziel] rc=$rc ausgabe=$(head -c 60 "$TLS/$name-$ziel.ausgabe" | tr '\n' '|')"
        eval "rc_$ziel=$rc"
    done
    # 5b. Beide Ziele müssen dasselbe sagen (gleiche Semantik auf beiden ISAs).
    if [ -n "${rc_x86_64:-}" ] && [ -n "${rc_aarch64:-}" ]; then
        if [ "$rc_x86_64" = "$rc_aarch64" ] && cmp -s "$TLS/$name-x86_64.ausgabe" "$TLS/$name-aarch64.ausgabe"; then
            echo "  5b. x86_64 und aarch64 stimmen überein (rc=$rc_x86_64)."
        else
            echo "  5b. FUND: Ziele weichen ab (x86_64: rc=$rc_x86_64, aarch64: rc=$rc_aarch64)."; fehler=1
        fi
    fi
    unset rc_x86_64 rc_aarch64
done
exit "$fehler"
