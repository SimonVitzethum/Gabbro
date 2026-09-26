#!/usr/bin/env bash
# instrumente/pruefe-metall.sh -- Gabbro threads on BARE METAL, booted under QEMU
# (Opus agent I, 2026-09-26; stage 11 of `pruefe-emission.sh`, runnable alone).
#
# WHAT IT MEASURES. The emitted C of a Gabbro unit, UNCHANGED, linked against the
# freestanding thread runtime `laufzeit/metall/` (Multiboot1 entry, long mode, SMP
# bring-up, per-core round-robin scheduler with LAPIC-timer preemption, the ticket lock
# of CTicket.lean) -- no libc, no Linux -- booted on `qemu-system-x86_64 -smp 4`, and
# the report on the serial port (0x3F8) compared with a hand-written expectation.
#
#   metall159   runtime `start { heber_a, heber_b }` on a lock-guarded counter: 2N = 64
#   metall124   boot `concurrent { hauptA, hauptB }` through the GENERATED bare-metal
#               driver (`gabbro build` -> `<unit>.metall.c`): the lock invariant, the
#               private tables, the one schedule-dependent value named as a set
#   metall157   the worker pool `concurrent { arbeiter, arbeiter }`, generated driver
#   (hosted)    the same interface on Linux (`laufzeit/faden.c`): 200000 start/join rounds
#               on one stack -- the lost-join race fixed on 2026-09-26 stays fixed
#
# Every boot also checks `METALL-VERTEILUNG`, the threads that ended on each core: the
# declared starts ran on other cores than their starter (placement is round robin from
# core 1, so the line is deterministic).
#   stress      8 threads x 20000 increments under ONE ticket lock (more threads than
#               cores: preempted holders and same-core waiters), plus 200 start/join
#               rounds on ONE reused stack (the join word cleared only after the thread
#               has left the stack)
#   staffel     a thread spins on a flag that only a LATER thread of the SAME core sets:
#               finishes only if the core is taken away from the spinner (preemption)
#
# Each positive has a gift that must FAIL (R14): the counter step `+1 -> +0` (159);
# the lock macro emptied (stress: lost updates); the runtime built cooperative
# (`-DMETALL_KOOPERATIV`: staffel hangs into the timeout).
#
# QEMU MISSING IS NOT A PASS. Without `qemu-system-x86_64` every image is still BUILT
# and LINKED (freestanding, `nm` shows no undefined symbol), and the script says
# `METALL: NOT RUN` for the boots -- a line no reader can mistake for a result.
#
# USAGE
#   instrumente/pruefe-metall.sh [WORKDIR]
#   GABBRO_BIN=target/debug/gabbro instrumente/pruefe-metall.sh   # skip `cargo run`
# Exit 0 = every run held (or NOT RUN, said so), 1 = a finding.
set -euo pipefail

W="$(cd "$(dirname "$0")/.." && pwd)"
M="$W/laufzeit/metall"
ARB="${1:-$W/.tmp/metall}"
mkdir -p "$ARB"

G() {
    if [ -n "${GABBRO_BIN:-}" ]; then "$GABBRO_BIN" "$@"
    else cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- "$@"; fi
}

echo "== Stufe 11: bare metal -- Gabbro threads without an OS (laufzeit/metall/) =="

for t in cc ld objcopy nm; do
    if ! command -v "$t" > /dev/null; then
        echo "  METALL: NOT RUN -- \`$t\` missing; nothing was built, nothing was measured."
        exit 0
    fi
done
QEMU=""
command -v qemu-system-x86_64 > /dev/null && QEMU=qemu-system-x86_64

# The one flag word for every C file of an image. `-mno-red-zone`: the timer interrupt
# pushes onto the running thread's stack, and a leaf function's red zone would be under it.
CF="-std=c11 -O2 -ffreestanding -fno-builtin -nostdlib -fno-pic -fno-pie -mno-red-zone
    -mcmodel=small -fno-stack-protector -fno-asynchronous-unwind-tables
    -fno-tree-loop-distribute-patterns -Wall -Wextra -Werror"

# baue NAME EXTRA_CFLAGS -- $ARB/NAME/treiber.c (+ einheit.c) -> $ARB/NAME/k32.elf
baue() {
    local d="$ARB/$1" extra="$2"
    # shellcheck disable=SC2086
    cc $CF $extra -c "$M/kern.c" -o "$d/kern.o" 2> "$d/cc.err" \
      && cc -fno-pie -c "$M/start.S" -o "$d/start.o" 2>> "$d/cc.err" \
      && cc $CF $extra -I"$M" -I"$d" -DEINHEIT_INCLUDE='"einheit.c"' \
            -c "$d/treiber.c" -o "$d/treiber.o" 2>> "$d/cc.err" \
      && ld -nostdlib -static -no-pie -T "$M/metall.ld" -z max-page-size=0x1000 \
            -o "$d/k.elf" "$d/start.o" "$d/kern.o" "$d/treiber.o" 2>> "$d/cc.err" \
      && objcopy -O elf32-i386 "$d/k.elf" "$d/k32.elf" 2>> "$d/cc.err" || {
        echo "  $1: BUILD FAILED"; head -20 "$d/cc.err"; return 1; }
    # Freestanding, measured: a linked image with an undefined symbol does not exist
    # (`ld` refuses), and no Linux thread call survives in it by name.
    if nm "$d/k.elf" | grep -E ' U |pthread|clone|futex' > "$d/nm.fund"; then
        echo "  $1: NOT FREESTANDING:"; cat "$d/nm.fund"; return 1
    fi
}

# boote NAME -> $ARB/NAME/serial.log; prints the qemu status
boote() {
    local d="$ARB/$1"
    : > "$d/serial.log"
    set +e
    timeout "${METALL_ZEIT:-60}" "$QEMU" -machine pc -accel tcg,thread=multi -smp 4 -m 128M \
        -display none -monitor none -no-reboot -serial "file:$d/serial.log" \
        -device isa-debug-exit,iobase=0xf4,iosize=0x04 -kernel "$d/k32.elf" \
        > "$d/qemu.out" 2>&1
    local rc=$?
    set -e
    echo "$rc"
}

BEFUND=0
N_GEBOOTET=0

# pruefe NAME EXPECTED_LINE... : every expected line must stand in the log, plus the
# success end; the qemu status must be the debug-exit success (0x10 << 1 | 1 = 33).
pruefe() {
    local name="$1"; shift
    local d="$ARB/$name" rc
    rc="$(boote "$name")"
    local fehlt=""
    for z in "$@" "METALL-ENDE 0"; do
        grep -qxF "$z" "$d/serial.log" || fehlt="$fehlt [$z]"
    done
    if [ "$rc" != 33 ] || [ -n "$fehlt" ]; then
        echo "  $name: FAILED (qemu status $rc; missing:$fehlt)"
        sed 's/^/      /' "$d/serial.log" | head -20
        BEFUND=1
        return 0
    fi
    N_GEBOOTET=$((N_GEBOOTET + 1))
    echo "  $name: ok ($(grep -c '' "$d/serial.log") serial lines, $(grep '^METALL-KERNE' "$d/serial.log"))"
}

# gift NAME WHY : the boot must NOT show the success end.
gift() {
    local name="$1" why="$2" d="$ARB/$1" rc
    rc="$(boote "$name")"
    if [ "$rc" = 33 ] && grep -qxF "METALL-ENDE 0" "$d/serial.log"; then
        echo "  $name: GIFT DOES NOT BITE -- $why"; BEFUND=1
    else
        echo "  $name: bites ($why; qemu status $rc)"
    fi
}

einheit() {   # einheit NAME SOURCE [SED]
    local d="$ARB/$1"; mkdir -p "$d"
    G emit "$2" > "$d/einheit.c"
    if [ -n "${3:-}" ]; then
        sed -i "$3" "$d/einheit.c"
    fi
}

# -- 159: runtime `start`. -----------------------------------------------------------
TREIBER159='#include "metall.h"
#include "einheit.c"
METALL_SPERRE(L)
int gabbro_metall_haupt(void)
{
    uint32_t v = lauf();
    metall_schreibe("159 lauf "); metall_zahl(v); metall_schreibe("\n");
    return v == 64u ? 0 : 1;
}
'
einheit metall159 "$W/beispiele/159-laufzeit-start.gab"
printf '%s' "$TREIBER159" > "$ARB/metall159/treiber.c"
einheit metall159-gift "$W/beispiele/159-laufzeit-start.gab" \
    's/stand) + (uint32_t)(1)/stand) + (uint32_t)(0)/'
if cmp -s "$ARB/metall159/einheit.c" "$ARB/metall159-gift/einheit.c"; then
    echo "  metall159-gift: the mutation did not apply -- the gift would measure nothing"; exit 1
fi
printf '%s' "$TREIBER159" > "$ARB/metall159-gift/treiber.c"

# -- 124 and 157: boot `concurrent` sets, through the GENERATED bare-metal driver.
#    `gabbro build` writes `<unit>.metall.c` beside the hosted `<unit>.treiber.c` (same plan,
#    same multiset pin, `treiber.rs` `erzeuge_metall`); the harness appends the observation
#    at the NACHLAUF marker -- the build artefact and the test artefact differ by exactly
#    that block, as with the hosted driver. The driver thread joins the declared starts and
#    reads the carriers under the lock.
concurrent_wurzeln() {  # the members of the source's `concurrent { ... }` sets, in order
    sed -n 's/^[[:space:]]*concurrent[[:space:]]*{\(.*\)};.*/\1/p' "$1" | tr ',' '\n' | tr -d ' ' | grep -v '^$'
}
boot_einheit() {  # boot_einheit NAME SOURCE OBSERVATION_FILE
    local d="$ARB/$1" out="$ARB/$1/out"
    mkdir -p "$d"
    printf 'compiler cc -std=c11 -O0 -Wall -Wextra -Werror -pthread\nout %s\nunit einheit object\n    %s\n' \
        "$out" "$2" > "$d/bau"
    if ! G build "$d/bau" > "$d/bau.log" 2>&1; then
        echo "  $1: gabbro build FAILED"; sed 's/^/      /' "$d/bau.log" | head -10; exit 1
    fi
    [ -f "$out/einheit.metall.c" ] || { echo "  $1: no einheit.metall.c written by gabbro build"; exit 1; }
    cp "$out/einheit.c" "$d/einheit.c"
    awk -v f="$3" '/\/\* NACHLAUF:/ { while ((getline z < f) > 0) print z } { print }' \
        "$out/einheit.metall.c" > "$d/treiber.c"
    # The pin: the generated driver starts exactly the members the source declares, BY COUNT.
    local soll ist
    soll="$(concurrent_wurzeln "$2" | sort | uniq -c | tr -s ' ')"
    ist="$(grep -o 'gabbro_faden_start([a-zA-Z_0-9]*' "$d/treiber.c" \
           | sed 's/gabbro_faden_start(//' | sort | uniq -c | tr -s ' ')"
    if [ -z "$soll" ] || [ "$soll" != "$ist" ]; then
        echo "  $1: PIN -- source starts [$soll], driver starts [$ist]"; exit 1
    fi
}

cat > "$ARB/beob124.c" <<'C124'
    L_nimm();
    uint32_t k0 = konto_speicher.slots[0].stand, k1 = konto_speicher.slots[1].stand;
    uint32_t a = privA_speicher.slots[0].stand, b = privB_speicher.slots[0].stand;
    L_gib();
    metall_schreibe("124 konto-gleich "); metall_zahl(k0 == k1);
    metall_schreibe(" konto-in-30-70 "); metall_zahl(k0 == 30u || k0 == 70u);
    metall_schreibe(" privA "); metall_zahl(a);
    metall_schreibe(" privB "); metall_zahl(b); metall_schreibe("\n");
    if (!(k0 == k1 && (k0 == 30u || k0 == 70u) && a == 7u && b == 5u)) return 1;
C124
boot_einheit metall124 "$W/beispiele/124-two-threads-private.gab" "$ARB/beob124.c"

cat > "$ARB/beob157.c" <<'C157'
    L_nimm();
    uint32_t k0 = konto_speicher.slots[0].stand, k1 = konto_speicher.slots[1].stand;
    L_gib();
    metall_schreibe("157 konto "); metall_zahl(k0); metall_schreibe(" ");
    metall_zahl(k1); metall_schreibe("\n");
    if (!(k0 == 30u && k1 == 30u)) return 1;
C157
boot_einheit metall157 "$W/beispiele/157-worker-pool.gab" "$ARB/beob157.c"

# -- stress: the lock under contention, and stack reuse after a join. -------------------
TREIBER_STRESS='#include "metall.h"
SPERRE_DEF
static volatile uint32_t zaehler;
static void heber(void)
{
    for (int i = 0; i < 20000; i++) {
        L_nimm();
        zaehler = zaehler + 1u;
        L_gib();
    }
}
static void leer(void) { zaehler = zaehler; }
#define NF 8
static unsigned char st[NF][16384] __attribute__((aligned(16)));
static uint32_t w[NF];
static unsigned char st1[16384] __attribute__((aligned(16)));
static uint32_t w1;
int gabbro_metall_haupt(void)
{
    for (int i = 0; i < NF; i++) {
        if (gabbro_faden_start(heber, st[i] + sizeof(st[i]), &w[i]) != 0) return 4;
    }
    for (int i = 0; i < NF; i++) gabbro_faden_warte(&w[i]);
    uint32_t z = zaehler;
    metall_schreibe("stress zaehler "); metall_zahl(z); metall_schreibe("\n");
    for (int r = 0; r < 200; r++) {
        if (gabbro_faden_start(leer, st1 + sizeof(st1), &w1) != 0) return 5;
        gabbro_faden_warte(&w1);
    }
    metall_schreibe("stress wiederverwendung 200\n");
    return z == NF * 20000u ? 0 : 1;
}
'
mkdir -p "$ARB/stress" "$ARB/stress-gift"
printf '%s' "$TREIBER_STRESS" | sed 's/^SPERRE_DEF$/METALL_SPERRE(L)/' > "$ARB/stress/treiber.c"
printf '%s' "$TREIBER_STRESS" | sed 's/^SPERRE_DEF$/static void L_nimm(void) {} static void L_gib(void) {}/' \
    > "$ARB/stress-gift/treiber.c"

# -- staffel: a same-core spin that only preemption resolves. ---------------------------
#    Starts go round robin from core 1; with K cores the first and the (K+1)-th start share
#    core 1. The first spins until the (K+1)-th has run. Cooperative: it never gives the
#    core away, and the machine hangs into the timeout.
TREIBER_STAFFEL='#include "metall.h"
static _Atomic uint32_t flagge;
static void warter(void)
{
    while (atomic_load_explicit(&flagge, memory_order_acquire) == 0u) { }
}
static void setzer(void) { atomic_store_explicit(&flagge, 1u, memory_order_release); }
static void nichts(void) { }
static unsigned char st[17][16384] __attribute__((aligned(16)));
static uint32_t w[17];
int gabbro_metall_haupt(void)
{
    uint32_t k = metall_kerne();
    if (k < 2u || k > 16u) { metall_schreibe("staffel braucht 2..16 Kerne\n"); return 1; }
    for (uint32_t i = 0; i <= k; i++) {
        void (*f)(void) = i == 0 ? warter : (i == k ? setzer : nichts);
        if (gabbro_faden_start(f, st[i] + sizeof(st[i]), &w[i]) != 0) return 4;
    }
    for (uint32_t i = 0; i <= k; i++) gabbro_faden_warte(&w[i]);
    metall_schreibe("staffel durch\n");
    return 0;
}
'
mkdir -p "$ARB/staffel" "$ARB/staffel-gift"
printf '%s' "$TREIBER_STAFFEL" > "$ARB/staffel/treiber.c"
printf '%s' "$TREIBER_STAFFEL" > "$ARB/staffel-gift/treiber.c"

# -- Build everything (this half runs without qemu). ------------------------------------
for n in metall159 metall159-gift metall124 metall157 stress stress-gift staffel; do
    baue "$n" "" || exit 1
done
baue staffel-gift "-DMETALL_KOOPERATIV" || exit 1
echo "  built and linked: 8 freestanding images (no libc, no undefined symbol, no pthread/clone/futex)"

# -- The hosted counter-probe of the SAME interface (laufzeit/faden.c, Linux x86_64 only).
#    200000 start/join rounds of an empty root on ONE stack. Before 2026-09-26 the parent
#    stored the TID into the join word after `clone` returned, so a child that had already
#    ended got its cleared word overwritten with a dead TID, and the join hung (measured:
#    before round 20000). CLONE_PARENT_SETTID closes it; this probe holds it closed. It
#    has no gift: the lost join is a race, and a mutation would bite only sometimes.
if [ "$(uname -s)-$(uname -m)" = "Linux-x86_64" ]; then
    mkdir -p "$ARB/wettlauf"
    cat > "$ARB/wettlauf/w.c" <<'WETT'
#include <stdint.h>
#include <stdio.h>
#include "@FADEN@"
static unsigned char st[65536] __attribute__((aligned(16)));
static uint32_t w;
static void leer(void) { }
int main(void)
{
    for (int r = 0; r < 200000; r++) {
        if (gabbro_faden_start(leer, st + sizeof st, &w) != 0) return 2;
        gabbro_faden_warte(&w);
    }
    printf("durch\n");
    return 0;
}
WETT
    sed -i "s|@FADEN@|$W/laufzeit/faden.c|" "$ARB/wettlauf/w.c"
    cc -std=c11 -O2 -Wall -Wextra -Werror -o "$ARB/wettlauf/w" "$ARB/wettlauf/w.c"
    if [ "$(timeout 60 "$ARB/wettlauf/w" || true)" = "durch" ]; then
        echo "  hosted join (faden.c): ok (200000 start/join rounds on one stack)"
    else
        echo "  hosted join (faden.c): FAILED -- the join lost a thread's end"; BEFUND=1
    fi
else
    echo "  hosted join (faden.c): NOT RUN -- not Linux x86_64"
fi

if [ -z "$QEMU" ]; then
    echo "  METALL: NOT RUN -- qemu-system-x86_64 is not installed. The images above were"
    echo "  built and linked; NONE was booted. This is not a pass."
    exit "$BEFUND"
fi

pruefe metall159 "159 lauf 64" "METALL-VERTEILUNG 0 1 1 0"
pruefe metall124 "124 konto-gleich 1 konto-in-30-70 1 privA 7 privB 5" "METALL-VERTEILUNG 0 1 1 0"
pruefe metall157 "157 konto 30 30" "METALL-VERTEILUNG 0 1 1 0"
pruefe stress "stress zaehler 160000" "stress wiederverwendung 200" "METALL-VERTEILUNG 52 52 52 52"
pruefe staffel "staffel durch" "METALL-VERTEILUNG 1 2 1 1"
gift metall159-gift "counter step +1 -> +0 reports 0, not 64"
gift stress-gift "no lock: lost updates under 8 threads on 4 cores"
METALL_ZEIT=20 gift staffel-gift "cooperative runtime: the spinner never yields its core"

if [ "$BEFUND" != 0 ]; then
    echo "== METALL: FINDING (see above) =="
    exit 1
fi
echo "== METALL: $N_GEBOOTET booted on qemu -smp 4, every expectation held, 3 gifts bite =="
