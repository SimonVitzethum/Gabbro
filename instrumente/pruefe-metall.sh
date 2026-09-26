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
# Opus agent J (2026-09-26) added the features beyond threads (details at the images):
#   metall153/154/158(-else)  arenas on the bare-metal arena runtime (`arena.c`); the
#               `else` of `grow` taken by the REAL runtime under a smaller commit budget
#   metall161   bounded strings (memcpy/memcmp from the runtime)
#   metall59    the program's own `via idt` handler and entered entry in the metal IDT,
#               fired by fixed IPIs while threads take the `masks irqs` lock
#   metall07    an entry's register binding (`regs in`/`regs out`) through `int $0x80`,
#               and an NMI entry fired by an NMI IPI
# Opus agent L (OFFEN O31) added the gates bound for the metal target:
#   metall164   the program IS the kernel: its gate's `int $0x80` lands in its own entry
#   metall163   `--target metal`: the gate enters the runtime's vector-0x80 slot and the
#               image's C kernel (`metall_systemruf`) serves it
#   metall165   an entry on #GP (vector 13, pushes an error code) through the twin stub
#               `METALL_EINTRITT_FC` (OFFEN O32 (9))
# with gifts: the entry answers `len + 1` (164), an image with no kernel (163: the first
# gate call ends the machine, status 9, never an invented answer), and the plain stub on
# the error-code vector (165: `iretq` takes the code for the return address).
# with gifts: `17 -> 18` (158) and the masked lock built unmasked (59: hangs, and the
# handler reports that it landed on a core with a claim on the lock).
# Every image compiles with `-nostdinc` (the compiler's headers + `laufzeit/metall/include`).
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
# `-nostdinc` + the compiler's own headers + `laufzeit/metall/include/` (Opus agent J): the
# emitted unit includes <math.h> (and strings <string.h>), which a freestanding toolchain
# does not have; the image must not quietly borrow the host's C-library headers.
GCCINC="$(cc -print-file-name=include)"
CF="-std=c11 -O2 -ffreestanding -fno-builtin -nostdlib -nostdinc -isystem $GCCINC
    -isystem $M/include -fno-pic -fno-pie -mno-red-zone
    -mcmodel=small -fno-stack-protector -fno-asynchronous-unwind-tables
    -fno-tree-loop-distribute-patterns -Wall -Wextra -Werror"

# baue NAME EXTRA_CFLAGS [DRIVER_CFLAGS] -- $ARB/NAME/treiber.c (+ einheit.c) -> k32.elf
#   EXTRA_CFLAGS go to the runtime AND the driver (e.g. -DMETALL_KOOPERATIV, a smaller
#   arena budget); DRIVER_CFLAGS to the driver alone (e.g. -O0 for a unit whose `-O2`
#   diagnostics are the emitter's business, not the runtime's).
#   With `$ARB/NAME/fremd.ok` present, every symbol the driver leaves undefined that the
#   runtime does not define gets a TRAP stub (the program's own foreign bodies it does not
#   exercise: the run ends loudly if one is called). Without it, an undefined symbol is a
#   build failure, as before.
baue() {
    local d="$ARB/$1" extra="$2" textra="${3:-}"
    # shellcheck disable=SC2086
    cc $CF $extra -c "$M/kern.c" -o "$d/kern.o" 2> "$d/cc.err" \
      && cc $CF $extra -c "$M/arena.c" -o "$d/arena.o" 2>> "$d/cc.err" \
      && cc -fno-pie -c "$M/start.S" -o "$d/start.o" 2>> "$d/cc.err" \
      && cc $CF $extra $textra -I"$M" -I"$d" -DEINHEIT_INCLUDE='"einheit.c"' \
            -c "$d/treiber.c" -o "$d/treiber.o" 2>> "$d/cc.err" || {
        echo "  $1: BUILD FAILED"; head -20 "$d/cc.err"; return 1; }
    : > "$d/fremd.S"
    if [ -f "$d/fremd.ok" ]; then
        nm --defined-only "$d/kern.o" "$d/arena.o" "$d/start.o" | awk 'NF == 3 {print $3}' \
            | sort -u > "$d/rt.def"
        nm -u "$d/treiber.o" | awk '{print $2}' | sort -u | comm -23 - "$d/rt.def" > "$d/fremd.namen"
        while IFS= read -r s; do
            printf '\t.text\n\t.global %s\n%s:\n\tmovq $%s_n, %%rdi\n\tjmp metall_fremd_fehlt\n\t.section .rodata\n%s_n:\n\t.asciz "%s"\n' \
                "$s" "$s" "$s" "$s" "$s" >> "$d/fremd.S"
        done < "$d/fremd.namen"
    fi
    # shellcheck disable=SC2086
    cc -fno-pie -c "$d/fremd.S" -o "$d/fremd.o" 2>> "$d/cc.err" \
      && ld -nostdlib -static -no-pie -T "$M/metall.ld" -z max-page-size=0x1000 \
            -o "$d/k.elf" "$d/start.o" "$d/kern.o" "$d/arena.o" "$d/treiber.o" "$d/fremd.o" \
            2>> "$d/cc.err" \
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

# =======================================================================================
# Opus agent J (2026-09-26): the features beyond threads, on the same bare metal.
#
#   metall153/154/158  dynamic arenas through the BARE-METAL arena runtime
#                      (`laufzeit/metall/arena.c`: a static reserve, commit = bookkeeping
#                      against a budget): the static twins 153/154 and the dynamic 158,
#                      whose `grow` commits the upper half (118) --
#   metall158-else     -- and the SAME source with a commit budget of exactly the floor
#                      (`-DMETALL_ARENA_ZUSAGE=8`: 4 slots x 2 bytes): the runtime REFUSES
#                      the grow and the program's `else` answers 1. Not a stub: the real
#                      runtime, with a smaller number.
#   metall161          bounded strings (lane 261): `memcpy`/`memcmp` from the runtime,
#                      <string.h> from `laufzeit/metall/include/`
#   metall59           the program's OWN `via idt` handler (`entry zeitgeber vector 32`)
#                      and its entered entry (`systemruf vector 0x80`), installed in the
#                      metal IDT, fired by real fixed IPIs from core 0 while three threads
#                      take the `masks irqs` lock `TAKT` in a loop; every handler run checks
#                      that it did NOT land on the core that holds `TAKT` (the observable
#                      form of the masked-lock discipline)
#   metall59-gift      the same with `TAKT` built UNMASKED: an IPI lands inside a held
#                      section, the handler waits for its own interrupted thread -- the
#                      same-core deadlock `H102` refuses (`gift/460`) -- and the machine
#                      hangs into the timeout
#   metall07           an entry with a REGISTER BINDING (`regs in { nr : rax, a0 : rdi,
#                      a1 : rsi, a2 : rdx, a3 : r10 } regs out { ret : rax }`), entered by
#                      `int $0x80` with chosen registers, and an NMI entry (vector 2) fired
#                      by an NMI IPI; the program's foreign bodies `syscall_verteiler` and
#                      `nmi_verteiler` are the driver's own C (the program side), every
#                      other foreign body a trap stub
cat > "$ARB/treiber-arena.c" <<'CARENA'
#include "metall.h"
#include "einheit.c"
int gabbro_metall_haupt(void)
{
    uint32_t v = ARENA_RUF;
    metall_schreibe(ARENA_NAME " "); metall_zahl(v); metall_schreibe("\n");
    return v == ARENA_SOLL ? 0 : 1;
}
CARENA
arena_bild() {  # arena_bild NAME SOURCE CALL EXPECTED [SED]
    local d="$ARB/$1"; mkdir -p "$d"
    einheit "$1" "$2" "${5:-}"
    { printf '#define ARENA_NAME "%s"\n#define ARENA_RUF %s\n#define ARENA_SOLL %su\n' "$1" "$3" "$4"
      cat "$ARB/treiber-arena.c"; } > "$d/treiber.c"
}
arena_bild metall153 "$W/beispiele/153-arena-waechst.gab" "waechst()" 370
arena_bild metall154 "$W/beispiele/154-arena-voll.gab" "voll()" 1004
arena_bild metall158 "$W/beispiele/158-arena-commit.gab" \
    "(gabbro_arena_reserve(&Vorrat_desc), fuellen())" 118
arena_bild metall158-else "$W/beispiele/158-arena-commit.gab" \
    "(gabbro_arena_reserve(&Vorrat_desc), fuellen())" 1
arena_bild metall158-gift "$W/beispiele/158-arena-commit.gab" \
    "(gabbro_arena_reserve(&Vorrat_desc), fuellen())" 118 's/(17)/(18)/'
if cmp -s "$ARB/metall158/einheit.c" "$ARB/metall158-gift/einheit.c"; then
    echo "  metall158-gift: the mutation did not apply -- the gift would measure nothing"; exit 1
fi

mkdir -p "$ARB/metall161"
einheit metall161 "$W/beispiele/161-zeichenkette.gab"
cat > "$ARB/metall161/treiber.c" <<'C161'
#include "metall.h"
#include "einheit.c"
static void z(uint32_t v) { metall_zahl(v); metall_schreibe(" "); }
int gabbro_metall_haupt(void)
{
    gabbro_string_8 h = baue();
    gabbro_string_16 k = kopiere(h);
    gabbro_string_5 a = { 2, "hi" };
    gabbro_string_3 b = { 1, "!" };
    gabbro_string_8 c = haenge_an(a, b);
    metall_schreibe("161 ");
    z(h.len); z(h.data[0]); z(h.data[1]); z(k.len); z(laenge(c));
    z(zeichen(c, 0)); z(zeichen(c, 1)); z(zeichen(c, 2));
    z(gleich(h, h)); z(gleich(h, c)); z(kleiner(h, c)); metall_zahl(kleiner(c, h));
    metall_schreibe("\n");
    return 0;
}
C161

TREIBER59='#include "metall.h"
#include "einheit.c"
SPERRE_TAKT
METALL_SPERRE(RING)
static _Atomic uint32_t verletzt;
/* Every run of the thrown entry first asks: does THIS core hold TAKT right now? With a
 * masked TAKT that can never be true (IF = 0 while held); the answer is the report. */
static void takt_beobachtet(void)
{
    if (metall_anspruch_TAKT[metall_kern_nr()] != 0u) {
        if (atomic_fetch_add_explicit(&verletzt, 1u, memory_order_relaxed) == 0u) {
            metall_schreibe("59 an entry landed on a core with a claim on TAKT\n");
        }
    }
    gabbro_eintritt_zeitgeber_verteiler();
}
METALL_EINTRITT(zeitgeber, 1, takt_beobachtet())
METALL_EINTRITT(systemruf, 0, gabbro_eintritt_systemruf_verteiler())
#define RUNDEN 3000u
#define IPIS 600u
static void arbeiter(void)
{
    for (uint32_t i = 0; i < RUNDEN; i++) {
        takt_verteiler();
        __asm__ __volatile__("int $0x80" ::: "memory");
    }
}
static unsigned char st[3][65536] __attribute__((aligned(16)));
static uint32_t w[3];
int gabbro_metall_haupt(void)
{
    uint32_t n = metall_kerne();
    if (n < 2u) { metall_schreibe("59 braucht 2 Kerne\n"); return 1; }
    metall_idt_setze(gabbro_eintritt_zeitgeber_VEKTOR, gabbro_eintritt_zeitgeber);
    metall_idt_setze(gabbro_eintritt_systemruf_VEKTOR, gabbro_eintritt_systemruf);
    for (int i = 0; i < 3; i++) {
        if (gabbro_faden_start(arbeiter, st[i] + sizeof(st[i]), &w[i]) != 0) return 4;
    }
    /* One IPI at a time, and the next only once the handler has run: an IPI never meets
     * a pending one, so the count below is exact. */
    for (uint32_t i = 0; i < IPIS; i++) {
        uint32_t vorher = atomic_load_explicit(&metall_eintritt_zaehler_zeitgeber, memory_order_acquire);
        metall_ipi_fest(1u + i % (n - 1u), gabbro_eintritt_zeitgeber_VEKTOR);
        while (atomic_load_explicit(&metall_eintritt_zaehler_zeitgeber, memory_order_acquire) == vorher) {
            __asm__ __volatile__("pause" ::: "memory");
        }
    }
    for (int i = 0; i < 3; i++) gabbro_faden_warte(&w[i]);
    uint32_t e = atomic_load_explicit(&metall_eintritt_zaehler_zeitgeber, memory_order_acquire);
    uint32_t r = atomic_load_explicit(&metall_eintritt_zaehler_systemruf, memory_order_acquire);
    uint32_t v = atomic_load_explicit(&verletzt, memory_order_relaxed);
    metall_schreibe("59 eintritte "); metall_zahl(e);
    metall_schreibe(" systemrufe "); metall_zahl(r);
    metall_schreibe(" takt "); metall_zahl(Takte_speicher.slots[0].stand);
    metall_schreibe(" auftrag "); metall_zahl(Auftraege_speicher.slots[0].stand);
    metall_schreibe(" verletzt "); metall_zahl(v); metall_schreibe("\n");
    return (e == IPIS && r == 3u * RUNDEN && v == 0u) ? 0 : 1;
}
'
mkdir -p "$ARB/metall59" "$ARB/metall59-gift"
einheit metall59 "$W/beispiele/59-eintritt-nimmt-maskierte-sperre.gab"
cp "$ARB/metall59/einheit.c" "$ARB/metall59-gift/einheit.c"
printf '%s' "$TREIBER59" | sed 's/^SPERRE_TAKT$/METALL_SPERRE_MASKIERT(TAKT)/' > "$ARB/metall59/treiber.c"
# The gift: the same ticket lock WITHOUT the mask (the spelling `gift/460` refuses), holder
# tracked the same way so the handler can say where it landed before it hangs.
GIFT_TAKT='static metall_ticket gift_takt; static volatile uint8_t metall_anspruch_TAKT[METALL_KERNE_MAX]; void TAKT_nimm(void) { uint64_t f = metall_ia_aus(); metall_anspruch_TAKT[metall_kern_nr()] = 1u; metall_ia_her(f); metall_sperre_nimm(\&gift_takt); } void TAKT_gib(void) { metall_ticket_gib(\&gift_takt); uint64_t f = metall_ia_aus(); metall_anspruch_TAKT[metall_kern_nr()] = 0u; metall_ia_her(f); }'
printf '%s' "$TREIBER59" | sed "s/^SPERRE_TAKT\$/$GIFT_TAKT/" > "$ARB/metall59-gift/treiber.c"
grep -q 'gift_takt' "$ARB/metall59-gift/treiber.c" \
    || { echo "  metall59-gift: the mutation did not apply -- the gift would measure nothing"; exit 1; }

mkdir -p "$ARB/metall07"
einheit metall07 "$W/beispiele/07-eintritt-und-boot.gab"
: > "$ARB/metall07/fremd.ok"
cat > "$ARB/metall07/treiber.c" <<'C07'
#include "metall.h"
#include "einheit.c"
/* The program side of two foreign bodies (`extern fn` in the source). */
uint64_t syscall_verteiler(uint64_t nr, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3)
{
    return nr * 10000u + a0 * 1000u + a1 * 100u + a2 * 10u + a3;
}
static _Atomic uint32_t nmis;
void nmi_verteiler(void)
{
    atomic_fetch_add_explicit(&nmis, 1u, memory_order_release);
}
METALL_EINTRITT(syscall, 0, r->rax = (uint64_t)gabbro_eintritt_syscall_verteiler(r->rax, r->rdi, r->rsi, r->rdx, r->r10))
METALL_EINTRITT(nmi, 0, gabbro_eintritt_nmi_verteiler())
int gabbro_metall_haupt(void)
{
    metall_idt_setze(gabbro_eintritt_syscall_VEKTOR, gabbro_eintritt_syscall);
    metall_idt_setze(gabbro_eintritt_nmi_VEKTOR, gabbro_eintritt_nmi);
    register uint64_t a3 __asm__("r10") = 4;
    register uint64_t bx __asm__("rbx") = 0x5555u;
    register uint64_t r11 __asm__("r11") = 0x4321u;
    uint64_t rax = 7, rcx = 0x1234u;
    __asm__ __volatile__("int $0x80"
                         : "+a"(rax), "+c"(rcx), "+r"(r11), "+r"(bx)
                         : "D"((uint64_t)1), "S"((uint64_t)2), "d"((uint64_t)3), "r"(a3)
                         : "memory");
    metall_ipi_nmi(1u);
    while (atomic_load_explicit(&nmis, memory_order_acquire) == 0u) {
        __asm__ __volatile__("pause" ::: "memory");
    }
    metall_schreibe("07 syscall "); metall_zahl(rax);
    metall_schreibe(" erhalten "); metall_zahl(rcx == 0x1234u && r11 == 0x4321u && bx == 0x5555u);
    metall_schreibe(" nmi "); metall_zahl(atomic_load_explicit(&nmis, memory_order_acquire));
    metall_schreibe("\n");
    return rax == 71234u ? 0 : 1;
}
C07

# -- OFFEN O31 (Opus agent L): system calls bound for the bare-metal target. -----------
#   metall164  the program IS the kernel: 164's gate executes `int $0x80` into 164's own
#              `entry systemruf vector 0x80` (installed by the driver; the register binding
#              is the entry's: nr=rax a0=rdi a1=rsi a2=rdx -> ret=rax, `N561`-checked)
#   metall163  163 emitted with `--target metal`: the gate enters the RUNTIME's vector-0x80
#              slot, and the image's C kernel (`metall_systemruf` below) serves number 1 --
#              the text reaches the serial port through a real `int $0x80`
#   gifts      metall163-ohne-kern: the image supplies no kernel, and the first gate call
#              ends the machine (status 9) -- never an invented answer;
#              metall164-gift: the entry answers `len + 1`, and the count moves
mkdir -p "$ARB/metall164" "$ARB/metall164-gift" "$ARB/metall163" "$ARB/metall163-ohne-kern"
einheit metall164 "$W/beispiele/164-eigener-kern.gab"
einheit metall164-gift "$W/beispiele/164-eigener-kern.gab" 's/^    return len;$/    return len + 1u;/'
if cmp -s "$ARB/metall164/einheit.c" "$ARB/metall164-gift/einheit.c"; then
    echo "  metall164-gift: the mutation did not apply -- the gift would measure nothing"; exit 1
fi
TREIBER164='#include "metall.h"
#include "einheit.c"
METALL_EINTRITT(systemruf, 0, r->rax = (uint64_t)gabbro_eintritt_systemruf_verteiler(r->rax, r->rdi, r->rsi, r->rdx))
int gabbro_metall_haupt(void)
{
    metall_idt_setze(gabbro_eintritt_systemruf_VEKTOR, gabbro_eintritt_systemruf);
    uint64_t a = schreibe(1u, 3u);
    uint64_t b = schreibe(7u, 3u);
    metall_schreibe("164 schreibe "); metall_zahl(a);
    metall_schreibe(" badfd "); metall_zahl(b); metall_schreibe("\n");
    return (a == 3u && b == 900u) ? 0 : 1;
}
'
printf '%s' "$TREIBER164" > "$ARB/metall164/treiber.c"
printf '%s' "$TREIBER164" > "$ARB/metall164-gift/treiber.c"
export GABBRO_TARGET=metal
einheit metall163 "$W/beispiele/163-systemruf-variablen.gab"
einheit metall163-ohne-kern "$W/beispiele/163-systemruf-variablen.gab"
unset GABBRO_TARGET
if ! grep -q 'int \$0x80' "$ARB/metall163/einheit.c" || grep -q '"syscall' "$ARB/metall163/einheit.c"; then
    echo "  metall163: \`--target metal\` did not bind the gate to \`int \$0x80\`"; exit 1
fi
TREIBER163_HAUPT='int gabbro_metall_haupt(void)
{
    static const char text[] = "163 metal ok\n";
    uint32_t w = 0u, w2 = 0u;
    IoError g = IoError_Interrupted, g2 = IoError_Interrupted;
    bool ok = wiederholt_schreiben(1u, (uint64_t)text, 13u, 2u, &w, &g);
    bool ok2 = wiederholt_schreiben(7u, (uint64_t)text, 13u, 2u, &w2, &g2);
    metall_schreibe("163 geschrieben "); metall_zahl(ok ? w : 999u);
    metall_schreibe(" badfd "); metall_zahl(!ok2 && g2 == IoError_BadFd); metall_schreibe("\n");
    return (ok && w == 2u && !ok2 && g2 == IoError_BadFd) ? 0 : 1;
}
'
{
    printf '#include "metall.h"\n#include "einheit.c"\n'
    cat <<'C163'
/* The image's kernel (metall.h `metall_systemruf`): number 1 writes the frame to the serial
 * port for descriptor 1 and answers the count; another descriptor answers -EBADF, another
 * number -ENOSYS. The Linux x86_64 convention, as `metal_kernel_contract` names it. */
void metall_systemruf(struct metall_rahmen *r)
{
    if (r->rax != 1u) { r->rax = (uint64_t)(int64_t)-38; return; }
    if (r->rdi != 1u) { r->rax = (uint64_t)(int64_t)-9; return; }
    const char *p = (const char *)r->rsi;
    char puffer[64];
    uint64_t n = r->rdx < 63u ? r->rdx : 63u;
    for (uint64_t i = 0; i < n; i++) puffer[i] = p[i];
    puffer[n] = 0;
    metall_schreibe(puffer);
    r->rax = n;
}
C163
    printf '%s' "$TREIBER163_HAUPT"
} > "$ARB/metall163/treiber.c"
{ printf '#include "metall.h"\n#include "einheit.c"\n'; printf '%s' "$TREIBER163_HAUPT"; } \
    > "$ARB/metall163-ohne-kern/treiber.c"

# -- OFFEN O32 (9) (Opus agent L): an entry on an exception that pushes an error code. ----
#   metall165       165's `entry gp vector 13` through the twin stub (`METALL_EINTRITT_FC`,
#                   installed by `metall_idt_setze_fc`): three non-canonical loads raise
#                   #GP(0); the C half steps the 3-byte faulting load (`movq (%rax), %rax`)
#                   -- the one thing a dispatch cannot do -- and the run goes on
#   metall165-gift  the PLAIN stub on the same vector (installed through the fc installer so
#                   the build does not refuse it first): `iretq` takes the error code for the
#                   return address, and the machine never reports
mkdir -p "$ARB/metall165" "$ARB/metall165-gift"
einheit metall165 "$W/beispiele/165-gp-eintritt.gab"
einheit metall165-gift "$W/beispiele/165-gp-eintritt.gab"
TREIBER165_HAUPT='int gabbro_metall_haupt(void)
{
    metall_idt_setze_fc(gabbro_eintritt_gp_VEKTOR, gabbro_eintritt_gp);
    for (int i = 0; i < 3; i++) {
        uint64_t x = 0x8000000000000000ull;
        __asm__ __volatile__("movq (%%rax), %%rax" : "+a"(x) :: "memory");
    }
    uint32_t n = atomic_load_explicit(&metall_eintritt_zaehler_gp, memory_order_acquire);
    metall_schreibe("165 gp "); metall_zahl(n);
    metall_schreibe(" fehlercode "); metall_zahl(gp_code); metall_schreibe("\n");
    return (n == 3u && gp_code == 0u) ? 0 : 1;
}
'
{
    printf '#include "metall.h"\n#include "einheit.c"\nstatic volatile uint64_t gp_code = 99u;\n'
    printf 'METALL_EINTRITT_FC(gp, gabbro_eintritt_gp_verteiler(); gp_code = rf->fehlercode; rf->rip += 3u)\n'
    printf '%s' "$TREIBER165_HAUPT"
} > "$ARB/metall165/treiber.c"
{
    printf '#include "metall.h"\n#include "einheit.c"\nstatic volatile uint64_t gp_code = 99u;\n'
    printf 'METALL_EINTRITT(gp, 0, gabbro_eintritt_gp_verteiler(); ((struct metall_rahmen *)r)->rip += 3u)\n'
    printf '%s' "$TREIBER165_HAUPT"
} > "$ARB/metall165-gift/treiber.c"

# -- `gabbro build` links the image ITSELF (Opus agent J). A `metal <dir>` line in the
#    manifest makes the build compile `<unit>.metall.c` freestanding and link it with the
#    runtime into `<unit>.metall.elf` + `<unit>.metall.boot.elf`; the boot below takes that
#    artefact UNCHANGED (no harness driver, no observation block): 157's pool must start,
#    join and end with success on the declared distribution, and 59's entry-only driver must
#    install its two entries and end with success.
bau_bild() {  # bau_bild NAME SOURCE
    local d="$ARB/$1" out="$ARB/$1/out"
    mkdir -p "$d"
    printf 'compiler cc -std=c11 -O0 -Wall -Wextra -Werror\nout %s\nmetal %s\nunit einheit object\n    %s\n' \
        "$out" "$M" "$2" > "$d/bau"
    if ! G build "$d/bau" > "$d/bau.log" 2>&1; then
        echo "  $1: gabbro build FAILED"; sed 's/^/      /' "$d/bau.log" | head -10; exit 1
    fi
    [ -f "$out/einheit.metall.boot.elf" ] || { echo "  $1: gabbro build linked no image"; exit 1; }
    if nm "$out/einheit.metall.elf" | grep -E ' U |pthread|clone|futex' > "$d/nm.fund"; then
        echo "  $1: the built image is NOT FREESTANDING:"; cat "$d/nm.fund"; exit 1
    fi
    cp "$out/einheit.metall.boot.elf" "$d/k32.elf"
}
bau_bild bau157 "$W/beispiele/157-worker-pool.gab"
bau_bild bau59 "$W/beispiele/59-eintritt-nimmt-maskierte-sperre.gab"

# -- grenze: the core limit behind `gabbro_kern` (Opus agent J). A unit's `accumulates ...
#    per cpu N` indexes N cells with `gabbro_kern()`; the driver passes the smallest cell
#    count as `METALL_KERNE_GRENZE`, and the runtime must then bring up no more cores than
#    that, whatever the machine has. Measured with N = 2 on `-smp 4`: two cores check in,
#    and every thread's `gabbro_kern()` is below 2.
mkdir -p "$ARB/grenze"
cat > "$ARB/grenze/treiber.c" <<'CGRENZE'
#include "metall.h"
static _Atomic uint32_t zellen[2];
METALL_KERNE_GRENZE(METALL_MIN(METALL_KERNE_MAX, METALL_ZELLEN(zellen)))
uint32_t gabbro_kern(void);
static void zaehle(void) { atomic_fetch_add_explicit(&zellen[gabbro_kern()], 1u, memory_order_relaxed); }
static unsigned char st[6][16384] __attribute__((aligned(16)));
static uint32_t w[6];
int gabbro_metall_haupt(void)
{
    for (int i = 0; i < 6; i++) {
        if (gabbro_faden_start(zaehle, st[i] + sizeof(st[i]), &w[i]) != 0) return 4;
    }
    for (int i = 0; i < 6; i++) gabbro_faden_warte(&w[i]);
    uint32_t z = atomic_load_explicit(&zellen[0], memory_order_relaxed)
               + atomic_load_explicit(&zellen[1], memory_order_relaxed);
    metall_schreibe("grenze kerne "); metall_zahl(metall_kerne());
    metall_schreibe(" zellen "); metall_zahl(z); metall_schreibe("\n");
    return (metall_kerne() == 2u && z == 6u) ? 0 : 1;
}
CGRENZE

# -- Build everything (this half runs without qemu). ------------------------------------
for n in metall159 metall159-gift metall124 metall157 stress stress-gift staffel; do
    baue "$n" "" || exit 1
done
baue staffel-gift "-DMETALL_KOOPERATIV" || exit 1
# 154's emitted `buf[a]` warns at `-O2 -Werror` (`-Warray-bounds` after inlining `voll`), the
# emitter-idiom note of lane 242 that also keeps it out of the hosted runs; its driver is
# built at stage 9's `-O0`. The runtime keeps `-O2`.
baue metall153 "" || exit 1
baue metall154 "" "-O0" || exit 1
baue metall158 "" || exit 1
baue metall158-else "-DMETALL_ARENA_ZUSAGE=8" || exit 1
baue metall158-gift "" || exit 1
baue metall161 "" || exit 1
baue metall59 "" || exit 1
baue metall59-gift "" || exit 1
baue metall07 "" || exit 1
baue grenze "" || exit 1
for n in metall164 metall164-gift metall163 metall163-ohne-kern metall165 metall165-gift; do
    baue "$n" "" || exit 1
done
echo "  built and linked: 26 freestanding images + 2 linked by gabbro build (no libc, no undefined symbol, no pthread/clone/futex)"

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
pruefe metall153 "metall153 370"
pruefe metall154 "metall154 1004"
pruefe metall158 "metall158 118"
pruefe metall158-else "metall158-else 1"
pruefe metall161 "161 2 104 105 2 3 104 105 33 1 0 1 0"
pruefe metall59 "59 eintritte 600 systemrufe 9000 takt 1 auftrag 1 verletzt 0" "METALL-VERTEILUNG 0 1 1 1"
pruefe metall07 "07 syscall 71234 erhalten 1 nmi 1"
pruefe bau157 "METALL-VERTEILUNG 0 1 1 0"
pruefe bau59 "METALL-VERTEILUNG 0 0 0 0"
pruefe grenze "METALL-KERNE 2" "grenze kerne 2 zellen 6"
pruefe metall164 "164 schreibe 3 badfd 900"
pruefe metall163 "163 metal ok" "163 geschrieben 2 badfd 1"
gift metall164-gift "the program's own kernel entry answers len + 1: the count moves"
pruefe metall165 "165 gp 3 fehlercode 0"
METALL_ZEIT=20 gift metall165-gift "the plain stub on an error-code vector: iretq takes the code for the return address"
gift metall163-ohne-kern "no kernel in the image: the first gate call ends the machine (status 9)"
if ! grep -q "entered through vector 0x80, and the image supplies no kernel service" "$ARB/metall163-ohne-kern/serial.log"; then
    echo "  metall163-ohne-kern: it did not end in success, but not for the named reason"
    BEFUND=1
fi
gift metall158-gift "stored value 17 -> 18: the sum moves to 119"
METALL_ZEIT=30 gift metall59-gift "TAKT unmasked: an entry lands on a core with a claim on TAKT (ticket drawn or held) and waits behind the thread it interrupted"
# ... and it bites for the NAMED reason, not for any hang: the handler reported where it
# landed before it stopped.
if ! grep -qxF "59 an entry landed on a core with a claim on TAKT" "$ARB/metall59-gift/serial.log"; then
    echo "  metall59-gift: it did not end in success, but the handler never reported landing on"
    echo "  the holder's core -- the hang is not the one the gift names"
    BEFUND=1
fi

if [ "$BEFUND" != 0 ]; then
    echo "== METALL: FINDING (see above) =="
    exit 1
fi
echo "== METALL: $N_GEBOOTET booted on qemu -smp 4, every expectation held, 8 gifts bite =="
