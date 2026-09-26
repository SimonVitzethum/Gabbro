#!/usr/bin/env bash
# instrumente/pruefe-freistehend.sh -- EVERY emitting unit, compiled and LINKED without an OS
# (Opus agent J, 2026-09-26; stage 12 of `pruefe-emission.sh`, runnable alone).
#
# SIMON'S RULE (2026-09-26): everything Gabbro can do must work FREESTANDING, without an OS --
# Gabbro exists for the Caprock microkernel. Stage 9 asks "does every emitting unit compile?"
# with the HOST's compiler and headers; stage 11 (`pruefe-metall.sh`) boots a handful of
# chosen units on bare metal. This stage asks the question between them, over the SAME
# population as stage 9 (every tracked `.gab` that emits, all roots):
#
#   does the emitted C compile with NO hosted header, and does it LINK into the bare-metal
#   image (`laufzeit/metall/`) with NO C library -- and if it needs something from outside,
#   WHAT, named and classified, never skipped?
#
# THE RECIPE, per unit:
#   1. compile the unit INSIDE a generated link driver (the unit's roots are `static`, exactly
#      as with the hosted and bare-metal drivers) with `-ffreestanding -fno-builtin -nostdlib
#      -nostdinc`: the compiler's own headers (C11's freestanding set) plus
#      `laufzeit/metall/include/` -- the two hosted headers the emitter writes (<math.h>,
#      <string.h>), reduced to exactly what the emitter uses. `-O0`: stage 9's level, and the
#      level at which every `static` body is kept, so every call the unit can make reaches
#      the linker (measured: the `-O2` undefined-symbol set is a SUBSET of the `-O0` one over
#      all 311 units, 194 against 212 names, and adds no compiler-emitted helper).
#   2. `nm -u` the driver object and CLASSIFY every undefined symbol:
#        runtime   defined by the bare-metal runtime (`kern.c`, `arena.c`, `start.S`):
#                  the thread interface, `memcpy`/`memset`/`memmove`/`memcmp`, the arena
#        lock      `L_nimm`/`L_gib` (+ `_geteilt`) of a `lock L` the source declares -- the
#                  driver defines it (`METALL_SPERRE`, `_GETEILT`, `_MASKIERT` for
#                  `masks irqs`), as `gabbro build`'s `<unit>.metall.c` does
#        rcu       `R_lese_start`/`R_lese_ende` of an `rcu R` -- `METALL_RCU`
#        entry     `gabbro_eintritt_E` of an `entry E` -- `METALL_EINTRITT`: the stub the
#                  emitter declares and never defines, installed in the metal IDT
#        foreign   a name the source declares `extern fn`: the PROGRAM supplies its body
#                  (its own C, Caprock's). The link driver gives each one a trap stub that
#                  says so if it is ever called -- the link then proves that nothing ELSE is
#                  missing. A foreign name that is a C-library or POSIX function is the
#                  program binding to a hosted library by its own choice: HOSTED-ONLY (b).
#        anything else: UNCLASSIFIED -- a finding.
#   3. link: `ld -nostdlib -static -T metall.ld` over start.o kern.o arena.o, the driver and
#      the foreign stubs. `ld` refuses an undefined symbol, so a linked image IS the proof.
#
# HOSTED-ONLY, NAMED, NEVER SKIPPED. A unit that links freestanding can still be a program
# for an OS:
#   (a) KERNEL GATE -- its C executes a `syscall` instruction (a `syscall` item with
#       `abi linux`, or the program's own `asm`): the other side of that instruction is a
#       kernel. On bare metal the program IS the kernel; there is nothing to call.
#   (b) HOSTED FOREIGN NAME -- an `extern fn` bound to a C-library/POSIX name.
# And the hosted RUNTIME files are named with their bare-metal counterpart (the table at the
# end). OFFEN O32 carries the list.
#
# BOUND FOR THE METAL TARGET (OFFEN O31, Opus agent L). A unit whose gates call through
# system-call variables and that carries a `target T abi metal …` block is emitted with
# `--target T`: its gates execute `int $0x80` into the image's kernel entry (vector 0x80 of
# the runtime, served by the image's `metall_systemruf`, or by the unit's OWN `entry …
# vector 0x80`). Such a unit is listed with the numbers it calls, and it is NOT hosted-only:
# the other side of its gates is inside the image. Stage 11 boots both shapes
# (`metall163`, `metall164`).
#
# QEMU is not needed here: this stage links; `pruefe-metall.sh` boots. Missing `cc`/`ld`/`nm`
# prints `FREESTANDING: NOT RUN` -- never a pass line.
#
# USAGE
#   instrumente/pruefe-freistehend.sh [WORKDIR]
#   GABBRO_BIN=target/debug/gabbro instrumente/pruefe-freistehend.sh
# Exit 0 = every emitting unit compiles and links freestanding and every symbol is
# classified; 1 = a finding (listed).
set -uo pipefail

W="$(cd "$(dirname "$0")/.." && pwd)"
M="$W/laufzeit/metall"
ARB="${1:-$W/.tmp/freistehend}"
mkdir -p "$ARB"

G() {
    if [ -n "${GABBRO_BIN:-}" ]; then "$GABBRO_BIN" "$@"
    else cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- "$@"; fi
}

echo "== Stufe 12: freestanding -- every emitting unit compiles and LINKS without an OS =="

for t in cc ld nm; do
    if ! command -v "$t" > /dev/null; then
        echo "  FREESTANDING: NOT RUN -- \`$t\` missing; nothing was compiled, nothing was linked."
        exit 0
    fi
done

GCCINC="$(cc -print-file-name=include)"
if [ ! -f "$GCCINC/stdint.h" ] || [ ! -f "$GCCINC/stdatomic.h" ]; then
    echo "  FREESTANDING: NOT RUN -- the compiler's own header directory ($GCCINC) lacks"
    echo "  <stdint.h>/<stdatomic.h>; -nostdinc would measure the toolchain, not the units."
    exit 0
fi

# The flag word of the bare-metal image (`pruefe-metall.sh`), plus -nostdinc and stage 9's -O0.
CF="-std=c11 -O0 -ffreestanding -fno-builtin -nostdlib -nostdinc -isystem $GCCINC -isystem $M/include
    -fno-pic -fno-pie -mno-red-zone -mcmodel=small -fno-stack-protector
    -fno-asynchronous-unwind-tables -Wall -Wextra -Werror"
CFR="-std=c11 -O2 -ffreestanding -fno-builtin -nostdlib -nostdinc -isystem $GCCINC -isystem $M/include
    -fno-pic -fno-pie -mno-red-zone -mcmodel=small -fno-stack-protector
    -fno-asynchronous-unwind-tables -fno-tree-loop-distribute-patterns -Wall -Wextra -Werror"

# -- The runtime, once. -------------------------------------------------------------------
mkdir -p "$ARB/rt"
# shellcheck disable=SC2086
if ! { cc $CFR -c "$M/kern.c" -o "$ARB/rt/kern.o" \
       && cc $CFR -c "$M/arena.c" -o "$ARB/rt/arena.o" \
       && cc -fno-pie -c "$M/start.S" -o "$ARB/rt/start.o"; } 2> "$ARB/rt/cc.err"; then
    echo "  RUNTIME DOES NOT BUILD:"; head -20 "$ARB/rt/cc.err"; exit 1
fi
nm --defined-only "$ARB/rt/kern.o" "$ARB/rt/arena.o" "$ARB/rt/start.o" 2>/dev/null \
    | awk 'NF == 3 && $2 ~ /[TDBR]/ {print $3}' | sort -u > "$ARB/rt/definiert"

# -- Sprechprobe: can this stage FALL? Two planted units, one per question it asks. -------
#   (1) a hosted header must not compile under the stage's flag word (-nostdinc works);
#   (2) a call into the C library that nobody supplies must not link (`ld` refuses).
# Either one passing means the stage measures nothing, and it says so with exit 2.
mkdir -p "$ARB/sprech"
printf '#include <stdio.h>\nint sprech_eins(void) { return 1; }\n' > "$ARB/sprech/kopf.c"
# shellcheck disable=SC2086
if cc $CF -c "$ARB/sprech/kopf.c" -o "$ARB/sprech/kopf.o" 2> /dev/null; then
    echo "  Sprechprobe 1: GESCHEITERT -- <stdio.h> compiles under -nostdinc; the header half measures nothing"
    exit 2
fi
printf '#include "metall.h"\nint puts(const char *s);\nint gabbro_metall_haupt(void) { return puts("x"); }\n' \
    > "$ARB/sprech/libc.c"
# shellcheck disable=SC2086
cc $CF -I"$M" -c "$ARB/sprech/libc.c" -o "$ARB/sprech/libc.o" || exit 2
if ld -nostdlib -static -no-pie -T "$M/metall.ld" -z max-page-size=0x1000 -o "$ARB/sprech/k.elf" \
        "$ARB/rt/start.o" "$ARB/rt/kern.o" "$ARB/rt/arena.o" "$ARB/sprech/libc.o" 2> /dev/null; then
    echo "  Sprechprobe 2: GESCHEITERT -- a call to \`puts\` links; the link half measures nothing"
    exit 2
fi
echo "  Sprechprobe: ok (<stdio.h> does not compile, an unsupplied \`puts\` does not link)"

# C library and POSIX names a program's `extern fn` might bind to. The list is the question
# "would this link against libc on a hosted system?" -- it only labels, it never admits:
# a foreign name outside it is still the program's own body, a foreign name inside it is
# still a stub here, and the unit is listed HOSTED-ONLY (b).
LIBC_NAMEN=" abort abs accept atexit atof atoi bind calloc close connect exit fclose fopen \
fprintf fputs fread free fwrite getchar getenv getpid ioctl kill listen lseek malloc memchr \
mmap mprotect munmap open pause perror printf pthread_create pthread_join pthread_self \
pthread_mutex_lock pthread_mutex_unlock putchar puts raise read realloc recv send shutdown \
signal socket sprintf snprintf sqrt sqrtf strcmp strcpy strlen strncmp time usleep write \
cos sin tan exp log pow floor ceil fabs fmod "

# -- The population: stage 9's list, byte for byte (tracked `.gab`, same prunes). --------
GAB_GEFUNDEN="$(find "$W" \( -name target -o -name .claude -o -name .lake \
                          -o -name arbeitsprotokoll \) -prune \
                    -o -name '*.gab' -print | sort)"
if GAB_VERFOLGT="$(git -C "$W" ls-files -z -- '*.gab' 2>/dev/null \
                        | tr '\0' '\n' | sed "s#^#$W/#" | sort)" \
        && [ -n "$GAB_VERFOLGT" ]; then
    LISTE="$(comm -12 <(printf '%s\n' "$GAB_GEFUNDEN") <(printf '%s\n' "$GAB_VERFOLGT"))"
else
    echo "pruefe-freistehend.sh: \`git ls-files\` failed under $W -- directory blacklist only" >&2
    LISTE="$GAB_GEFUNDEN"
fi

n_emit=0; n_umg=0; n_ok=0; befund=0
n_kl_rt=0; n_kl_sperre=0; n_kl_rcu=0; n_kl_eintritt=0; n_kl_fremd=0
n_fremd_einheiten=0; n_rein=0
gate_liste=""; libc_liste=""; umg_bericht=""; bindung_liste=""; metall_liste=""
: > "$ARB/einheiten.txt"

while IFS= read -r q; do
    [ -n "$q" ] || continue
    d="${q#"$W"/}"
    k="$(printf '%s' "$d" | tr '/' '_')"
    e="$ARB/u/$k"
    mkdir -p "$e"
    # **OFFEN O31 (Opus agent L): a unit that binds its gates for the bare-metal target is
    # emitted FOR it** (`--target`, the name of its `target … abi metal` block): the gates
    # then enter the image's kernel through `int $0x80` instead of calling Linux.
    metallziel="$(sed -n 's/^[[:space:]]*target[[:space:]]\{1,\}\([A-Za-z_][A-Za-z0-9_]*\)[[:space:]]\{1,\}abi[[:space:]]\{1,\}metal[[:space:]].*/\1/p' "$q" | head -1)"
    # The population stays stage 9's: a unit whose DEFAULT build refuses (a gift) is not
    # in it, whatever another target would do.
    if ! G emit "$q" > "$e/einheit.c" 2>/dev/null || [ ! -s "$e/einheit.c" ]; then
        rm -rf "$e"; continue          # `C001` -- a refusal is an honest answer (stage 9)
    fi
    if [ -n "$metallziel" ]; then
        if ! GABBRO_TARGET="$metallziel" G emit "$q" > "$e/einheit.c" 2>/dev/null || [ ! -s "$e/einheit.c" ]; then
            echo "  THE METAL TARGET DOES NOT EMIT: $d (target $metallziel)"
            befund=1; rm -rf "$e"; continue
        fi
    fi
    n_emit=$((n_emit + 1))
    # A `-- erwartet: cc` probe bites a HOSTED C rule (stage 9 keeps it reversed). It is
    # not a unit of this population; its freestanding verdict is reported, not judged.
    if [ "$(head -1 "$q")" = "-- erwartet: cc" ]; then
        n_umg=$((n_umg + 1))
        # shellcheck disable=SC2086
        if cc $CF -c "$e/einheit.c" -o /dev/null 2> "$e/cc.err"; then
            umg_bericht="$umg_bericht\n    $d -- compiles freestanding (its bite is a hosted rule: $(grep -m1 -oE '\[-W[a-z=-]+\]' <(cc -std=c11 -Wall -Wextra -Werror -c "$e/einheit.c" -o /dev/null 2>&1) || echo '?'))"
        else
            umg_bericht="$umg_bericht\n    $d -- still falls freestanding"
        fi
        continue
    fi

    # 1. Compile inside a driver: first the unit alone, for the symbol census.
    printf '#include "metall.h"\n#include "einheit.c"\n' > "$e/drv0.c"
    # shellcheck disable=SC2086
    if ! cc $CF -I"$M" -I"$e" -c "$e/drv0.c" -o "$e/drv0.o" 2> "$e/cc.err"; then
        echo "  DOES NOT COMPILE FREESTANDING: $d"
        grep -m3 -E 'error|Fehler' "$e/cc.err" | sed 's/^/      /'
        befund=1; continue
    fi

    # 2. Classify every undefined symbol.
    sperren=""; rcus=""; eintritte=""; fremde=""; offen=""
    while IFS= read -r s; do
        [ -n "$s" ] || continue
        if grep -qxF "$s" "$ARB/rt/definiert"; then
            n_kl_rt=$((n_kl_rt + 1)); continue
        fi
        case "$s" in
        *_nimm_geteilt|*_gib_geteilt|*_nimm|*_gib)
            p="${s%_geteilt}"; p="${p%_nimm}"; p="${p%_gib}"
            if grep -qE "^[[:space:]]*(pub[[:space:]]+)?lock[[:space:]]+$p([[:space:]]|$)" "$q"; then
                n_kl_sperre=$((n_kl_sperre + 1))
                case " $sperren " in *" $p "*) ;; *) sperren="$sperren $p" ;; esac
                continue
            fi ;;
        *_lese_start|*_lese_ende)
            p="${s%_lese_start}"; p="${p%_lese_ende}"
            if grep -qE "^[[:space:]]*(pub[[:space:]]+)?rcu[[:space:]]+$p([[:space:]]|$)" "$q"; then
                n_kl_rcu=$((n_kl_rcu + 1))
                case " $rcus " in *" $p "*) ;; *) rcus="$rcus $p" ;; esac
                continue
            fi ;;
        esac
        if grep -qE "^[[:space:]]*(pub[[:space:]]+)?extern[[:space:]]+fn[[:space:]]+$s[[:space:]]*\(" "$q"; then
            n_kl_fremd=$((n_kl_fremd + 1))
            fremde="$fremde $s"
            continue
        fi
        offen="$offen $s"
    done < <(nm -u "$e/drv0.o" | awk '{print $2}')
    if [ -n "$offen" ]; then
        echo "  UNCLASSIFIED SYMBOL(S) in $d:$offen"
        befund=1; continue
    fi
    # Entries are read off the emitted C, not off `nm`: the unit only DECLARES the stub
    # (nobody in the unit calls it -- hardware does), so it is never an undefined symbol,
    # and an image without it would simply lack the handler. Every declared entry gets its
    # stub and its IDT slot here.
    eintritte="$(sed -n 's#^/\* entry \([A-Za-z_][A-Za-z0-9_]*\) -- arch x86_64.*#\1#p' "$e/einheit.c" | tr '\n' ' ')"
    for p in $eintritte; do n_kl_eintritt=$((n_kl_eintritt + 1)); done
    fc_liste=""
    if sed -n 's#^/\* entry [A-Za-z0-9_]* -- arch \([a-z0-9_]*\).*#\1#p' "$e/einheit.c" | grep -qv '^x86_64$'; then
        echo "  ENTRY FOR ANOTHER ARCH in $d -- the metal runtime is x86_64 only"
        befund=1; continue
    fi

    # The link driver: the unit, its locks, rcu domains and entries, and a haupt that
    # installs every entry in the IDT (so the image carries the handlers it would run).
    {
        printf '#include "metall.h"\n#include "einheit.c"\n'
        for p in $sperren; do
            if grep -qE "^[[:space:]]*(pub[[:space:]]+)?lock[[:space:]]+$p[[:space:]].*masks[[:space:]]+irqs" "$q"; then
                if nm -u "$e/drv0.o" | grep -qw "${p}_nimm_geteilt"; then
                    printf 'METALL_SPERRE_MASKIERT_GETEILT(%s)\n' "$p"
                else
                    printf 'METALL_SPERRE_MASKIERT(%s)\n' "$p"
                fi
            elif nm -u "$e/drv0.o" | grep -qw "${p}_nimm_geteilt"; then
                printf 'METALL_SPERRE_GETEILT(%s)\n' "$p"
            else
                printf 'METALL_SPERRE(%s)\n' "$p"
            fi
        done
        for p in $rcus; do printf 'METALL_RCU(%s)\n' "$p"; done
        # `gabbro_kern` (runtime) answers below the cores the image brings up; the driver
        # caps them at the SMALLEST per-cpu cell count of the unit (certificate section E:
        # "below the `per cpu` count"), read off the arrays by the compiler.
        grenze="METALL_KERNE_MAX"
        for z in $(sed -n 's/^ *static _Atomic [a-z0-9_]* \([A-Za-z_][A-Za-z0-9_]*_zellen\)\[.*/\1/p' "$e/einheit.c" | sort -u); do
            grenze="METALL_MIN($grenze, METALL_ZELLEN($z))"
        done
        [ "$grenze" != "METALL_KERNE_MAX" ] && printf 'METALL_KERNE_GRENZE(%s)\n' "$grenze"
        for p in $eintritte; do
            # The entry's comment block names its register binding
            # (` * regs in : nr=rax a0=rdi`, ` * regs out: ret=rax`); the C half passes the
            # `regs in` registers in order and stores the result into the `regs out` one.
            block="$(awk -v n="$p" '$0 ~ "^/\\* entry " n " -- arch" {on=1} on {print} on && /\*\// {exit}' "$e/einheit.c")"
            ein="$(printf '%s\n' "$block" | sed -n 's/^ \* regs in : //p' | tr ' ' '\n' | sed -n 's/^[A-Za-z_0-9]*=\([a-z0-9]*\)$/r->\1/p' | paste -sd, -)"
            aus="$(printf '%s\n' "$block" | sed -n 's/^ \* regs out: //p' | tr ' ' '\n' | sed -n 's/^[A-Za-z_0-9]*=\([a-z0-9]*\)$/\1/p')"
            n_aus="$(printf '%s' "$aus" | grep -c . || true)"
            # The dispatch reference exists only when the target is declared in the unit
            # (`erzeugernamen.rs`); without it the stub has nothing to run and ends loudly.
            n_ein="$(printf '%s' "$ein" | tr ',' '\n' | grep -c . || true)"
            sig="$(sed -n "s/^static \(.*\) (\*const gabbro_eintritt_${p}_verteiler)(\(.*\)) __attribute__.*/\1|\2/p" "$e/einheit.c")"
            if [ -n "$sig" ]; then
                s_ret="${sig%%|*}"; s_par="${sig#*|}"
                if [ "$s_par" = "void" ]; then s_n=0; else s_n=$(( $(printf '%s' "$s_par" | tr -cd ',' | wc -c) + 1 )); fi
                if [ "$s_ret" = "void" ]; then s_aus=0; else s_aus=1; fi
                if [ "$s_n" = "$n_ein" ] && { [ "$s_aus" = "$n_aus" ] || [ "$n_aus" = 0 ]; }; then   # an answer with no out register is dropped (N561)
                    ruf="gabbro_eintritt_${p}_verteiler($ein)"
                    if [ "$n_aus" = 1 ]; then ruf="r->$aus = (uint64_t)$ruf"; fi
                else
                    # The declared registers do not match the dispatch's signature: there
                    # is no honest binding. The stub ends the machine if entered -- it
                    # never guesses which register feeds which parameter.
                    ruf="metall_eintritt_bindung_falsch()"
                    bindung_liste="$bindung_liste\n    $d -- entry $p: regs in $n_ein / out $n_aus, dispatch takes $s_n / returns $s_aus"
                fi
            elif grep -q "gabbro_eintritt_${p}_verteiler" "$e/einheit.c"; then
                echo "  ENTRY SIGNATURE UNREADABLE in $d ($p) -- the stub cannot bind it" >&2
                ruf="metall_eintritt_bindung_falsch()"
                bindung_liste="$bindung_liste\n    $d -- entry $p: dispatch signature not readable"
            else
                ruf="metall_eintritt_ohne_ziel()"
            fi
            # EOI only for a LAPIC-delivered interrupt: `via idt` at a vector >= 32. A CPU
            # exception or an NMI (vector 2) is acknowledged by `iretq` alone.
            geworfen=0
            vek="$(printf '%s\n' "$block" | sed -n 's/^ \* vector \([0-9]*\)$/\1/p')"
            if printf '%s\n' "$block" | head -1 | grep -q ', via idt' && [ -n "$vek" ] && [ "$vek" -ge 32 ]; then
                geworfen=1
            fi
            # OFFEN O32 (9): an exception that pushes a CPU error code takes the twin stub.
            case " 8 10 11 12 13 14 17 21 29 30 " in
            *" $vek "*) printf 'METALL_EINTRITT_FC(%s, %s)\n' "$p" "$ruf"; fc_liste="$fc_liste $p" ;;
            *) printf 'METALL_EINTRITT(%s, %s, %s)\n' "$p" "$geworfen" "$ruf" ;;
            esac
        done
        printf 'int gabbro_metall_haupt(void)\n{\n'
        for p in $eintritte; do
            if grep -q "gabbro_eintritt_${p}_VEKTOR" "$e/einheit.c"; then
                case " $fc_liste " in
                *" $p "*) setze=metall_idt_setze_fc ;;
                *) setze=metall_idt_setze ;;
                esac
                printf '    %s(gabbro_eintritt_%s_VEKTOR, gabbro_eintritt_%s);\n' "$setze" "$p" "$p"
            fi
        done
        printf '    return 0;\n}\n'
    } > "$e/drv.c"
    : > "$e/fremd.S"
    for s in $fremde; do
        printf '\t.text\n\t.global %s\n%s:\n\tmovq $%s_name, %%rdi\n\tjmp metall_fremd_fehlt\n\t.section .rodata\n%s_name:\n\t.asciz "%s"\n' \
            "$s" "$s" "$s" "$s" "$s" >> "$e/fremd.S"
    done
    # shellcheck disable=SC2086
    if ! { cc $CF -I"$M" -I"$e" -c "$e/drv.c" -o "$e/drv.o" \
           && cc -fno-pie -c "$e/fremd.S" -o "$e/fremd.o" \
           && ld -nostdlib -static -no-pie -T "$M/metall.ld" -z max-page-size=0x1000 \
                 -o "$e/k.elf" "$ARB/rt/start.o" "$ARB/rt/kern.o" "$ARB/rt/arena.o" \
                 "$e/drv.o" "$e/fremd.o"; } 2> "$e/ld.err"; then
        echo "  DOES NOT LINK FREESTANDING: $d"
        grep -m4 -E 'error|Fehler|undefined|nicht definiert' "$e/ld.err" | sed 's/^/      /'
        befund=1; continue
    fi
    n_ok=$((n_ok + 1))

    # 4. Hosted-only, named.
    klasse="clean"
    # O31: gates bound for the metal target enter the image's kernel (`int $0x80`, the
    # runtime's vector-0x80 slot). With the unit's OWN `entry … vector 0x80` the program is
    # that kernel; without it the image's kernel -- Caprock, or a C `metall_systemruf` --
    # serves the numbers. Neither is hosted: nothing outside the image stands behind them.
    if [ -n "$metallziel" ] && grep -q '"int \$0x80' "$e/einheit.c"; then
        nummern="$(grep -o 'number [0-9]* in rax' "$e/einheit.c" | awk '{print $2}' | sort -un | paste -sd, -)"
        if grep -q 'gabbro_eintritt_[A-Za-z0-9_]*_VEKTOR 128u' "$e/einheit.c"; then
            metall_liste="$metall_liste\n    $d -- target $metallziel, numbers {$nummern}, served by the program's own entry at 0x80"
        else
            metall_liste="$metall_liste\n    $d -- target $metallziel, numbers {$nummern}, served by the image's kernel (metall_systemruf)"
        fi
        klasse="metal-gate"
    fi
    if grep -qE '"syscall(\\n|\\t|")' "$e/einheit.c"; then
        if grep -qE '^[[:space:]]*abi[[:space:]]+linux' "$q"; then
            gate_liste="$gate_liste\n    $d -- syscall item, abi linux"
        else
            gate_liste="$gate_liste\n    $d -- the program's own asm executes \`syscall\`"
        fi
        klasse="hosted-gate"
    fi
    hosted_namen=""
    for s in $fremde; do
        case "$LIBC_NAMEN" in *" $s "*) hosted_namen="$hosted_namen $s" ;; esac
    done
    if [ -n "$hosted_namen" ]; then
        libc_liste="$libc_liste\n    $d --$hosted_namen"
        klasse="hosted-libc"
    fi
    [ -n "$fremde" ] && n_fremd_einheiten=$((n_fremd_einheiten + 1))
    if { [ "$klasse" = "clean" ] || [ "$klasse" = "metal-gate" ]; } && [ -z "$fremde" ]; then n_rein=$((n_rein + 1)); fi
    printf '%s %s locks=[%s] rcu=[%s] entries=[%s] foreign=[%s]\n' "$klasse" "$d" \
        "${sperren# }" "${rcus# }" "${eintritte# }" "${fremde# }" >> "$ARB/einheiten.txt"
done < <([ -z "$LISTE" ] || printf '%s\n' "$LISTE")

n_nenner=$((n_emit - n_umg))
n_gate=$(printf '%b' "$gate_liste" | grep -c . || true)
n_libc=$(printf '%b' "$libc_liste" | grep -c . || true)
echo "  $n_ok of $n_nenner emitting units compile AND link freestanding (no hosted header, no libc,"
echo "  \`ld\` refuses an undefined symbol); $n_umg reverse probes (\`-- erwartet: cc\`) set aside"
echo "  symbols classified: $n_kl_rt runtime, $n_kl_sperre lock, $n_kl_rcu rcu, $n_kl_eintritt entry, $n_kl_fremd foreign"
echo "  $n_rein units need nothing but the runtime; $n_fremd_einheiten name foreign bodies the program supplies"
if [ -n "$umg_bericht" ]; then
    echo "  reverse probes, measured freestanding:"
    printf '%b\n' "$umg_bericht" | sed '/^$/d'
fi
n_metall=$(printf '%b' "$metall_liste" | grep -c . || true)
echo "  BOUND FOR THE BARE-METAL TARGET (OFFEN O31), $n_metall unit(s): emitted with --target, the"
echo "  gates enter the image's kernel through int \$0x80 -- NOT hosted-only:"
printf '%b\n' "$metall_liste" | sed '/^$/d'
echo "  HOSTED-ONLY (a) -- KERNEL GATE, $n_gate unit(s): links freestanding; running needs a kernel"
echo "  on the other side of \`syscall\` (OFFEN O31/O32):"
printf '%b\n' "$gate_liste" | sed '/^$/d'
echo "  HOSTED-ONLY (b) -- FOREIGN NAME OF A HOSTED LIBRARY, $n_libc unit(s): the program binds"
echo "  a C-library/POSIX function by its own choice; the feature (\`extern fn\`) is freestanding:"
printf '%b\n' "$libc_liste" | sed '/^$/d'
n_bindung=$(printf '%b' "$bindung_liste" | grep -c . || true)
echo "  ENTRY BINDING MISMATCH, $n_bindung entr(y/ies): the declared \`regs in\`/\`regs out\` are not the"
echo "  dispatch's parameters/result, so no stub can bind them honestly; the image links, and the"
echo "  stub ends the machine if the entry is ever taken (since Opus agent L the checker refuses"
echo "  the shape at check time, N561 -- a unit listed here was emitted without the checker):"
printf '%b\n' "$bindung_liste" | sed '/^$/d'
echo "  HOSTED-ONLY runtime files, each with its bare-metal counterpart:"
echo "    laufzeit/faden.c       raw Linux clone/futex      -> laufzeit/metall/kern.c (gabbro_faden_*)"
echo "    laufzeit/start.c       pthreads + printf (boot)   -> <unit>.metall.c (gabbro build)"
echo "    laufzeit/start_pool.c  pthreads (pool boot)       -> <unit>.metall.c (gabbro build)"
echo "    laufzeit/arena_dyn.c   mmap/mprotect              -> laufzeit/metall/arena.c"
echo "    <unit>.treiber.c       pthreads (generated)       -> <unit>.metall.c (generated)"

if [ "$befund" != 0 ] || [ "$n_ok" != "$n_nenner" ]; then
    echo "== FREESTANDING: FINDING (see above) =="
    exit 1
fi
echo "== FREESTANDING: $n_ok of $n_nenner link without an OS; $n_metall bound for the metal target; $((n_gate + n_libc)) hosted-only listed by name =="
