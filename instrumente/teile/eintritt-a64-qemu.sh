#!/bin/bash
# eintritt-a64-qemu.sh -- die aarch64-Eintritte (`entry ... arch aarch64`) AUSFUEHREN, unter
# `qemu-system-aarch64 -M virt` auf EL1 (nicht im Benutzermodus: `eret` und `mrs elr_el1` sind dort ein Trap).
#
#   messung/llvm/eintritt-a64.gab --gabbro llvm--> IR --opt/llc--> Objekt
#   + Pruefstand (handgeschriebenes Assembler, NUR Apparat: Stapel, CPACR, VBAR_EL1, zwei `svc`, Pruefung,
#     Semihosting-Ende) --ld.lld--> ELF --qemu-system-aarch64--> Exit-Code
#
# Der Pruefstand ist der EINZIGE handgeschriebene Teil und gehoert nicht zum Erzeugnis: er schreibt VBAR_EL1
# (was der Erzeuger ausdruecklich NICHT tut), setzt Stapel und CPACR und bewertet das Ergebnis. Was er prueft:
#   Platz 4 (SPx, sync):  svc -> Stub -> verteiler_vier(41) -> x0 = 42, eret kehrt hinter den svc zurueck;
#   Platz 0 (SP0, sync):  nach `msr spsel,#0` ein svc -> Stub -> verteiler_null(42) -> x0 = 142;
#   callee-saved x19/x20, x30 bleiben, ebenso das gerettete SPSR (SPSel kommt zurueck) und das FPSR-Muster.
# Exit 0 = alles gehalten, sonst die Nummer der gefallenen Pruefung (1..6). Exit 2 = nicht messbar (Werkzeug fehlt).
set -u
W="$(cd "$(dirname "$0")/../.." && pwd)"
GABBRO="$W/target/debug/gabbro"
TLS="${TLS:-$W/.tmp/eintritt-a64}"
mkdir -p "$TLS"
for w in opt llc ld.lld llvm-mc qemu-system-aarch64 llvm-objdump; do
    command -v "$w" >/dev/null || { echo "eintritt-a64: $w fehlt -- NICHT GEMESSEN" >&2; exit 2; }
done
[ -x "$GABBRO" ] || { echo "eintritt-a64: $GABBRO fehlt (cargo build -p gabbro-cli)" >&2; exit 2; }

"$GABBRO" llvm --target=aarch64 "$W/messung/llvm/eintritt-a64.gab" >"$TLS/e.ll" || { echo "ROT: Erzeuger"; exit 1; }
opt -O3 "$TLS/e.ll" -o "$TLS/e.bc" || { echo "ROT: opt"; exit 1; }
llc -O3 -mtriple=aarch64-unknown-linux-gnu -filetype=obj "$TLS/e.bc" -o "$TLS/e.o" || { echo "ROT: llc"; exit 1; }

cat >"$TLS/stand.S" <<'EOF'
    .section .text.start,"ax"
    .globl _start
_start:
    ldr  x0, =stapel_el1_oben
    mov  sp, x0                         // SPSel = 1 beim Start: das ist SP_EL1
    mov  x0, #(3 << 20)                 // CPACR_EL1.FPEN: Gleitkomma/SIMD ohne Trap (der Stub rettet q0-q31)
    msr  cpacr_el1, x0
    adrp x0, gabbro_eintritt_vektoren   // die Tabelle des Erzeugers
    add  x0, x0, :lo12:gabbro_eintritt_vektoren
    tst  x0, #0x7ff                     // 0x800-ausgerichtet?
    mov  w9, #1
    b.ne fertig_mit_w9
    msr  vbar_el1, x0
    isb
    // --- Platz 4: SPx, sync ---
    mov  x19, #0x1234
    mov  x20, #0x5678
    mov  x30, #0x9abc
    mov  x0, #0x15
    msr  fpsr, x0                       // ein FPSR-Muster, das den Rufweg ueberleben muss
    mov  x0, #41
    svc  #0
    cmp  x0, #42
    mov  w9, #2
    b.ne fertig_mit_w9
    mov  x1, #0x1234
    cmp  x19, x1
    mov  w9, #3
    b.ne fertig_mit_w9
    mov  x1, #0x5678
    cmp  x20, x1
    b.ne fertig_mit_w9
    mov  x1, #0x9abc
    cmp  x30, x1
    mov  w9, #4
    b.ne fertig_mit_w9
    mrs  x1, fpsr
    cmp  x1, #0x15
    mov  w9, #5
    b.ne fertig_mit_w9
    // --- Platz 0: SP0, sync ---
    ldr  x1, =stapel_el0_oben
    msr  spsel, #0                      // ab hier ist `sp` SP_EL0
    mov  sp, x1
    mov  x0, #42
    svc  #0                             // die Ausnahme schaltet SPSel auf 1; der Stub laeuft auf SP_EL1
    cmp  x0, #142
    mov  w9, #6
    b.ne fertig_mit_w9
    mrs  x1, spsel                      // eret hat SPSR zurueckgebracht: wieder SPSel = 0
    mov  w9, #7
    cbnz x1, fertig_mit_w9
    mov  w9, #0
fertig_mit_w9:
    ldr  x1, =semi_block
    uxtw x9, w9
    str  x9, [x1, #8]
    mov  x0, #0x18                      // SYS_EXIT; der Block {Grund, Status} gibt den Exit-Code
    hlt  #0xf000
1:  b    1b
    .data
    .balign 8
semi_block:
    .quad 0x20026, 0                    // ADP_Stopped_ApplicationExit, Status
    .bss
    .balign 16
    .space 4096
stapel_el1_oben:
    .space 4096
stapel_el0_oben:
EOF
cat >"$TLS/stand.ld" <<'EOF'
ENTRY(_start)
SECTIONS {
  . = 0x40000000;
  .text : { *(.text.start) *(.text*) }
  .data : { *(.data*) *(.rodata*) }
  .bss : { *(.bss*) *(COMMON) }
}
EOF
llvm-mc -triple=aarch64-unknown-linux-gnu -filetype=obj "$TLS/stand.S" -o "$TLS/stand.o" || { echo "ROT: Pruefstand"; exit 1; }
ld.lld -static -T "$TLS/stand.ld" -o "$TLS/e.elf" "$TLS/e.o" "$TLS/stand.o" || { echo "ROT: ld"; exit 1; }

# Die Tabelle: 0x800-ausgerichtet, Platz 0 und 4 gesprungen, sonst `b .`.
tab=$(llvm-objdump -t "$TLS/e.elf" | awk '$NF=="gabbro_eintritt_vektoren"{print $1}')
echo "  Tabelle bei 0x$tab"
case "$tab" in *000|*800) echo "  Tabelle 0x800-ausgerichtet." ;; *) echo "ROT: Tabelle nicht 0x800-ausgerichtet"; exit 1 ;; esac
fin=$(printf "0x%x" $(( 0x$tab + 0x800 )))
llvm-objdump -d "$TLS/e.elf" --start-address=0x$tab --stop-address=$fin >"$TLS/tabelle.aus"
grep -q "gabbro_eintritt_ruf_vier" "$TLS/tabelle.aus" \
  && grep -q "gabbro_eintritt_ruf_null" "$TLS/tabelle.aus" \
  && [ "$(grep -cE "[[:space:]]b[[:space:]]+0x" "$TLS/tabelle.aus")" -eq 16 ] || { echo "ROT: die Tabelle hat nicht 16 Spruenge oder nennt Platz 0/4 nicht"; exit 1; }
for befehl in "eret" "mrs.*elr_el1" "msr.*spsr_el1" "stp.*q0, q1" "ldp.*q30, q31"; do
    llvm-objdump -d "$TLS/e.elf" | grep -qiE "$befehl" || { echo "ROT: im Stub fehlt: $befehl"; exit 1; }
done
echo "  Stub-Text: eret, elr/spsr, q0-q31 gesichert und zurueckgeladen."

timeout 60 qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -monitor none -serial none \
    -semihosting -kernel "$TLS/e.elf" >"$TLS/qemu.aus" 2>&1
rc=$?
echo "  qemu-system-aarch64 -M virt (EL1): exit $rc"
if [ "$rc" -eq 0 ]; then
    echo "== eintritt-a64: GRUEN (zwei Ausnahmen genommen, Stub-Rahmen und eret bewiesen) =="
    exit 0
fi
head -n 5 "$TLS/qemu.aus"
echo "== eintritt-a64: ROT (Pruefung $rc gefallen) =="
exit 1
