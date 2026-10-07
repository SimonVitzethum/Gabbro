# AArch64 compatibility of the C11 backend and its runtime (agent A)

*2026-10-07, Sonnet agent A. Worktree base `d58fbd92` (master `35a5bd21` only adds Arm plan
files). Debug `gabbro` built in the worktree with `CARGO_BUILD_JOBS=2`. Host: x86_64, gcc 16.2.1;
cross: `aarch64-linux-gnu-gcc` 16.1.0, clang 23.1.1 (`--target=aarch64-linux-gnu`),
`qemu-aarch64` (user mode, no binfmt registered, so a launcher script runs it). **Nothing here
proves anything about hardware**: qemu-user runs on an x86 host, which is stronger than Arm
(see section 4).*

Scripts and probe drivers are in `messung/arm-a/` (set `ARM_A_SCRATCH` to a scratch directory).
`ARM-PLAN.md` does not exist in this base commit; the task text was the plan.

## Summary

* **No source change was needed or made.** Every AArch64 failure is a unit that declares
  `arch x86_64` in its own Gabbro source, or the generated runtime reading such a declaration
  (`bibliothek/linux/linux.gab`). The language already makes the machine explicit, and the
  emitter already refuses `arch` other than `x86_64` (`syscall.rs:399`, `emit.rs:4815`,
  `emit.rs:18791`). The blocker is the sealed `aarch64` row in the checker, not a bug in
  portable emission.
* **Measured:** 157 of 157 `beispiele/*.gab` emit. **136 of 157 compile for AArch64** with
  `-std=c11 -Wall -Wextra -Werror` (gcc; clang 137), 154 of 157 on the x86 host (the 3 host
  failures are the `nolibc` units, which need the manifest's `-ffreestanding`). The 21
  failures fall in 4 classes, all x86-by-declaration (section 2).
* **Measured:** the existing differential harness, with `cc` replaced by a cross-compiling
  launcher: **46 of 52 units run under `qemu-aarch64` and print exactly the expected
  (x86-validated) result at `-O0` and `-O2`**. The 6 failures are one class: the
  `register ... __asm__("rax")` system-call stub.
* **Measured:** a hand-port of that one stub (no tool change) makes `beispiele/74` print the
  expected `ok` / `3` under qemu-aarch64. The stub is the whole difference for the hosted
  system-call units.
* **Not portable by nature:** `laufzeit/metall/` (bare metal), the `nolibc` `_start`, the
  clone/thread trampoline, port I/O, `asm` bodies of the examples.

## 1. Inventory

Counts are lines matching an x86 pattern (`x86`, register names, `__asm__`, `pause`, `cli`,
`hlt`, `wrmsr`, `syscall`, ...) over total lines, taken with
`grep -cE '<pattern>' <file>` (pattern in the command history of this report; matches include
comments that explain x86, so read counts as upper bounds). Classes: **P** portable already,
**S** needs a target switch (could be made portable), **N** x86-only by nature (needs an Arm
equivalent written, not a switch).

| File | x86 lines / total | Class | What |
|---|---|---|---|
| `laufzeit/metall/start.S` | 108 / 427 | **N** | Multiboot1 entry, long-mode setup, GDT/IDT, AP trampoline copied to 0x8000 |
| `laufzeit/metall/eintritt_asm.h` | 91 / 128 | **N** | register-save entry stubs, `iretq`, x87/SSE state |
| `laufzeit/metall/kern.c` | 22 / 571 | **N** | `outb`/`inb` (`:72-74`), `wrmsr` (`:78`), `pushfq/cli` (`:86,91`), `pause` (`:94`), 16550 at port 0x3F8 (`:106-125`), LAPIC, ACPI MADT, `isa-debug-exit` port 0xF4 (`:174`) |
| `laufzeit/metall/metall.h` | 25 / 251 | mixed | ticket lock is C11 atomics (**P**, `:63-81`) with one `pause` asm (**S**, `:70`); `METALL_EINTRITT` stubs are **N** (`:161,196`) |
| `laufzeit/metall/metall.ld` | 0 / 23 | **N** | 1 MiB identity-mapped Multiboot layout |
| `laufzeit/arena_dyn.h`, `laufzeit/sperre.gab` | 1 / 72, 0 / 74 | **P** | no machine content |
| `bibliothek/linux/linux.gab` | 58 / 499 | **S** | every gate is `abi linux arch x86_64 number N` with `rdi/rsi/rdx/r10/r8/r9`, clobbers `rcx, r11`: write `:130`, exit_group `:141`, mmap `:108`, mprotect `:119`, madvise `:346`, sched_yield `:378`, clone `:430`, plus exit, futex. Numbers differ on AArch64 (write 64, mmap 222, exit_group 94, clone 220, futex 98, ...), registers are `x0-x5`, number in `x8`, `svc #0` |
| `bibliothek/linux-kmod/linux-kmod.gab` | 3 / 400 | **P** (mostly) | kernel-function declarations; one comment names the x86_64 SysV convention (`:77`); built by kbuild, so arch comes from the kernel tree |
| `crates/gabbro-check/src/syscall.rs` | 20 / 501 | **S** | closed list of x86_64 registers (`:33-39`), `N066`; `A006` refuses any arch but `x86_64` (`:395-405`) |
| `crates/gabbro-check/src/emit.rs` | 140 / 19250 (most are comments and Gabbro keywords such as `syscall`) | **S** | the stub (`:9178-9207`, `:9798-9830`): `register ... __asm__("rax")`, `syscall`; the ABI table `("linux","x86_64") => "syscall"`, `("metal","x86_64") => "int $0x80"` (`:9278-9279`); stack-gate trampoline `testq/andq $-16,%rsp/call *` (`:9204-9211`, `:10005-10011`); port I/O `in`/`out` (`:5152-5161`); arch gates for `entry`/`entrust`/`boot`/`device at port` (`:18791`, `:18900`, `:18995`, `:4815`) |
| `crates/gabbro-cli/src/treiber.rs` | 43 / 2537 | split | hosted driver text: **P** (C11 atomics, `ARENA_LAUFZEIT` `:168`, `FADEN_LAUFZEIT` `:279`, `SPERRE_TICKET` `:328`); the metal driver strings (`METALL_SPERREN` `:1095` `pushfq; popq; cli` `:1130-1141`, `pause` `:1151`; `METALL_IDT` `:1271` `lidt` `:1349`; `METALL_FADEN` `:1397` `rsp` switch, `%gs:0` `:1447`, `wrmsr` `:1459`, `sti; hlt; cli` `:1591`) are **N** |
| `crates/gabbro-cli/src/bau.rs` | 29 / 3253 | **S** | `nolibc` `_start`: `and $-16, %rsp` (`:2847-2849`); metal entries refuse arch != `x86_64` (`:1675-1677`); the manifest already takes any `compiler` line, which is what let the AArch64 builds below work |
| `crates/gabbro-check/src/schablonen.rs` | 37 / 1825 | **S** (text) | template register prose names x86 registers (`:216-219`, `:403-418`); the proofs behind it are in Lean (out of scope here) |
| `crates/gabbro-check/src/tearing.rs` | 23 / 824 | doc | a ruling's price text says "x86_64 total store order ... no fence" (`:263`); the scan itself reads emitted C and is arch-neutral |
| `crates/gabbro-check/src/x86/` (9 files) | all | **N** | the direct x86 backend; untouched by instruction |
| `instrumente/` | `-mfma` (`pruefe-emission.sh:226,235`, `sonde-fma.c`), `qemu-system-x86` (`pruefe-metall.sh`, `pruefe-freistehend.sh`, `pruefe-kernelmodul.sh`) | **S** / **N** | the FMA probe is an x86 flag; the QEMU stages boot x86 images |

Searches that found **nothing**: no `__x86_64__` / `__i386__` guard anywhere in `crates/`,
`laufzeit/`, `bibliothek/`; no `_mm_*`, `__builtin_ia32`, `rdtsc`, `cpuid` in emitted C; no
plain `char` in emitted C (only `unsigned char`, `159-laufzeit-start.c:29`), so the
x86/Arm `char` signedness difference does not bite. `static_assert((-1 >> 1) == -1)` and
the modular-conversion asserts in every unit's header hold on AArch64 (they compiled).

## 2. Measurement

Commands (from the worktree root; `S` = scratch directory):

```
cargo build --bin gabbro                       # CARGO_BUILD_JOBS=2, debug
bash messung/arm-a/emit_all.sh target/debug/gabbro $S/em0   # emit every beispiele/*.gab
bash messung/arm-a/cc_all.sh $S/em0                          # host cc, aarch64 gcc, aarch64 clang: -c
python3 messung/arm-a/derive.py instrumente/pruefe-emission.sh arm-probe.sh $PWD $PWD/target/debug/gabbro
bash messung/arm-a/run-a64.sh                  # arm-probe.sh with cc = messung/arm-a/cc-wrapper.sh
bash messung/arm-a/conc.sh                     # two threaded drivers, host vs qemu-aarch64
python3 messung/arm-a/port74.py                # hand-port of one stub
```

### 2a. Compile only (157 emitted units, `-std=c11 -Wall -Wextra -Werror -Ilaufzeit -c`)

| Compiler | ok | FAIL |
|---|---|---|
| host `cc` (x86_64 gcc) | 154 | 3 (`172`, `173`, `183`: `_Noreturn void main` needs the manifest's `-ffreestanding`) |
| `aarch64-linux-gnu-gcc` | **136** | 21 |
| `clang --target=aarch64-linux-gnu` | 137 | 20 (`60` passes in clang because an unused `static` function is not emitted; gcc `-O0` emits it and the assembler rejects `mfence`) |

First error of every failure class (aarch64 gcc):

| Class | Units | First error |
|---|---|---|
| A. system-call stub, `register ... __asm__("rax")` | 17: `1114 149 150 155 156 160 163 164 172 173 174 181 182 183 74 90 96` | `error: invalid register name for '_sys_rax'` (and `_sys_rdi`, `_sys_rsi`, `_sys_rdx`), e.g. `74-syscall-schreiben.c:45:22` |
| B. user `asm` body with x86 constraints | 3: `36-asm`, `65-port-space`, `67-befehlsebene` | `error: impossible constraint in 'asm'` (`outb %[wert], %[tor]` with `"a"`/`"d"`, `36-asm.c:35`) |
| C. user `asm` with an x86 mnemonic | 1: `60-annahme-mit-maschine` | `Error: unknown mnemonic 'mfence'` (assembler, `60-annahme-mit-maschine.c:54`) |
| D. `main` shape | `172 173 183` (also fail on the host) | `error: 'main' declared '_Noreturn'`; they build through `gabbro build` with `nolibc` flags, which then hit class A and the x86 `_start` (below) |

All 21 sources say `arch x86_64` or `abi linux arch x86_64` in the Gabbro text (checked per
file with `grep -E 'arch x86_64|abi linux|abi metal'`); `67` even names `dsb sy`, an Arm
barrier, in its comment.

### 2b. Run (52 units of the differential harness, 5 stages each)

`derive.py` cuts `instrumente/pruefe-emission.sh` to its 52 `lauf` calls, wraps each in a
subshell so a failure is recorded and the run continues (the harness's own `set -e` would
stop at the first one: the "stops at the first hit" trap of `CLAUDE.md`), replaces
`cargo run` by the built binary, and stops each unit after stage 5. Stages 6-8 (UBSan,
ASan, certificate, poison probe) are **not** run on AArch64: no cross sanitizer runtime and
no Arm certificate; the wrapper drops `-fsanitize*`. The wrapper compiles with
`aarch64-linux-gnu-gcc -static` and writes a launcher `exec qemu-aarch64 <binary>`.

```
host baseline   : 52 PASS, 0 FAIL  (host-run.txt)          -- the derived script itself is sound
aarch64/qemu    : 46 PASS, 6 FAIL  (a64-run.txt)
```

PASS means: generated C compiles with `-Wall -Wextra -Werror`, runs under qemu-aarch64, and
prints exactly the harness's expected string (the x86 result) at `-O0` **and** at `-O2`.
This covers integer tables, records, floats (`26-gleitkomma`, expected `0.2 0.5 0.5 0.8 1.0`),
arenas without OS gates, matrices, the F01-F10 fragments, `161-zeichenkette`, `175` unbound.

FAIL (6): `beispiel74`, `beispiel90`, `beispiel96`, `beispiel158`, `beispiel175-gebunden`,
`beispiel159`. All six stop at stage 3 with class A. 158, 175-gebunden and 159 do not contain
the stub themselves: it comes from `bibliothek/linux/linux.gab` (`linux_bind.c:174-180`,
`:245-248`), which every hosted arena or thread program links.

`gabbro build` with a manifest whose `compiler` line is
`aarch64-linux-gnu-gcc -static ...` works for hosted programs: `63-druckt` and
`64-writes-a-whole-buffer` build, and under qemu-aarch64 print `Hallo` / `Puffer`, equal to
the x86 output. The `nolibc` manifest `172` with an aarch64 compiler line fails at the same
stub (`prozess.c:50:22: invalid register name for '_sys_rax'`); behind it would come the
x86 `_start` (`bau.rs:2847`).

### 2c. Concurrency and atomics (hand-written pthread drivers around emitted units)

* `117-message-passing-flag` (payload `bericht` written plain, flag `BEREIT` store-release /
  load-acquire): 20 000 rounds, writer thread vs reader loop. host: `seen=28..1166
  violations=0`; qemu-aarch64: `seen=510..16302 violations=0` (`-O0` and `-O2`). The AArch64
  code is `stlrb` / `ldarb` (measured with `aarch64-linux-gnu-gcc -O2 -S`), so the emitted
  orderings map to real Arm release/acquire instructions with no change.
* `140-atomic-array-counter` (bounded `compare_exchange_weak` loop, bound 64, `regel_streit`
  on exhaustion): 4 threads x 200 000 increments of one cell hit `regel_streit` **on the host
  too**; the driver exceeds the declared contention, so this run discriminates nothing.
  The AArch64 code calls `__aarch64_cas4_relax` (outline atomics, runtime LSE dispatch).
* Thread start (`159-laufzeit-start`, `157-worker-pool`): not runnable on AArch64, see class A;
  the thread start is a `clone` system-call gate in `linux.gab:430`.

### 2d. Hand-port of one stub (scratch only, not committed as a fix)

`port74.py` rewrites the one `write` stub of the emitted `74-syscall-schreiben.c`
(`rdi/rsi/rdx` -> `x0/x1/x2`, number 1 in `rax` -> 64 in `x8`, `syscall` -> `svc #0`, result
read from `x0`). `aarch64-linux-gnu-gcc -static -std=c11 -O2 -Wall -Wextra -Werror` builds it
and `qemu-aarch64` prints `ok` and `3`, the harness's expected output. So the stub text is a
mechanical translation; the missing part is the language/checker side that is allowed to
say it (section 3).

## 3. Fixes

**None committed to `crates/`, `laufzeit/`, `bibliothek/`.** Reason, per candidate:

* Adding `("linux","aarch64")` to `emit.rs:9278` is unreachable and unsafe alone: `A006`
  (`syscall.rs:399`) and `N066` (`syscall.rs:33-39`) refuse any other arch and register name
  first, and loosening them is a checker-rule change that the task excludes. The stub text
  (section 2d) and the stack-gate trampoline (`emit.rs:10005-10011`, needs `x0`/`sp` code in
  place of `rax`/`rsp`) belong to one change together with the Lean template register
  (`schablonen.rs:403-418`, the Lean files behind it), not to a "target switch".
* `-mfma` in `instrumente/pruefe-emission.sh:226,235` is the FMA probe of the x86 build; an
  Arm variant needs a decision (what the probe measures on Arm), not a flag swap.
* `tearing.rs:263` is a price text; changing it for Arm before an Arm ruling exists would
  state something nobody measured.

The only thing added is the measurement apparatus in `messung/arm-a/`.

## 4. Findings: decisions an Arm port must take

**Measured versus reading** is marked on each line.

1. **System-call ABI is a Gabbro-level declaration, so the port is declaration plus table,
   not C surgery** (measured: 2a class A, 2b, 2d). Needed: `arch aarch64` accepted by `A006`
   and `N066` with its own register list (`x0-x30`, `sp` conventions), an
   `("linux","aarch64") => "svc #0"` row at `emit.rs:9278`, clobber rules (x86 clobbers
   `rcx`, `r11`; the Arm `svc` clobbers none of `x0-x7` beyond the declared outputs, reading),
   a second `linux.gab` with the aarch64 numbers, and the Lean template/G-side counterpart.
   Note `bibliothek/linux/linux.gab` encodes numbers in the binding, which is where the
   project's rule ("the OS is user logic, nothing is OS-specific") already puts them.
2. **Thread start** (measured: class A blocks it; reading for the rest). The hosted thread
   runtime is generated C11 (`treiber.rs:279-327`, portable) around `gabbro_os_klon_tor_trampolin`,
   whose body the emitter writes from the stack gate with x86 text (`testq %rax,%rax; movq
   %stackreg,%rdi; andq $-16,%rsp; call *%reg; ud2`, `emit.rs:9204-9211`, `:10005-10015`).
   AArch64 needs the child path (`cbz x0`, set `sp`, `br`) and a decision on the 16-byte
   alignment text that the template proof (`tor.trampolin`, `tor.kind`) states in terms of
   `rsp + 8`.
3. **CAS retry bound on LL/SC** (reading, not measured; qemu-user emulates atomics with host
   instructions and cannot show it). Emitted `compare_exchange_weak` loops are bounded by a
   constant (64 in `140`, `emit.rs:11573`) and exit through `regel_streit()`. On x86 a weak
   CAS fails only when the value changed; on AArch64 without LSE it is an `ldxr/stxr` pair
   that can fail spuriously (exclusive monitor lost to an unrelated write on the same granule,
   interrupt). The argument that justifies the bound ("a lost race means somebody made
   progress") needs to be restated for Arm, or the emitter should use the strong form where
   the bound is meant to be a contention bound. Compiled code uses outline atomics
   (`__aarch64_cas4_relax`), which dispatches to LSE `cas` when present (measured on the
   `-S` output).
4. **Message passing and locks are portable** (measured for 117; reading for locks).
   Publish/await uses C11 `memory_order_release`/`acquire` on the flag with a plain payload
   (`117-message-passing-flag.c:32-44`), lowered to `stlrb/ldarb`. The hosted and metal ticket
   locks are written with `memory_order_relaxed` ticket draw, `acquire` spin and `release`
   store (`treiber.rs:328-357`, `metall.h:63-81`), which is the correct C11 pairing on Arm; the
   only x86 text is `pause`, whose Arm counterpart is `yield` (or `wfe` with a wake protocol,
   a design choice with a proof obligation). **Where C code relies on TSO, I found no emitter
   path** that emits a plain shared access without a lock or a declared release/acquire pair;
   this is a reading of `emit.rs` plus the 157 emitted files, not a proof, and the tearing
   scan (`tearing.rs`) only admits `SlotPlain`/`GlobalPlain` shapes "no ordering claim"
   (`:240-251`). The C11 contract holds on Arm for these as long as DRF holds; the
   *price text* at `tearing.rs:263` (TSO plus compiler barrier, no fence) is the one place that
   states the x86 reading and must be re-ruled for Arm.
5. **Volatile device registers carry no barriers** (reading + counting: at least 9 emitted
   `*(volatile uint32_t *)(d->basis + ...)` accesses in the corpus, `Shape::Volatile` is `Open`
   in `tearing.rs:263-270`). Ordering between a device write and a normal-memory write is
   implicit on x86 (port and uncached MMIO are strongly ordered) and needs `dmb`/`dsb` on
   Arm. The language already has a `device ... at dma` assumption for DMA barriers
   (`emit.rs:4936`); there is no equivalent for MMIO ordering, which is a language decision.
6. **User `asm` bodies are, by design, machine text** (measured: class B/C). Each carries
   `arch x86_64`. An Arm unit says `arch aarch64` and writes `dsb sy` (the corpus already has
   that sentence in `67`); the emitter's `asm` lowering is machine-neutral
   (`__asm__ __volatile__`) as long as the constraint letters are the user's.
7. **Floating point** (measured for `26-gleitkomma`; reading for the rest). The header
   (`emit.rs:923-935`) presupposes SSE2 and `__FLT_EVAL_METHOD__ == 0`; AArch64 has no x87
   and evaluates in the declared type, so the IEEE-kernel argument is easier there. The
   only trap is fused multiply-add: GCC defaults to `-ffp-contract=fast` in GNU mode and
   `off` in ISO mode, and AArch64 has FMA in the base ISA, so the manifest flag
   `-ffp-contract=off` stops being optional hygiene and becomes load-bearing on Arm
   (the existing FMA probe uses `-mfma`, x86 only, and needs an Arm twin).
8. **Bare metal** (`laufzeit/metall/`, metal driver strings in `treiber.rs`): nothing
   carries over except the C11 lock and the arena template. A new runtime is required
   (exception vectors, `VBAR_EL1`, GIC instead of LAPIC, PSCI or spin-table SMP start,
   PL011 instead of 16550, no port I/O, `eret`, `TPIDR_EL1` instead of `%gs`), plus a new
   QEMU stage (`qemu-system-aarch64` is available here, untested by this report).
   `bau.rs:1675` already refuses non-x86 metal entries, so nothing silently half-works.
9. **Instrument apparatus** (measured): `instrumente/pruefe-emission.sh` aborts at the first
   failing unit (`set -e`, `exit 1` inside `lauf_kern`); run on a cross target it reports one
   failure for what is 6. Any Arm gate built on it needs the continue-and-count form (the
   `--absenkung` mode is the existing precedent; `derive.py` shows a minimal one).
10. **Lean side not looked at** (out of my area): the weak-memory model for the goal theorem
    is x86-TSO (`schwach_ist_gX`, `SchwachX`); an Arm claim needs an Arm memory model there.
    Nothing in the Rust or C measured above says anything about that.

## 5. What this report does not say

* It does not say the Arm runs are correct hardware behaviour: qemu-user is not a memory
  model test and not silicon.
* It does not say the 46 passing units are certified for Arm: the certificate and
  sanitizer stages were not run (stages 6-8 of the harness).
* The 157-unit compile count is `-c` only; link-and-run was done for the 52 units of the
  harness, the two threaded drivers and the hand-ported stub.
