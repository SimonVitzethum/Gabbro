# Opus agent J — every Gabbro feature freestanding, measured (2026-09-26)

*Task: Simon's rule of the day — everything Gabbro can do must work FREESTANDING, without an OS
(Gabbro exists for the Caprock microkernel). Opus agent I built the bare-metal thread runtime
(`laufzeit/metall/`, stage 11, OFFEN O32). This agent: a freestanding stage over EVERY emitting
unit, the gaps closed (arenas, strings, the program's own `via idt` handlers, idle `hlt`,
`gabbro build` linking the image), the things that genuinely need an OS named.*

## 1. The headline numbers

| measure | result |
|---|---|
| emitting units that compile with NO hosted header (`-ffreestanding -fno-builtin -nostdinc`) AND LINK with NO C library (`ld -nostdlib` against `laufzeit/metall/`) | **311 of 311** (stage 9's population; 313 emit, 2 are reverse probes set aside) |
| undefined symbols, classified | 13 runtime, 112 lock, 8 rcu, 10 entry, 167 foreign (the program's own `extern fn` bodies); **0 unclassified** |
| units that need nothing but the runtime | 225 |
| units that name foreign bodies the program supplies | 81 |
| HOSTED-ONLY, named (OFFEN O33) | **16**: 11 kernel gates (`syscall`), 5 foreign bindings to C-library names |
| entries with no honest register binding | 2 (`beispiele/11`, `probe-emission144-typeof`; OFFEN O32 (7)) |
| images booted on `qemu-system-x86_64 -smp 4` (stage 11) | **15** (Opus I's 5 + 10 new), every expectation held |
| gifts that bite | **5** (Opus I's 3 + 2 new) |
| images linked by `gabbro build` itself and booted unchanged | 2 (157, 59) |

## 2. What was measured first

The census over all 313 emitting units (`gabbro emit`, every tracked `.gab`):

- **Every unit includes `<math.h>`** (the emitter's prelude `KOPF`), 6 include `<string.h>`.
  Neither is a C11 freestanding header. With `-nostdinc` (the compiler's own header directory
  only) **313 of 313 failed** at `#include <math.h>`. `gcc -ffreestanding` on this machine
  had quietly used glibc's header — a hidden libc, in headers.
- Of `<math.h>` the emitter uses exactly ONE name: `isfinite` (the lowering of
  `narrow x to finite`). Of `<string.h>`: `memcpy`, `memcmp` (bounded strings, lane 261).
- Undefined symbols at `-O0` (every `static` body kept): 212 distinct names; at `-O2` with
  `-fkeep-static-functions`: 194, a strict subset — the optimiser adds no helper call.
- libc/OS names among them: `memcpy`, `memcmp` (runtime has them), `gabbro_arena_grow`
  (arena runtime), `gabbro_kern` (per-cpu), and the program's own `extern fn` bindings
  `putchar`, `write`, `close`, `mmap`, `pthread_self`, `raise`, `shutdown`, `sqrt`.

## 3. What was built

| piece | what |
|---|---|
| `laufzeit/metall/include/math.h`, `string.h` | the two hosted headers reduced to what the emitter uses: `isfinite` → `__builtin_isfinite` (no library call), the four memory functions `kern.c` defines. Nothing else: a unit that reached for more fails at compile time |
| `laufzeit/metall/arena.c` | the bare-metal half of `arena_dyn.h`, same two signatures: reserve = a static region (`METALL_ARENA_VORRAT`, 1 MiB) carved per arena at load, refusal = load refusal; commit = bookkeeping against a budget (`METALL_ARENA_ZUSAGE`), CAS on one word; budget exhausted → `grow` returns false → the program's `else`. Past `max` = fail-stop, as hosted |
| `metall.h`: `METALL_SPERRE_MASKIERT` (+ `_GETEILT`) | a `masks irqs` lock: IF cleared BEFORE the ticket is drawn, restored at release. Spins with IF = 0 never yield (`metall_sperre_nimm` checks IF): a masked holder is never descheduled |
| `metall.h`: `METALL_EINTRITT(NAME, GEWORFEN, CALL)` + `start.S` `metall_eintritt_gemeinsam` | the stub the emitter declares and never defines: saves every GPR + FXSAVE, hands the C half a `struct metall_rahmen *`, whose `CALL` binds `regs in` → the dispatch's parameters and `regs out` ← its result; EOI only for a LAPIC-thrown entry (`via idt`, vector ≥ 32) |
| `kern.c` | `metall_idt_setze` (refuses 0x40/0x41/0xFF and error-code exceptions, allows e.g. NMI), `metall_ipi_fest`, `metall_ipi_nmi`, `gabbro_kern` (the core index), the core limit `metall_kerne_grenze` (weak; `METALL_KERNE_GRENZE` in a driver), idle `sti; hlt; cli` + the wake IPI (vector 0x41) on every cross-core start, `metall_fremd_fehlt` (trap stub target), `metall_abgeben` safe from scheduler context |
| `metall.h`: `METALL_RCU(R)` | `R_lese_start`/`R_lese_ende` (reader count) and the grace wait `metall_rcu_gnade_R` |
| `instrumente/pruefe-freistehend.sh` | **stage 12** of `pruefe-emission.sh` (after stage 11): the freestanding compile + link over stage 9's list, symbol classification, hosted-only lists, a Sprechprobe (a `<stdio.h>` must not compile, an unsupplied `puts` must not link) |
| `instrumente/pruefe-metall.sh` | 10 new QEMU images + 2 gifts (below); every image now compiles `-nostdinc` |
| `gabbro build` (`bau.rs`, `treiber.rs`) | the metal driver also carries entries (installed before the first root starts), masked locks, rcu, the per-cpu core limit; a unit with entries but no roots owns a metal driver and no hosted one; a `metal <dir>` manifest line makes the build compile and LINK `<unit>.metall.elf` + `.metall.boot.elf` itself (runtime bytes in the fingerprint). Refusals by name: non-literal vector, non-x86_64 entry, runtime or error-code vector. `GENERATOR_KENNUNG` → `treiber-gen-4` |

## 4. QEMU results (stage 11, `-machine pc -accel tcg,thread=multi -smp 4 -m 128M`)

| image | expected line (serial) | result |
|---|---|---|
| `metall153` (arena, static twin) | `metall153 370` | ok |
| `metall154` (arena full, the `else` of `alloc`) | `metall154 1004` | ok (driver at `-O0`: 154's `-O2` array-bounds note is the emitter's, lane 242) |
| `metall158` (dynamic arena, `grow` commits) | `metall158 118` | ok |
| `metall158-else` (budget = the floor, 8 bytes) | `metall158-else 1` | ok — the REAL runtime refuses the commit |
| `metall161` (bounded strings) | `161 2 104 105 2 3 104 105 33 1 0 1 0` | ok (the hosted run's numbers) |
| `metall59` (own `via idt` handler + entered entry + masked lock) | `59 eintritte 600 systemrufe 9000 takt 1 auftrag 1 verletzt 0`, `METALL-VERTEILUNG 0 1 1 1` | ok: 600 fixed IPIs (one at a time, handshake), 3 threads × 3000 rounds of `locks TAKT` + `int $0x80`; **0** entries landed on a core with a claim on `TAKT` |
| `metall07` (register binding + NMI) | `07 syscall 71234 erhalten 1 nmi 1` | ok: `int $0x80` with rax=7 rdi=1 rsi=2 rdx=3 r10=4 → 71234 in rax; rcx, r11, rbx preserved; NMI entry (vector 2) fired by an NMI IPI |
| `bau157` (`gabbro build`'s own image, unchanged) | `METALL-VERTEILUNG 0 1 1 0` | ok |
| `bau59` (`gabbro build`'s own image, entry-only) | `METALL-VERTEILUNG 0 0 0 0` | ok |
| `grenze` (core limit 2 on `-smp 4`) | `METALL-KERNE 2`, `grenze kerne 2 zellen 6` | ok |
| gift `metall158-gift` (`17 → 18`) | must not succeed | bites (status 35) |
| gift `metall59-gift` (`TAKT` unmasked) | must not succeed, AND the handler reports landing on a core with a claim | bites (status 124, timeout) and prints `59 an entry landed on a core with a claim on TAKT` |

Opus I's five images and three gifts are unchanged and green with the new runtime (idle `hlt`,
wake IPI, IF-aware spin).

**A finding while building the gift.** The first gift checked only "landed on the HOLDER's
core" and hung without reporting it. The cause: with a TICKET lock, a thread that has DRAWN its
ticket and waits is part of the queue; an entry that interrupts it and takes a later ticket
waits behind the very thread it sits on. The masked lock therefore clears IF before the draw
(not after acquiring), and the observation is "a claim" (drawn or held). With that, the gift
names its reason.

## 5. HOSTED-ONLY (OFFEN O33), as stage 12 prints it

- **(a) kernel gate, 11:** `beispiele/74`, `90`, `96`, `149`, `150`, `155`, `156`, `160`,
  `1114`, `messung/schreibprobe/S14` (`syscall` items, `abi linux`), `beispiele/36` (own asm
  executes `syscall`). They LINK freestanding; running needs a kernel on the other side →
  OFFEN O31 (per-target syscall binding).
- **(b) hosted foreign name, 5:** `beispiele/63` (putchar), `64` (write),
  `c23-void-nullary` (putchar), `probe-c-namen-frei` (close mmap pthread_self raise shutdown),
  `probe-extern-bindet-c` (putchar).
- **hosted runtime files:** `laufzeit/faden.c` → `metall/kern.c`; `start.c`, `start_pool.c`,
  `<unit>.treiber.c` → `<unit>.metall.c`; `arena_dyn.c` → `metall/arena.c`.
- **reverse probes:** `gift/414` still falls freestanding; `probe-eintritt-parameter` bites a
  HOSTED rule (`-Werror=main`: freestanding C has no `main` rule) and compiles freestanding.

## 6. Decisions, with reasons

| decision | why |
|---|---|
| shim headers in the runtime, not an emitter change | removing `<math.h>` from the prelude moves `CText104.lean`/`CText108.lean` (pinned byte for byte), `CProben.lean`, `cnamen.rs` and the C-form census; the shim is how a freestanding kernel supplies headers, costs no pinned text, and fails loudly on any new name |
| link at `-O0` in stage 12 | stage 9's level, and the level at which every `static` body is kept; measured: the `-O2` symbol set is a subset |
| foreign bodies get TRAP stubs in stage 12 | the program supplies them (its own C); the link then proves nothing ELSE is missing. Bindings to C-library names are listed hosted-only, not admitted |
| mismatched entry bindings: loud stub, no checker rule | a rule (N561) would refuse `beispiele/11` and a probe and move pinned counts; that tightening is its own decision. The stub never guesses a binding |
| a spin with IF = 0 never yields | an entry handler or a masked holder must not give its core away; before this agent no Gabbro lock was ever taken with IF = 0, so Opus I's measured behaviour is unchanged |
| `gabbro_kern` from the runtime + a core limit | the contract "below the `per cpu` count" now holds by construction: the image brings up no more cores than the smallest cell array |
| idle `hlt` | `sti; hlt` is one window (no lost wake-up); the wake IPI shortens cross-core starts; the timer bounds any miss to one quantum |
| `Spec.lean` not edited | O25c's reviewer holds it; the proposed (M8)-(M10) assumptions stand in OFFEN O32 (12) |

## 7. Checks

- `free -g` at start: 31 GB total, 19 GB available; mid-run 8 GB available (other agents).
- Stage 12 alone: exit 0, 311 of 311. Stage 11 alone: exit 0, 15 booted, 5 gifts bite.
- `./lean-bau`, `./cargo-pruef`, `./emission-pruef`: see §8 (filled in after the merge of master).
- **MARKE deltas: none.** No `.gab` file was added or changed; stage 12 counts the same
  population as stage 9 and books no mark of its own. `MARKE_EMIT*` untouched.
- No checker code, no gift file, no example (N561–N565, gifts 1351–1360 unused; N561 named as
  the candidate for the entry-binding check).

## 8. Final runs
