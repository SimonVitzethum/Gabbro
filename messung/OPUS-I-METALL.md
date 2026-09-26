# Opus agent I — Gabbro threads without an OS (2026-09-26)

*Task: a bare-metal thread runtime for x86_64 behind the SAME interface the emitted C already
calls, a QEMU harness wired into `pruefe-emission.sh`, the named assumptions in the `Spec.lean`
header, OFFEN and TODO. Simon's rule of the day: everything Gabbro can do must work freestanding
— Gabbro exists for the Caprock microkernel. OFFEN O32.*

## 1. What was there, measured first

| piece | before | needs |
|---|---|---|
| runtime `start` (`laufzeit/faden.c`) | raw Linux syscalls `clone` (56), `futex` (202), `exit` (60) | Linux |
| boot `concurrent` (`start_pool.c`, `start.c`, generated `<unit>.treiber.c`) | pthreads, `printf`, `main` | libc + Linux |
| `L_nimm` / `L_gib` | hosted mutex (drivers) or a test spinlock (stage 22) | libc |
| emitted C of `beispiele/159` | `-ffreestanding -fno-builtin -nostdlib` clean; references only `gabbro_faden_start`, `gabbro_faden_warte`, `L_nimm`, `L_gib` | nothing else |

No boot stub existed in the tree (`grep` for Multiboot/LAPIC/0x3F8 over `.c/.S/.rs`: only prose
in `SPRACHE.md` and Caprock references). Everything below is new.

## 2. What was built

`laufzeit/metall/` (no libc anywhere; headers only `<stdint.h>`, `<stdatomic.h>`):

| file | content |
|---|---|
| `start.S` | Multiboot1 header; 32-bit `_start`: identity page tables for the low 4 GiB (2 MiB pages, LAPIC inside), PAE + LME + SSE, far jump to 64-bit, BSP stack; `metall_schalte` (the context switch); 32 exception entries (report + stop); the LAPIC-timer entry (saves 15 GPRs + FXSAVE, yields, `iretq`); the AP trampoline (16 → 32 → 64 bit), copied to 0x8000, absolute references as `T(x)` constants |
| `kern.c` | `memcpy/memmove/memset/memcmp`; serial 0x3F8; both 8259s masked; IDT; ACPI RSDP → RSDT → MADT (cores); INIT–SIPI–SIPI one AP at a time; per-core `struct kern` behind `IA32_GS_BASE`; thread table (64); one FIFO run queue per core under a ticket lock; scheduler loop per core (the idle root is its empty-queue branch: `pause`, touch nothing); LAPIC timer periodic (vector 0x40); `gabbro_faden_start` / `gabbro_faden_warte`; `metall_ende` via `isa-debug-exit` |
| `metall.h` | the thread interface (identical to `faden.h`), the ticket lock (`metall_ticket_nimm/gib`: the four instructions of `CTicket.lean`), `metall_sperre_nimm` (the same plus a yield every 64 spins), `METALL_SPERRE(L)` / `METALL_SPERRE_GETEILT(L)` defining exactly `L_nimm`/`L_gib` (+ shared pair), the driver hook `int gabbro_metall_haupt(void)` |
| `metall.ld` | image at 1 MiB, Multiboot header first |

`gabbro build` now writes **`<unit>.metall.c`** beside `<unit>.treiber.c` (`treiber.rs`
`erzeuge_metall`, `metall_pin_pruefe`; `bau.rs` pins it at every build like the hosted driver,
a missing file forces a rebuild; `GENERATOR_KENNUNG` → `treiber-gen-3`). Tests: unit test
`metall_treiber_haelt_pin` (pin, pool ×2, shared lock, no hosted symbol, determinism) and
integration test `bau_schreibt_metalltreiber_freistehend` (the generated file for 124 compiles
with `-ffreestanding -nostdlib -Werror` against `metall.h`).

## 3. Decisions, with reasons

| decision | why |
|---|---|
| **own Multiboot1 stub**, not Caprock's boot | Caprock is read-only and not in this tree; Multiboot1 is SPRACHE A21 and what `qemu -kernel` boots. The ELF64 image is handed over as `objcopy -O elf32-i386` (QEMU refuses ELF64 Multiboot) |
| **per-core queues, thread fixed to its core, round robin placement from core 1** | no work stealing = no cross-core dequeue protocol to get wrong; placement from core 1 puts the declared starts on other cores than the driver thread (core 0), which the harness measures (`METALL-VERTEILUNG`) |
| **LAPIC-timer preemption, on by default** | cooperative scheduling is NOT enough for Gabbro programs: a thread spinning on a flag (or a `retry spin`) that a later thread of the same core sets never gives up the core. Measured: the `staffel` probe finishes preemptive and hangs into the timeout cooperative (`-DMETALL_KOOPERATIV`, the gift) |
| **join = re-read with acquire, yield between reads** (no `hlt`+IPI) | a sleeping waiter needs a wake list per word and an IPI from the ending core — a second protocol with its own lost-wakeup race. The yield loop re-reads on every path, exactly the shape of the hosted futex loop. Cost: the waiter stays in its queue (one short turn per round) |
| **the word is cleared by the SCHEDULER after the thread left its stack** | the emitter reuses the unit's static stack at the next `start`; a thread that clears its own word is still standing on it. Measured positive: 200 start/join rounds on one stack |
| **ticket lock = CTicket's four instructions; the Gabbro-facing spin yields every 64 passes** | pure spinning with more threads than cores waits a whole quantum per hand-over when the next ticket belongs to a descheduled thread (a convoy): 8 × 20000 acquisitions on 4 cores did not finish in 60 s, 8 × 500 took 1.5 s. With the yield: 8 × 500 in 0.15 s, 8 × 20000 in about 3 s. The yield is a stutter of an unserved ticket (`spinnt_nur`), not a lock step; order stays ticket order |
| **runtime-internal locks: ticket locks with IF = 0** | the timer can then never interrupt a holder of a runtime lock, and its handler only takes one on the core's own scheduler stack — the one discipline that keeps preemption deadlock-free inside the runtime |
| **a shared lock takes the same exclusive ticket** | stronger than asked (readers exclude each other), never weaker |
| **idle = `pause` spin, interrupts off** | touches no carrier (`none` of `mitRuhe`); `hlt` would need a wake-up source per core. A power question, named in O32 |
| **no checker rule** | nothing in the language changed; N556–N560 and gifts 1341–1350 stay unused with the O32 work |

## 4. A finding on the hosted side, fixed

`laufzeit/faden.c` **lost joins.** The parent stored the TID into the join word itself after
`clone` returned; a child that had already ended had its word cleared by the kernel
(`CLONE_CHILD_CLEARTID`) BEFORE that store, which then wrote a dead TID back — and
`gabbro_faden_warte` waited on it forever. Measured: 200000 start/join rounds of an empty root on
one stack hung (timeout 60 s) before round 20000. Fix: `CLONE_PARENT_SETTID` with `ptid = wort`
(the kernel writes the TID in `copy_process`, before `wake_up_new_task`) and no parent store.
After: 200000 rounds run through. The probe is part of `pruefe-metall.sh` (no gift: the race
bites only sometimes). The metal runtime keeps the same order by construction.

## 5. QEMU results

`instrumente/pruefe-metall.sh` (stage 11 of `pruefe-emission.sh`; runs alone), QEMU 11.1.1,
`-machine pc -accel tcg,thread=multi -smp 4 -m 128M`, report over serial 0x3F8, end over
`isa-debug-exit` (status 33 = success):

| run | expectation (every line must stand in the serial log) | result |
|---|---|---|
| `metall159` | `159 lauf 64`, `METALL-VERTEILUNG 0 1 1 0` | ok |
| `metall124` (generated driver) | `124 konto-gleich 1 konto-in-30-70 1 privA 7 privB 5`, `METALL-VERTEILUNG 0 1 1 0` | ok |
| `metall157` (generated driver, pool ×2) | `157 konto 30 30`, `METALL-VERTEILUNG 0 1 1 0` | ok |
| `stress` | `stress zaehler 160000`, `stress wiederverwendung 200`, `METALL-VERTEILUNG 52 52 52 52` | ok |
| `staffel` | `staffel durch`, `METALL-VERTEILUNG 1 2 1 1` | ok |
| gift `metall159-gift` (`+1 → +0`) | must not succeed | bites (status 35, reports 0) |
| gift `stress-gift` (lock emptied) | must not succeed | bites (status 35, lost updates) |
| gift `staffel-gift` (`-DMETALL_KOOPERATIV`) | must not succeed | bites (status 124: timeout) |
| hosted join (`faden.c`) | 200000 rounds | ok |

All images: `METALL-KERNE 4` (four cores checked in), `nm` shows no undefined symbol and no
`pthread`/`clone`/`futex`. Without `qemu-system-x86_64` the script builds and links all eight
images and prints `METALL: NOT RUN` — never a pass line.

## 6. Spec, OFFEN, TODO

- `grammatik/Grammatik/Zielsatz/Spec.lean`: comment-only hunk **"bare-metal runtime block"**
  inside THE ONE ASSUMPTION LIST under (d): what `ZielF`'s thread machine already covers (any
  scheduler is a subset of its free interleaving; no leg depends on which one runs), and
  (M1)–(M7), the named runtime/hardware assumptions of the metal runtime: context switch,
  LAPIC/IPI, boot protocol (incl. `.bss` zeroing = `Laufzeit.lader`), scheduler fairness (used
  by NO leg; what makes ending runs reachable), the lock (CTicket refinement, yield = stutter),
  the join, DRF-SC on metal; plus NOT CLAIMED on metal (hardware other than QEMU, the limits,
  quantum length, stacks, program-declared `via idt` handlers → O19/O32). No definition moved.
- `dokumente/OFFEN.md` **O32** (new). `TODO.md` §0 (thread start, bare-metal form). `AGENTS.md`
  §7 ledger row. No SATZKARTE section: no Lean was added.

## 7. What stays open (O32)

Real hardware; the program's own `via idt` handlers in the metal IDT; the Caprock integration
(the runtime would move under Caprock's own entry); the limits (16 cores, 64 live threads,
16 KiB scheduler stacks); `hlt` for idle cores; `gabbro build` renders the metal driver but the
link recipe is the harness's.

## 8. Checks

- `free -g` at start: 31 GB total, 17 GB available; before the final runs: 20 GB available.
- `./lean-bau`: exit 0, 0 error lines (the only Lean change is the comment hunk in `Spec.lean`).
- `./cargo-pruef`: first run 1402 passed, 1 failed — `bausystem::inkrementell_nach_inhalt_und_nicht_nach_zeitstempel`, the flaky build-system test Opus O25 met too (shared `target/bau-beispiel`, unrelated to this branch); **final run exit 0, 1403 passed, 0 failed, 1 ignored.**
- **MARKE_EMIT: no delta.** No `.gab` file was added or changed; stage 11 counts no files.
- `./emission-pruef`: exit 0, ALL PASS (51 executed units, 311 of 311 compile); stage 11 inside it green with the results of section 5.
- `pruefe-englisch.py` is red on master already (ratchets 7949/26/2 against 7965/37/5, none of
  the listed sites is in this branch).
