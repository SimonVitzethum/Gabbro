# C-FREI-REPORT -- no handwritten C in a finished Gabbro binary (C-free lane)

*Interim state, 2026-09-30 (session 11, Opus 5.5). The assignment is `~/claude-lane/AUFTRAG-C.md`;
the rule is AGENTS.md §3 (Simon, 2026-09-30). This file is rewritten at every milestone; the
numbers carry the command that measured them.*

## The measure

`python3 instrumente/zaehle-c.py` (C0): the handwritten C/asm/header files the build's own lists
put into each finished product, per target.

| target | 2026-09-30 morning | now | what is left |
|---|---|---|---|
| hosted | 1174 lines, 7 files | **0 lines, 0 files** | -- |
| kmod | 1344 lines, 11 files (two probes; 1659 / 13 with the `atomar` probe the counter lists since C2) | **399 lines, 4 files; runtime share 0** | the binding `bibliothek/linux-kmod/linux-kmod.c` (231) and the probes' own C (`takt.c` 98, `atomar.c` 42, `melde.c` 28) -- C2 slice 2 |
| metal | 1962 lines, 6 files | 1962, 6 | C3 not started: `laufzeit/metall/*` |

Hosted imports (`C0_ARBEIT=… python3 instrumente/zaehle-c.py --baue`, toolchain names removed):
172, 173 and the os-probe 0; examples 63 (`putchar`) and 64 (`write`) bind the C library by their
OWN `extern fn` -- the documented point of those two examples; their libc-free twins are 172/173
(a reading for Simon to confirm). The os-probe's binary still starts through the toolchain's
`__libc_start_main` (the driver's `int main` returns into it): the hosted `nolibc` driver is open.

## What moved, in order (each merged green: `cargo test --no-fail-fast`, `pruefe-emission.sh`, `lake build`, standard axioms)

| step | master | what | proved template(s) |
|---|---|---|---|
| a process without libc | `55a18e2d`, `f2b286f7`, `9b537fbb` | `nolibc`, `-> never` gates, gates in machine G (`bindAxiom`, `bindAxiomElse`) | `tor.nie`, `start.nolibc`, `tor.fehlbar` |
| the pointer-index hole | `d863c28d` | `N571` (OFFEN O36) | -- |
| memory as a REGION | `29652c50` | `-> ptr<…> u8 or R` gates, the extent from the gate's `ensures`; example 183 | `tor.region` |
| the arena runtime | `4c40b2f7` | `laufzeit/arena_dyn.c` gone; storage and report calls in Gabbro | `arena.dyn` |
| locks, page return | `273432da` | the ticket lock in the driver; `madvise`/`sched_yield` as gates; `start.c`, `start_pool.c` gone | `sperre.ticket`, `region.leeren` |
| a safety hole | `8fd71d0c` | `N572` (a stack-gate call with no `child` region checked clean); the clone trap's store (OFFEN O38) | -- |
| the `child` region outlined | (this merge) | OFFEN O38 closed: the region is a function the trap calls on the handed stack | `tor.kind` |
| threads | `f2295654`, `dec755b3` | `linux.c`, `bindung.h`, `faden.c`, `faden.h` gone; the hosted binding is Gabbro only | `tor.trampolin`, `faden.laufzeit` |
| the probe's report | `76e15c34` | `melde.c` gone: the os-probe prints through the binding's Gabbro writers | -- |
| the kernel-module runtime (C2, slice 1) | (this merge) | `laufzeit/kmodul/*` and `bibliothek/linux-kmod/stdatomic.h` gone: `gabbro build` writes the module driver (static arena pools of the manifest's `provision`, the lock primitives over the binding, a thread per root, the loader's entry symbols and the licence from the manifest), the type headers and a C11-builtin `<stdatomic.h>`; (M11) revised (comment only, `SERVER-0E-SPEC-DIFF.md` Part IV); `N506` accepts a constant clause | `arena.modul`, `modul.lebenslauf` |

Template register (`gabbro schablonen`): 33 entries, 22 machine-checked; `--tor` still names the 6
hanging premises it named before this lane (none of this lane's).

## Open, by name

* **Acceptance 0 (the network stack)**: the patch `~/claude-lane/C-FREI-FUER-NETZ.md` is on master
  since session 8; the network lane has not reported its `tests/*.sh` on it. `N571` asked it for
  74 sites.
* **Hosted**: a `nolibc` driver (`main` returns into the C runtime's start code).
* **C2 slice 2** (kernel module): the binding `linux-kmod.c` in Gabbro -- needs a variadic
  `extern fn` (`_printk`), the kernel thread start as a checked form (the hosted twin is `N572` +
  `tor.trampolin`), and the core number (`raw_smp_processor_id` is a per-CPU read); the probes'
  own C. **C3** (bare metal): not started.
* **Machine G has no byte pointers** (OFFEN O37): region programs stay UNCERTIFIED; nothing
  releases a region.
* No Isabelle on the server: `abnahme.py --voll` has not been run by this lane.
