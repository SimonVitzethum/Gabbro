# C-FREI-REPORT -- no handwritten C in a finished Gabbro binary (C-free lane)

*Interim state, 2026-09-30 (session 10, Opus 5.5). The assignment is `~/claude-lane/AUFTRAG-C.md`;
the rule is AGENTS.md §3 (Simon, 2026-09-30). This file is rewritten at every milestone; the
numbers carry the command that measured them.*

## The measure

`python3 instrumente/zaehle-c.py` (C0): the handwritten C/asm/header files the build's own lists
put into each finished product, per target.

| target | 2026-09-30 morning | now | what is left |
|---|---|---|---|
| hosted | 1174 lines, 7 files | **0 lines, 0 files** | -- |
| kmod | 1344 lines, 11 files | 1344, 11 | C2 not started: `laufzeit/kmodul/*`, `bibliothek/linux-kmod/linux-kmod.c` |
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
| threads | `f2295654`, `dec755b3` | `linux.c`, `bindung.h`, `faden.c`, `faden.h` gone; the hosted binding is Gabbro only | `tor.trampolin`, `faden.laufzeit` |
| the probe's report | (this merge) | `melde.c` gone: the os-probe prints through the binding's Gabbro writers | -- |

Template register (`gabbro schablonen`): 30 entries, 19 machine-checked; `--tor` still names the 6
hanging premises it named before this lane (none of this lane's).

## Open, by name

* **Acceptance 0 (the network stack)**: the patch `~/claude-lane/C-FREI-FUER-NETZ.md` is on master
  since session 8; the network lane has not reported its `tests/*.sh` on it. `N571` asked it for
  74 sites.
* **Hosted**: a `nolibc` driver (`main` returns into the C runtime's start code).
* **C2** (kernel module), **C3** (bare metal): not started.
* **Machine G has no byte pointers** (OFFEN O37): region programs stay UNCERTIFIED; nothing
  releases a region. **O38**: the `child` region's C runs in the parent's frame.
* No Isabelle on the server: `abnahme.py --voll` has not been run by this lane.
