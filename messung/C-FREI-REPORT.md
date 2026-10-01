# C-FREI-REPORT -- no handwritten C in a finished Gabbro binary (C-free lane)

*Interim state, 2026-10-01 (session 12, Opus 5.5). The assignment is `~/claude-lane/AUFTRAG-C.md`;
the rule is AGENTS.md §3 (Simon, 2026-09-30). This file is rewritten at every milestone; the
numbers carry the command that measured them.*

## The measure

`python3 instrumente/zaehle-c.py` (C0): the handwritten C/asm/header files the build's own lists
put into each finished product, per target.

| target | 2026-09-30 morning | now | what is left |
|---|---|---|---|
| hosted | 1174 lines, 7 files | **0 lines, 0 files** | -- |
| kmod | 1344 lines, 11 files (two probes; 1659 / 13 with the `atomar` probe the counter lists since C2) | **95 lines, 1 file; runtime and binding 0** | the `takt` probe's own hardirq timer `messung/proben/kmodul/takt.c` (95) -- its HARNESS, not product: on kernel 6.8 an hrtimer's callback is a field of `struct hrtimer` (a code address stored into a kernel layout) |
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
| the kernel-module runtime (C2, slice 1) | `beb513d3` | `laufzeit/kmodul/*` and `bibliothek/linux-kmod/stdatomic.h` gone: `gabbro build` writes the module driver (static arena pools of the manifest's `provision`, the lock primitives over the binding, a thread per root, the loader's entry symbols and the licence from the manifest), the type headers and a C11-builtin `<stdatomic.h>`; (M11) revised (comment only, `SERVER-0E-SPEC-DIFF.md` Part IV); `N506` accepts a constant clause | `arena.modul`, `modul.lebenslauf` |

| the kernel-module binding in Gabbro (C2, slice 2) | (this merge) | `N573`: a variadic `extern fn` (`_printk`, `panic`), arguments behind `...` cast to their declared type; the report, the load verdict and the locks are Gabbro over `_printk`/`_raw_spin_*`; the probes report through `gabbro_kern_zeige`/`_halt` -- `melde.c`, `atomar.c` and all but two pieces of `linux-kmod.c` gone | -- |

| the kernel thread start in Gabbro (C2, slice 3) | (this merge) | `N575`-`N577`: the type `entry fn(…) -> R` -- code a generated driver hands in, the one shape in which code reaches a foreign body; `gabbro_kern_faden_start` is Gabbro over `kthread_create_on_node`/`wake_up_process` (the `ERR_PTR` decoded in Gabbro), the join a word per root and `msleep`; the core number and the holder record (probe instrumentation in product code) gone -- `linux-kmod.c` DELETED; example 184, gifts 1394-1397; OFFEN O39 closed but for the probe's timer, O40 recorded | `faden.modul` |

Template register (`gabbro schablonen`): 34 entries, 23 machine-checked; `--tor` still names the 6
hanging premises it named before this lane (none of this lane's).

## Open, by name

* **Acceptance 0 (the network stack)**: the patch `~/claude-lane/C-FREI-FUER-NETZ.md` is on master
  since session 8; the network lane has not reported its `tests/*.sh` on it. `N571` asked it for
  74 sites.
* **Hosted**: a `nolibc` driver (`main` returns into the C runtime's start code).
* **Kernel module, the last 95 lines**: the `takt` probe's hrtimer (`takt.c`). Its callback is a
  FIELD of `struct hrtimer` on kernel 6.8; code reaches a foreign body only as an `entry fn`
  ARGUMENT. Kernels from 6.13 take it as an argument (`hrtimer_setup`). A question for Simon:
  is a probe's own harness C inside acceptance 3 ("0 handwritten C lines in the .ko")?
* **Probe finding:** `atomar`'s "flag seen > 0" is scheduling-dependent -- 1 of 5 runs this
  session saw the consumer finish before the producer's first store (`kratz/c/s11/kmod-b.log`). **C3** (bare metal): not started.
* **Machine G has no byte pointers** (OFFEN O37): region programs stay UNCERTIFIED; nothing
  releases a region.
* No Isabelle on the server: `abnahme.py --voll` has not been run by this lane.
