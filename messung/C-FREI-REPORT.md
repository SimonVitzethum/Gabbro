# C-FREI-REPORT -- no handwritten C in a finished Gabbro binary (C-free lane)

*Interim state, 2026-10-05 (session 13, Opus 5.5). The assignment is `~/claude-lane/AUFTRAG-C.md`;
the rule is AGENTS.md §3 (Simon, 2026-09-30). This file is rewritten at every milestone; the
numbers carry the command that measured them.*

## The measure

`python3 instrumente/zaehle-c.py` (C0): the handwritten C/asm/header files the build's own lists
put into each finished product, per target.

| target | 2026-09-30 morning | now | what is left |
|---|---|---|---|
| hosted | 1174 lines, 7 files | **0 lines, 0 files** | -- |
| kmod | 1344 lines, 11 files (two probes; 1659 / 13 with the `atomar` probe the counter lists since C2) | **95 lines, 1 file; runtime and binding 0** | the `takt` probe's own hardirq timer `messung/proben/kmodul/takt.c` (95) -- its HARNESS, not product: on kernel 6.8 an hrtimer's callback is a field of `struct hrtimer` (a code address stored into a kernel layout) |
| metal | 1962 lines, 6 files counted -- **2090 / 7 in truth**: `eintritt_asm.h` (128, included by `kern.c`) was in neither the build's list nor the count until 2026-10-05 | **1377 lines, 4 files** | C3 slices 1-4 done (arena, memory functions, headers; the Gabbro-facing locks and rcu read sides; the IDT; the thread runtime -- all generated, proved text); left: serial, LAPIC, ACPI, SMP bring-up (`kern.c` 571), boot/switch/entries (`start.S` 427, `eintritt_asm.h` 128), the entry macros (`metall.h` 251) |

Hosted imports (`C0_ARBEIT=… python3 instrumente/zaehle-c.py --baue`, toolchain names removed):
172, 173 and the os-probe 0; examples 63 (`putchar`) and 64 (`write`) bind the C library by their
OWN `extern fn` -- the documented point of those two examples; their libc-free twins are 172/173
(a reading for Simon to confirm). The os-probe -- two roots, a lock, an arena -- builds as a
`nolibc` `program` whose entry is its generated driver (2026-10-01): a static binary with no
startup file and no `__libc_start_main`, `nm -u` empty.

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

| bare metal, slice 1 (C3) | (this merge) | `laufzeit/metall/arena.c`, `include/math.h`, `include/string.h` and the memory functions of `kern.c` gone: the metal driver writes the PROVED `arena.modul` pool runtime behind a reservation by list position, the build writes the four memory functions and the two header names beside the image; harnesses take them from `gabbro runtime metal-arena`/`metal-memory`/`metal-include` | `metall.speicher`, `arena.metall` |

| bare metal, slice 2 (C3) | (this merge) | the Gabbro-facing locks (`METALL_SPERRE`, `_GETEILT`, `_MASKIERT`, `_MASKIERT_GETEILT`), `METALL_RCU` and the flag helpers left `metall.h`: the generated `<metall_sperren.h>`, the same bytes, now proved -- the yield of the spin a stutter of `CTicket.lean`, the masked lock's IF = 0 from before the draw until the restore and its flag word the holder's own, the rcu count the readers' total depth | `sperre.metall`, `sperre.maskiert`, `rcu.metall` |

| bare metal, slice 3 (C3) | (this merge) | the IDT left `kern.c`: the generated `<unit>.metall.idt.c` (table, gate encoding, the runtime's slots, `lidt`, the two installers), `gabbro runtime metal-idt` for harnesses; `pruefe-os-bindung.sh` scans the generated machine layer for OS names too | `idt.metall` |

| bare metal, slice 4 (C3) | (this merge) | the thread runtime left `kern.c`: the generated `<unit>.metall.faden.c` (run queues, scheduler loop, first frame, start, join), `gabbro runtime metal-threads`; `kern.c` keeps the bring-up and reaches the cores through `metall.h` | `faden.metall` |

Template register (`gabbro schablonen`): 41 entries, 30 machine-checked; `--tor` still names the 6
hanging premises it named before this lane (none of this lane's).

## Open, by name

* **Acceptance 0 (the network stack)**: the network lane applied `C-FREI-FUER-NETZ.py` in its
  real tree on 2026-10-05 (`~/gabbro-netz` `ac1f9f0`, branch `alltag-a`, WIP). Measured read-only
  on a clone of its HEAD `9d67c01` with gabbro `f1b12316`: 30 manifests build, 0 C files each,
  `nm -u` empty on all 29 ELF binaries (`~/claude-lane/kratz/c/netz8-mess.txt`). Open: its VM
  suites GREEN on this build and the change in its `master`.
* **Kernel module, the last 95 lines**: the `takt` probe's hrtimer (`takt.c`). Its callback is a
  FIELD of `struct hrtimer` on kernel 6.8; code reaches a foreign body only as an `entry fn`
  ARGUMENT. Kernels from 6.13 take it as an argument (`hrtimer_setup`). A question for Simon:
  is a probe's own harness C inside acceptance 3 ("0 handwritten C lines in the .ko")?
* **Probe finding:** `atomar`'s "flag seen > 0" is scheduling-dependent -- 1 of 5 runs this
  session saw the consumer finish before the producer's first store (`kratz/c/s11/kmod-b.log`).
* **C3** (bare metal), what is left after slices 1 and 2: the kernel proper -- serial, IDT, LAPIC,
  ACPI (MADT by physical address), SMP bring-up, scheduler, context switch (`kern.c`), the boot
  and entry stubs (`start.S`, `eintritt_asm.h`), the entry macros and declarations (`metall.h`).
  Mapped piece by piece in `messung/C3-WAENDE.md`: four walls -- (A) a device at a fixed
  hardware address, (B) physical memory read by an address the machine hands over, (C) a thread
  as saved machine state, (D) code before any Gabbro can run -- and three questions for Simon
  (A, B, and which asm stays asm).
* **Machine G has no byte pointers** (OFFEN O37): region programs stay UNCERTIFIED; nothing
  releases a region.
* No Isabelle on the server: `abnahme.py --voll` has not been run by this lane.
