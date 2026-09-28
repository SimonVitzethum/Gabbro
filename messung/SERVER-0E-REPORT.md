# Server lane, phase 1 (TODO section 0e): what was measured

*Written 2026-09-28 by the autonomous Claude lane on `ubuntu@simon.jocraft.cc`
(`~/claude-lane/AUFTRAG-1.md`). Every number below has the command that produced it beside
it. Isabelle is not installed on this machine, so `abnahme.py --voll` did not run and no
claim here rests on it.*

The machine: 15 GB RAM (`free -g`: 7 GB available throughout), 8 cores, ~15 GB disk free,
QEMU in TCG (no KVM). One heavy job at a time.

---

## 0. The headline

| acceptance point (AUFTRAG-1) | state | where |
|---|---|---|
| 1. two units (`bib` + `app`) link, check whole and build | **met** -- and it already stood in the tree; the `gabbro link` half was closed here | section 1 |
| 2. one concurrent driver RUNS against a handwritten C version | **open** | section 5 |
| 3. a Gabbro kernel module with a bounded heap loads in QEMU, allocates, hits refuse-on-full, reports it, unloads clean | **met** | section 3 |
| 4. H4 numbers (ceiling costs nothing) | **met** | section 2 |
| 5. `cargo test` zero failures, emission green, `grammatik` green, axioms standard | **partly** -- see section 4 | section 4 |
| 6. TODO boxes, ledger, merge, push, tag | **partly** | section 6 |

---

## 1. Acceptance point 1 -- two units link, check whole, build

**Measured first, built second.** The first thing this lane did was ask what of section 0e
already stands, because a lane that builds what is there measures its own work twice.

`gabbro build a.gab b.gab` (Opus agent F, OFFEN O28) already derived each unit's interface
from the other units on the command line and linked them; a two-unit manifest already built
both to C and objects:

```
$ cd ~/claude-lane/kratz/bau && gabbro build manifest        # unit bib / unit app
built    bib
built    app (+ app.treiber.c, app.metall.c)
gabbro build (link): bib + app -- 1 import(s) held against their bodies, 4 shared
declaration(s), 1 shared hardware assumption(s); the linked program checked whole
(0 error(s)); 0 refusal(s)
linked   2 unit(s) -- the whole program checked
built 2 unit(s), 0 up to date, 0 refused -- 2 file(s) named by this manifest
```

**What did NOT stand: `gabbro link a.gab b.gab`.** The same pair, handed to `link` instead of
`build`, fell -- `use bib::setze;` reached nothing, the app was checked alone with no head for
`setze`, and the link never ran:

```
error: [H016] … this `locks` effect names `L`, and no `lock` declaration explains it
error: [H021] … `app::arbeiter` calls `setze`, and `setze` is unknown to the graph
error: [K003] … `arbeiter` promises costs, but `setze` is not declared here
gabbro link: …/tabelle-app.gab has errors -- a unit with errors links nothing
```

A hand-made `.gabi` (`gabbro abi` + `--with`) was the workaround. That is exactly TODO section
0e's *"the honest workaround is an `extern` mirror plus a named assumption per crossing"*.

**Built here:** `gabbro link` without `--with` derives the preambles from the units on the
command line, out of the SAME function `gabbro build` uses
(`crates/gabbro-cli/src/main.rs::vorspaenne_aus_einheiten`; `bau.rs` now calls it instead of
carrying its own copy -- `W7`, one register over one thing).

```
$ gabbro link messung/proben/verbund/tabelle-bib.gab messung/proben/verbund/tabelle-app.gab
gabbro link: … -- 1 import(s) held against their bodies, 4 shared declaration(s),
1 shared hardware assumption(s); the linked program checked whole (0 error(s)); 0 refusal(s)
```

**The derivation is not a weakening**, and the test says so: a derived head is written FROM the
body, so `N501`-`N505` can only agree with it. What those codes are for is a head somebody
typed or generated earlier, and that path is unchanged -- give the link a `.gabi` whose
`ensures` is not the body's and it still refuses:

```
$ gabbro link …bib.gab …app.gab --with bib-stale.gabi
error: [N502] …: the contract the importer relies on for `bib::setze` is not the exporter's
… the linked program NOT checked whole (a head is stale -- fix it first); 1 refusal(s)
```

**A finding the change produced, and the repair.** The first version of the derivation broke
link probe `1248-modul-doppelt`: two units that declare the SAME module got each other's
`module werk { … }` heads prepended, so `werk` was declared twice in one text, the unit fell
alone with `N001` twice, and the link never reached `N516` ("a module holds items in two
units"). *A refusal that does not reach the link cannot be said at the link.* The rule now
is: two units sharing a module derive nothing from each other -- an interface is what a unit
reads of ANOTHER module. Test: `crates/gabbro-cli/tests/verbund.rs::jede_linkprobe_faellt_mit_ihrem_code_und_nur_am_link`
(unchanged, and it is what caught it) plus the new
`der_link_ohne_with_leitet_die_schnittstellen_ab`.

```
$ cargo test --no-fail-fast -p gabbro-cli --test verbund
test result: ok. 6 passed; 0 failed
```

---

## 2. Acceptance point 4 (H4) -- the ceiling costs nothing

**The claim:** compile time, emitted C size and binary size must not grow with a dynamic
arena's ceiling `max M` -- no static array of `M` slots, no `memset` of the reservation, no
per-element unrolling.

**The twins:** `messung/proben/arena-h4/ceiling-10mib.gab` and `ceiling-32gib.gab` differ in
the `max` number, the module name and the head comment, in nothing else.

**Why 32 GiB and not 40.** `M` is a slot COUNT and the counters are `uint32_t`
(`PLAN-DYNAMISCH.md` section 2: `M <= u32::MAX`), so with 8-byte slots the largest expressible
ceiling is 4 294 967 295 x 8 = 32 GiB. 40 GiB is not expressible in any element type this
language has. The twin therefore stands at the type system's own maximum, which is the
stronger measurement, and the 40 GiB of the task text is what TODO section 0e already calls it:
*"the 40 GiB number itself is irrelevant, what counts is statically linkable, bucket-bounded,
refuse-on-full."*

**The instrument:** `instrumente/miss-arena-decke.sh` (best of 5 translations each, `cc -O2`,
`size -A` for the sections).

```
$ instrumente/miss-arena-decke.sh
== the ceiling against the cost (H4) ==
                        max 1310720 (10 MiB)   max 4294967295 (32 GiB)
translate (ms, best of 5 )               4                         5
emitted C (bytes)                   3168                      3180
emitted C (lines)                     70                        70
binary (bytes)                     16488                     16488
binary .bss (bytes)                   24                        24
binary .data (bytes)                  64                        64
run answer                            33                        33

GREEN: the ceiling costs nothing -- 5 runs each, numbers above.
```

The 12-byte difference in the emitted C is the ceiling literal itself (7 digits against 10) plus
the module name. `.bss` and `.data` are equal to the byte, and the binaries are byte-identical
in size.

**The poison probe.** `--gift` links a real `static uint64_t buf[1310720]` beside the SMALL
twin -- exactly the shape the claim forbids -- and the instrument must turn red:

```
$ instrumente/miss-arena-decke.sh --gift
binary .bss (bytes)             10485824                        24
RED: .bss differs (10485824 vs 24) -- storage grew with the ceiling
GIFT CAUGHT (1 finding(s)) -- the instrument sees a ceiling that costs.
```

---

## 3. Acceptance point 3 -- a Gabbro kernel module with a bounded heap, in QEMU

**In QEMU only.** Nothing built here was ever loaded into this host's kernel
(`~/claude-lane/REGELN.md`). The harness boots a copy of the host's kernel
(`~/claude-lane/vm/vmlinuz`, 6.8.0-139-generic) with a busybox initramfs, loads the module
there, reads `dmesg`, unloads, powers off. TCG, no KVM: one run is about 25 s wall.

### 3.1 The program

`messung/proben/kmodul/halde-treiber.gab`, 7 items, 0 errors. It declares

* **one foreign function, and that is the whole of its Linux**:
  `extern fn gabbro_kmod_melde(schluessel : u32, wert : u64) effects { pure } costs <= 64 ops;`
  with the assumption `kmod_melde_vertrag` and its falsifier beside it. The body is the
  program's own C (`messung/proben/kmodul/melde.c`, three lines of `pr_info`). **No table of
  Linux kernel functions was added to the tree, here or anywhere** -- the binding constraint
  of TODO section -1.
* **one bounded heap**: `arena Knoten capacity 2 .. 4 max 4096 of Wert` (8-byte slots), grown
  three times by 1024. The whole-run upper bound is 4 + 3072 = 3076 slots, below the ceiling,
  so `N426` admits all three grows.

### 3.2 The runtime

`laufzeit/kmodul/` -- the third flavour of one interface, beside the hosted
(`laufzeit/arena_dyn.c`) and the bare-metal (`laufzeit/metall/arena.c`) halves:

| file | what |
|---|---|
| `kmodul.c` | the driver: `module_init`/`module_exit` over the unit's own functions, the arena reservations before any of the unit's code, the emitted C included (inclusion, not linkage -- a `static` root is nameable). **It is not generated**: everything unit-specific arrives as a `-D` macro, so there is one copy of the text in the tree |
| `arena.c` | reserve = one `vzalloc` region per arena, commit = a budget over it |
| `kmodul.h` | `gabbro_arena_ladefehler` / `gabbro_arena_alles_freigeben` -- a module is loaded and unloaded, so it has to say both |
| `include/` | `stdint.h`, `stdbool.h`, `stddef.h`, `stdatomic.h`, `math.h` over the kernel's own types: the kernel builds `-nostdinc` and every emitted unit's prelude asks for those five names |

**A measured finding, named and not worked around.** The hosted reserve names address space
without storage (`mmap(PROT_NONE)`); a loadable module has no exported primitive for that --
`get_vm_area` and `vmap_pages_range` are not `EXPORT_SYMBOL`, and everything that is exported
(`vmalloc`, `__vmalloc`, `kvmalloc`) commits what it maps. So the kernel-module flavour reads
the ceiling the way bare metal already does, which is the reading `Zielsatz/Spec.lean` (M10)
already carries: **the ceiling is the number the checker holds every `grow` against (`N426`),
and what the module can actually commit is the module's own provision** (`vorrat_kib`, a
module parameter). Nothing in the checker, the emitter or the goal theorem moves for it, and
the program's `else` is the answer either way. *The ceiling still costs nothing*: `span` is
`min(ceiling, provision)`, computed at run time out of the descriptor.

**`stdatomic.h` is a REFUSAL, not a shim.** A unit that declares an `atomic` fails to compile
as a kernel module, with the reason in the header: C11 `_Atomic` is not the kernel's memory
model, the kernel has its own (`READ_ONCE`/`WRITE_ONCE`, `atomic_t`, `smp_*`), and the goal
theorem's atomic rely (`SchwachX`) is proved about the first one. A silent lowering would put
a second memory model beside the proved one. What it would take to lift it is named in the
header and in section 5 below; neither half is built.

### 3.3 The run

`instrumente/pruefe-kernelmodul.sh`. The provision is set to 24 KiB on purpose: two grows fit
(4 + 2048 slots = 16 416 bytes), the third does not (3076 slots = 24 608 bytes > 24 576). So
the third `grow` is refused BELOW the ceiling and the program's `else` runs -- **refuse-on-full,
deliberately reached, not hoped for.** That is the branch the hosted runtime practically never
takes (OFFEN O20); here it is deterministic, every boot.

```
$ instrumente/pruefe-kernelmodul.sh
== a Gabbro unit as a Linux kernel module, in QEMU ==
   source      messung/proben/kmodul/halde-treiber.gab
   kernel      ~/claude-lane/vm/vmlinuz (6.8.0-139-generic headers)
   provision   vorrat_kib=24 (the program's ceiling is max 4096 slots)
   HARNESS: begin
   HARNESS: insmod ok
   HARNESS: rmmod ok
   [    3.463214] gabbro-halde: k=1 v=0        <- entered
   [    3.463345] gabbro-halde: k=2 v=33       <- allocated and read back (11 + 22)
   [    3.463378] gabbro-halde: k=3 v=3        <- the THIRD grow refused: refuse-on-full
   [    3.472570] gabbro-halde: k=9 v=0        <- unloaded
   HARNESS: end

GREEN: loaded, allocated, refused on full, reported, unloaded clean.
```

No `Oops`, no `BUG:`, no `WARNING:` -- the harness checks for all of them and for the four
lines in order.

### 3.4 What makes the green run a measurement

Four harness mutations, each caught by a different check (`--gift all`):

```
GIFT 1: caught (1 finding(s))   RED: the kernel log is missing: gabbro-halde: k=2 v=34
GIFT 2: caught (1 finding(s))   RED: the kernel log is missing: gabbro-halde: k=3 v=3
GIFT 3: caught (1 finding(s))   RED: the kernel log is missing: gabbro-halde: k=9 v=0
GIFT 4: caught (5 finding(s))   RED: insmod did not succeed
                                RED: rmmod did not succeed
                                RED: the kernel log is missing: gabbro-halde: k=2 v=33

gifts: 4 of 4 caught
```

1 moves the expected read-back (does the run read the log, or only `insmod`'s exit code?);
2 raises the provision past the third grow, so the refusal line must be MISSING (does the run
notice a line that did not come?); 3 drops the `rmmod`; 4 lowers the emitted ceiling to 4, so
every `grow` is past `max` -- a fail-stop, not a branch.

**Gift 4 found something, and that is the best thing in this section.** The first time it ran,
`insmod` SUCCEEDED. The runtime set its load error and returned false; the program's `else`
ran; the unit answered 0; and `module_init` -- which read the load error only BEFORE calling
the unit -- let the module in. *A fail-stop that does not reach the loader is not a fail-stop.*
`laufzeit/kmodul/kmodul.c` now reads it again after the unit's init, and the gift is caught at
`insmod` as well as in the log. The green run above is the run AFTER that repair.

---

## 4. Acceptance point 5 -- the walls

| wall | state | command |
|---|---|---|
| `cargo test --no-fail-fast` | **green**: rc 0, **1409 passed, 0 failed** (1408 before the change; the one is the new link test) | `cargo test --no-fail-fast` |
| `pruefe-emission.sh` | **green**: rc 0, `ALL PASS -- 51 durchgestochen, 318 von 318 uebersetzen`; FREESTANDING 318 of 318 | `instrumente/pruefe-emission.sh` |
| `grammatik` Lean build | see section 6 | `cd grammatik && lake build` |
| `#print axioms gabbro_ziel` | see section 6 | `cd grammatik && lake env lean Nachpruefung.lean` |
| `pruefe-saetze.py` | green: 470 identifiers, 198 sentences, 55 without a sentence, **0 invented** | `instrumente/pruefe-saetze.py` |
| `pruefe-todo/-englisch/-kennungen/-waechter` | rc 0 each. `kennungen` reports 2 double assignments, `N004`/`N005` in `namen.rs` + `zielbindung.rs` -- **pre-existing** (Opus lane L), not this lane's | -- |
| `abnahme.py --voll` | **cannot run here**: no Isabelle on this machine | -- |

**The emission run took three tries, and the middle one is the lesson.**

1. The first run was green at 315 of 315 -- **over a population that did not contain the new
   probes.** The corpus is `git ls-files` (`instrumente/korpus.py`: *"the property that
   actually defines part of the corpus is not a location, it is authorship"*), and untracked
   files are invisible to it. A green run over the wrong denominator.
2. Staged, the second run found `FUND: 156 statt 153 emittierende Dateien in messung/*/` --
   the good case, and still a finding -- **and ABORTED at stage 9**, so stages 10, 11 and 12
   were not measured at all. The script says so in its own last lines
   (`ABGESCHNITTEN in: Stufe 9 … Was DAHINTER steht, wurde NICHT gemessen`).
3. `MARKE_EMIT_M` 153 -> 156, booked with its date and its reason in `pruefe-emission.sh`
   (the three new probes, all emitting). Third run: `ALL PASS`, 318 of 318, freestanding
   318 of 318 -- the kernel-module probe links without an OS like every other unit.

**The Lean build.** `grammatik/.lake` did not exist when this session started: the setup's
warm-up (`~/claude-lane/logs/aufwaermen.log`) ended `rc=1` on `error: unknown short option
'-j'`. Nothing this lane changed touches `grammatik/`, so no Lean statement moved -- but
"nothing moved" is not "it was measured". Section 6 carries the outcome.

---

## 5. What is open, and why

* **Acceptance point 2** -- a concurrent driver RUNNING through the executed set against a
  handwritten C version. Not built. The executed set (`pruefe-emission.sh`) has concurrent
  runs; what is missing is the handwritten-C twin beside one of them.
* **K2/K3** -- `start` lowering (`C001`) and export (`LG004`); `entry`/`boot` vector,
  registers, steps in the kernel-module flavour; handler pinning/re-entry and `cli`/`sti` in
  the C (OFFEN O19). Untouched. The kernel module built here has no `start` and no `entry`:
  its init and exit are ordinary functions, which is what a Linux module is entered by.
* **K4 residue** -- the module is built by `instrumente/pruefe-kernelmodul.sh`, not yet by
  `gabbro build`. The design that avoids a second register is settled and half-built: the
  driver (`laufzeit/kmodul/kmodul.c`) is already macro-parameterised, so the build's job is a
  manifest word (`kmod <kernel build dir>`, beside `metal <dir>`) that writes a `Kbuild` with
  those `-D`s and copies the runtime beside the emitted C -- which is exactly what the
  instrument does today, in shell.
* **H3** -- `ArenaDyn.lean` has `DynArena`, `dynGrow` and the commit-sequence theorems with
  witnesses (lane 241's model half). What PLAN-DYNAMISCH section 9 still wants is named in
  that file's own tail comment: `DynForm` over `ArenaForm D`, the four section-9 theorems in
  full `Block` form, and the simulation. Untouched here. The two `Spec.lean` (d) assumption
  texts (`Laufzeit.reserve`, `Laufzeit.commit`) are not inserted, and `SERVER-0E-SPEC-DIFF.md`
  is therefore not written.
* **H5** -- the OFFEN O20 restriction is kept by not touching it: no `reset` concurrent with a
  reader, no cross-thread arena without the strict option. Nothing here widens it.
* **Atomics in a kernel module** -- named in `laufzeit/kmodul/include/stdatomic.h` as a
  compile-time refusal. Lifting it needs (a) a kernel-module lowering of `atomic` onto the
  kernel's own primitives and (b) the argument that the kernel's model refines the one
  `SchwachX` assumes. Neither is built, and the refusal is the honest placeholder.

## 6. The numbers at the end of the session

| measurement | number | command |
|---|---|---|
| `cargo test --no-fail-fast` | rc 0, **1409 passed, 0 failed** (1408 at the baseline; +1 is the new link test) | `cargo test --no-fail-fast` |
| `pruefe-emission.sh` | rc 0, `ALL PASS -- 51 durchgestochen, 318 von 318 uebersetzen, 2 umgekehrte Probe(n)`; FREESTANDING **318 of 318** link without an OS | `instrumente/pruefe-emission.sh` |
| `grammatik` Lean build | rc 0, **355 targets, no error** -- a COLD build (`grammatik/.lake` did not exist), about 75 min on 8 cores | `cd grammatik && ~/.elan/bin/lake build` |
| `#print axioms gabbro_ziel` | **`[propext, Classical.choice, Quot.sound]`** -- standard, and so are `gabbro_ziel_sc`, `gabbro_ziel_sc_aus`, `gabbro_ziel_zeuge`, `schlusssatz`, the chain witnesses and `schlusssatz_124` | `cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean` |
| kernel module in QEMU | GREEN; `--gift all` **4 of 4 caught** | `instrumente/pruefe-kernelmodul.sh` |
| the H4 twins | GREEN; `--gift` caught | `instrumente/miss-arena-decke.sh` |
| `abnahme.py --voll` | **not run** -- no Isabelle on this machine | -- |

`MARKE_EMIT_M` 153 -> 156, dated and reasoned in `pruefe-emission.sh` (the three new probes,
all emitting). No other counter moved. No diagnostic code, gift number or example number was
taken; the AGENTS.md section 7 ledger was re-measured (it was stale by more than a hundred
codes) and this lane is booked there with what it added instead.

**Not tagged.** A milestone tag belongs at the push that COMPLETES a phase, and acceptance
points 2 and 6 are open. The hand-over is `~/claude-lane/STAND.md`.
