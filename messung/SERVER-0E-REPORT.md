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
| 2. one concurrent driver RUNS against a handwritten C version | **met** -- and it FOUND something: the emitted C read a guarded carrier with the lock released | section 7 |
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

* **Acceptance point 2** -- *closed in session 2, see section 7*, and it found the
  release-before-the-read defect in the `locks` lowering. This entry stays as the record of
  what was open on 2026-09-28 session 1.
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

---

## 7. Acceptance point 2 -- one concurrent driver, RUN against a handwritten C version

*Added 2026-09-28, session 2 of the server lane. **This is the section with a finding in
it.***

### 7.1 What was built, and why it is a differential test and not a demonstration

| file | what |
|---|---|
| `messung/proben/nebenlaeufig/sperre-rueckgabe.gab` | the probe: a read under its lock, RETURNED, while a second thread writes the same carrier under the same lock. 10 items, 0 errors, 3 hints (the `E247` hint class `beispiele/125` carries) |
| `messung/proben/nebenlaeufig/sperre-rueckgabe-hand.c` | the same program **written by hand in C from the source** -- not from the emitted file. Its header says how it was written, because that is the whole of its value |
| `messung/proben/nebenlaeufig/treiber.c` | ONE driver, compiled over either side: the unit's lock as a test-only spinlock, plus two counters -- acquisitions (compared) and contended acquisitions (the overlap witness) |
| `instrumente/pruefe-nebenlaeufig-zwilling.sh` | the instrument: 2 sides x 2 optimisation levels x 5 repetitions, with four poison probes |

The probe's answer is a statement, not a number somebody chose: `lies_unter_sperre` writes
`7` into `z` and returns `z`, both inside one `locks L` block, so under the language's own
reading the answer is `7` on every schedule. `leser` does that 64 times and sums the answers
under the same lock, so the sum `448` says **every one of the 64 reads saw its own write**;
`nullt` writes `0` into the same carrier under the same lock 64 times, so every one of those
reads has a writer racing it. 193 is the acquisition count (64 x 2 + 64 + 1), and it is in the
compared line so the lock DISCIPLINE is compared and not only the answer.

**Why the overlap witness is part of the verdict.** Two threads that never contend have run
sequentially, and a sequential run of a concurrent program measures nothing about concurrency
-- the same empty population as a guardian with no input (W17). Zero contention over every
repetition is a RED here, not a pass.

### 7.2 The finding: `return` inside `locks` read the carrier with the lock RELEASED

The first run of the instrument, against the tree as it stood:

```
LINE emit -O0 1: 273 193 | overlap 128     <- the EMITTED C
LINE emit -O0 2: 427 193 | overlap 109
LINE emit -O0 4: 406 193 | overlap 108
LINE emit -O2 2: 413 193 | overlap 112
LINE emit -O2 5: 420 193 | overlap 116
LINE hand -O0 1..5: 448 193                <- the HANDWRITTEN twin, every run
LINE hand -O2 1..5: 448 193
RED: emit at -O0, run 1 answered '273 193', the source says '448 193'
```

The lowering was

```c
static uint32_t lies_unter_sperre(void) {
    L_nimm();
    {
        z = 7;
        L_gib();          /* <- the release */
        return z;         /* <- and THEN the read */
    }
    L_gib();
}
```

`emit.rs`'s own comment said it: *"Erst freigeben, dann zurueckkehren"*. The first half of
that decision is right and is booked (`MESSUNGEN.md` section 3): an emitter that writes the
release only at the end of the block leaves the lock held on every `return` inside it. **The
second half was wrong**, and it had never been questioned because the corpus shape that
carried it is `return true;` -- a literal, which has no carrier to lose.

**What it costs where it bites.** `beispiele/125-read-under-lock.gab` is the flagship of
"guarded at the access": two threads, both touching `z` only inside `locks WACHE`, and the
checker calls that race-free (`N291` silent, `concurrent { lese_schreibe, setze_null }`
declared). Its emitted C read `z` outside the section. *The guarantee did not survive the
lowering, and nothing in the tree was red.* And `beispiele/31-rcu.gab` is the same shape one
step worse: `BACCT_lese_ende()` stood in front of the read of the protected slot -- a read
side that leaves the RCU read section and reads afterwards is what RCU exists to prevent.

### 7.3 The repair, and what it costs the corpus

`emit.rs`, the `Return` arm: the value is produced BEFORE the releases.

* a VALUE return holds it in a local of the function's own C result type, in a block of its
  own (`{ uint32_t _rueck = z; L_gib(); return _rueck; }`), so two returns in one emitted
  block cannot redeclare the name;
* `*_wert` and `*_grund` need no local -- the store moves in front of the releases;
* a LITERAL return (`return true;`) keeps the old text byte for byte: nothing to lose, and
  that is the shape `messung/fragmente/F08.gab` and the two `rechenwerk` tests pin;
* `return;` / `return true;` without an expression are untouched.

**Measured, by emitting every tracked `.gab` before and after and comparing byte for byte:**
**12 of 317** emitting files change, and every diff is inside a `locks` block --
`beispiele/10`, `13`, `31`, `42`, `48`, `71`, `125`, `147`, `148`, `159`,
`messung/proben/probe-transport-warteschlange-aufsetzen.gab`,
`messung/proben/verbund/rennen-bewacht-bib.gab`.

**A regression on the way, and it was found by that same diff and by no test.** The first
version moved the `*_grund` store in front of the releases in one of the two reason arms and
dropped the releases entirely in the other: `warteschlange_aufsetzen`'s `GibtEsNicht` path
left the lock HELD. *A repair that loses a release is worse than the defect it repairs.* The
new cargo test `der_wert_wird_unter_der_sperre_gelesen` pins all three channels, and it was
speech-probed in both directions: with the release dropped again it fails with
*"the RELEASE stands between reason and answer -- it got lost here once"*, and it is green
with the repair in place.

### 7.4 What makes the green run a measurement

`--gift all`, four harness mutations, each caught by a DIFFERENT check:

```
GIFT 1: caught (8 findings)   emitted side back to "release, then read"  -> the answer
GIFT 2: caught (10 findings)  the twin sums 2*v                          -> the answer
GIFT 3: caught (2 findings)   the twin runs its roots sequentially       -> ONLY the overlap witness
GIFT 4: caught (10 findings)  the emitted post-join read loses its lock  -> ONLY the acquisition count
gifts: 4 of 4 caught
```

Gift 3 answers `448 193` like the green run -- it is caught because it never contends. Gift 4
answers `448` too -- it is caught because it acquires 192 times instead of 193. *Two of the
four are invisible to the answer, which is why the answer is not the whole verdict.*

**Two findings about the harness itself, both paid for once:**

1. The instrument's first run took `target/release/gabbro` because it existed -- an hour older
   than the emitter change under test -- and reported the OLD lowering's numbers against the
   new tree. It now takes the NEWER of the two binaries and ABORTS (`NOT RUN`, exit 2) when
   any `crates/**.rs` is younger than it, the same answer `pruefe-cformen.py` and
   `pruefe-saetze.py` already give. *The same class as `rsync -a` against `cargo`: a tool
   measuring a binary nobody built for it.*
2. Gift 3's mutation was a `sed` and the call it had to change spans two lines, so it changed
   nothing and the run stayed green: **`GIFT 3: NOT CAUGHT`** -- a mutation that does not
   apply looks exactly like a pass. It is a `perl -0777` now, and it also silences the two
   now-unused stacks, because a gift caught by `cc -Werror` says nothing about the run.

### 7.5 Where it runs

Both: alone (`instrumente/pruefe-nebenlaeufig-zwilling.sh`, green in 2 s) and **inside the
executed set** as stage 22b of `instrumente/pruefe-emission.sh`, which is where the acceptance
point asked for it. The whole emission run after the change:

```
== Stufe 22b: das erzeugte C gegen eine HANDGESCHRIEBENE C-Fassung (nebenlaeufig) ==
      OVERLAP emit -O0: 5 of 5 runs contended        (and the same for emit -O2, hand -O0, hand -O2)
   GREEN: emitted and handwritten agree on 20 of 20 runs
== EMISSION: ALL PASS -- 51 durchgestochen, 319 von 319 uebersetzen, 2 umgekehrte Probe(n) ==
```

### 7.6 The walls after the change

| wall | number | command |
|---|---|---|
| `cargo test --no-fail-fast` | rc 0, **1409 passed, 0 failed** (the new emitter test replaces nothing; 1409 before) | `cargo test --no-fail-fast` |
| `pruefe-emission.sh` | rc 0, **ALL PASS -- 51 durchgestochen, 319 von 319 uebersetzen**, all 12 stages | `instrumente/pruefe-emission.sh` |
| the twin instrument | GREEN, 20 of 20 runs; `--gift all` **4 of 4 caught** | `instrumente/pruefe-nebenlaeufig-zwilling.sh` |
| `pruefe-cformen.py` | GREEN: 0 new uncovered forms, 0 unclassified statements -- the new shape is a local declaration and a return of it, both already classified | `instrumente/pruefe-cformen.py` |
| `pruefe-ctext.py` | GRUEN, 2 of 2 pins byte-identical (neither pinned program holds a lock) | `instrumente/pruefe-ctext.py` |
| `pruefe-kernelmodul.sh` | GREEN, unchanged by the emitter move | `instrumente/pruefe-kernelmodul.sh` |
| `pruefe-saetze.py` | green: 470 identifiers, 198 sentences, 0 invented | `instrumente/pruefe-saetze.py` |
| `pruefe-waechter.py` | the new instrument passes all five requirements (deadline, speech test, red on abort, locale, work quantity) and adds **0** to the truncation ratchet (33 before, 33 after) | `instrumente/pruefe-waechter.py` |
| `MARKE_EMIT_M` | 156 -> **157**, dated and reasoned in `pruefe-emission.sh` (the new probe emits) | -- |

### 7.7 Two guardian findings that were NOT this lane's, and are now repaired or booked

**Repaired here, because a blind guardian is worse than a red one.** `pruefe-todo.py` was
**rc 2** at `4b8b5a7f` and at `bfb395ee`: *"the pattern for theories (bracket) hits nothing
any more"*. The document review (`6dbd581f`) reworded `(3 512 across all 15 theories)` into
`hold 3 512 lines of Isar` -- **the figures stayed right and two guardian patterns went
blind**, which is exactly the order CLAUDE.md forbids. One pattern now reads the wording the
README carries; and with the guardian measuring again it immediately reported three stale
figures, all three now pulled: `messung/KENNZAHLEN.md` 89 -> 78 metrics with a command and
179 -> 152 unguarded bold numbers, `README.md` 48 -> 50 guardians. `pruefe-todo.py` is
**ALL PASS**.

**Booked, not repaired: `pruefe-englisch.py` is rc 1, and it was rc 1 before this lane.**
Measured in a throwaway worktree at `bfb395ee` and at `4b8b5a7f`: **7965** German comment
lines in the checker against a booked 7949, **37** German feeders against 26, **5** German
messages at a sink against 2 -- three broken ratchets inherited from earlier merges, none of
them this lane's. This session's work LOWERS the first to **7964** and leaves the instruments'
half exactly at its booked 1086. *The last session's report claimed `-englisch.py` rc 0; that
claim does not hold and is corrected here.* Pulling the three ratchets straight is a
translation job across the checker's diagnostics and belongs to the language lane, not to
section 0e -- and the guardian TRUNCATES at that point, so what stands behind it was not
measured either way.

---

## 8. K4 -- `gabbro build` makes the kernel module

*Added 2026-09-28, session 2. The residue STAND.md named: until now the module was built by
`instrumente/pruefe-kernelmodul.sh` in shell, and `gabbro build` could not make one at all --
two registers over one artefact, and the one in the shell is the one a user never gets (`W7`).*

### 8.1 The manifest, and what is NOT in it

```
compiler cc -std=c11 -Wall -Wextra -Werror
out bau
kmod /home/ubuntu/Gabbro/laufzeit/kmodul /lib/modules/6.8.0-139-generic/build
unit gabbro_halde module laden entladen
  messung/proben/kmodul/halde-treiber.gab
  messung/proben/kmodul/melde.c
```

Four decisions, each with its reason:

| | |
|---|---|
| `kmod <runtime dir> <kernel build dir>` | **both named, neither guessed.** A path baked into the tree would be a fact about one machine, a kernel version a fact about one kernel |
| `unit <name> module <init> <exit>` | a third art beside `object` and `program`. A Linux module is entered by a CALL, not by a vector, so `entry … vector V` is the wrong word for it, and *what the product IS has no representative in the source* (`BAUSYSTEM.md` §1). The same `.gab` becomes an object, a program or a module by this line alone |
| a `.c` path in a module unit's file list | the body of an `extern fn` the PROGRAM declared -- that is how a kernel call enters the artefact, and why no table of Linux functions enters this tree. Outside a module unit a `.c` file is REFUSED: a hosted program with a foreign body is a gap of its own, and naming it would be a promise the build does not keep |
| the arenas are **not** in the manifest | the emitted unit carries `#define GABBRO_ARENEN &Knoten_desc` -- written by the emitter, the only thing that knows which descriptors it emitted. See §8.2 |

Measured:

```
$ gabbro build manifest
built    gabbro_halde
built 1 unit(s), 0 up to date, 0 refused -- 2 file(s) named by this manifest
$ file bau/gabbro_halde.ko
ELF 64-bit LSB relocatable, x86-64 … BuildID[sha1]=62f9db55… not stripped
$ modinfo bau/gabbro_halde.ko
description:    a Gabbro unit as a Linux kernel module
license:        Dual MIT/GPL
```

### 8.2 `GABBRO_ARENEN` -- the unit says which arenas it has

Until today every driver learned the arena list from somewhere else: the emission harness
writes `gabbro_arena_reserve(&Vorrat_desc);` by hand, and `pruefe-kernelmodul.sh` passed
`-DGABBRO_KMOD_ARENA_DESCS='&Knoten_desc'` on the command line. **An arena added to the
program and forgotten in the driver is an unreserved arena -- a null base at the first
`alloc`.** The emitter now writes the list it just emitted, under the same condition as the
descriptors (`max` stands AND the arena is used), in declaration order. Corpus reach,
measured: **4 of 317** emitting files gain the line (`beispiele/158-arena-commit.gab`, the two
`arena-h4` twins, the kernel-module probe); `laufzeit/kmodul/kmodul.c` reads it instead of its
`-D`, and the harness no longer names an arena at all.

### 8.3 The refusals, and where each would otherwise have surfaced

The module rule runs BEFORE any C is written, beside the entry rule and the driver rule --
and in `--dry-run` too, so it needs no kernel and no compiler:

| refused | otherwise |
|---|---|
| an init/exit the unit does not declare | *implicit declaration of function*, in a `make` log |
| one that takes an argument | the module passes nothing and the function reads a register nobody set |
| one that answers nothing | **`module_init` has no verdict, and a refused load looks like a good one** |
| the same name for both | loading and unloading are not one call |
| a `module` unit declaring `pub fn main` | a name the loader never calls and the kernel never links |
| a `module` unit without a `kmod` line, and a `kmod` line without a module unit | a claim nobody keeps, in both directions |
| a `.c` file in a non-module unit | silently compiled into nothing |

Held by `crates/gabbro-cli/tests/bausystem.rs` (6 new tests, `--dry-run` so they need no kernel
headers): `cargo test --no-fail-fast` **1415 passed, 0 failed** (1409 before).

### 8.4 The instrument now builds through the build

`instrumente/pruefe-kernelmodul.sh` writes a manifest and calls `gabbro build`; the Kbuild, the
runtime copies and the `-D`s are gone from the shell. It still owns what only it can own: the
QEMU boot, the expected kernel lines, and the four mutations. **4 of 4 caught, unchanged**, and
the green run is the same as before:

```
HARNESS: insmod ok / rmmod ok
gabbro-halde: k=1 v=0    k=2 v=33    k=3 v=3    k=9 v=0
GREEN: loaded, allocated, refused on full, reported, unloaded clean.
```

Gift 4 (the one that found the `module_init` defect in session 1) keeps working and keeps its
meaning: it mutates the EMITTED C inside the build directory `gabbro build` left behind and
re-makes with the `Kbuild` the build wrote -- so it carries no second copy of the recipe
either. *Mutating the source instead would be refused by `N426` one door earlier, and then the
fail-stop never runs.*

### 8.5 A third instance of one trap, and the register it got

`miss-arena-decke.sh` was the third instrument in one day to measure a STALE binary -- and its
verdict was the worst kind: **GREEN over the wrong bytes.** It had taken
`target/release/gabbro` because it existed, from before the emitter change under test.

`instrumente/binaer.sh` is now the one register: take the NEWER of the two profiles, and if any
`crates/**.rs` is younger than it, refuse with a reason and return 2 -- *a binary older than a
source is an ABORT, not a finding.* All three instruments source it.
`pruefe-waechter.py` books it as a sourced library (like `abschnitt.sh`) and DRIVES its speech
probe in both directions on a throwaway tree: a newer binary comes back, an older one is
refused with `OLDER than 1 source file`.

H4 re-measured with a release binary built from this tree (the numbers moved because the
emitted C gained the arena list, not because the ceiling costs anything):

```
                        max 1310720 (10 MiB)   max 4294967295 (32 GiB)
translate (ms, best of 5)                5                         5
emitted C (bytes)                     3512                      3524
emitted C (lines)                       76                        76
binary (bytes)                       16488                     16488
binary .bss (bytes)                     24                        24
GREEN: the ceiling costs nothing        (`--gift` still caught)
```

### 8.6 The walls after K4

| wall | number | command |
|---|---|---|
| `cargo test --no-fail-fast` | rc 0, **1415 passed, 0 failed** | `cargo test --no-fail-fast` |
| `pruefe-emission.sh` | rc 0, **ALL PASS -- 51 durchgestochen, 319 von 319 uebersetzen**, all 12 stages | `instrumente/pruefe-emission.sh` |
| kernel module in QEMU | GREEN, `--gift all` 4 of 4 caught, built by `gabbro build` | `instrumente/pruefe-kernelmodul.sh` |
| the concurrent twin | GREEN, 20 of 20 | `instrumente/pruefe-nebenlaeufig-zwilling.sh` |
| H4 | GREEN, `--gift` caught | `instrumente/miss-arena-decke.sh` |
| `pruefe-cformen.py`, `pruefe-ctext.py`, `pruefe-todo.py`, `pruefe-saetze.py` | rc 0 each | -- |
| `pruefe-waechter.py` | rc 1, and **one pre-existing hole fewer**: `pruefe-kernelmodul.sh` no longer lacks its speech-probe word. The five remaining `FEHLT` rows and the truncation ratchet (33) are unchanged and none of them this lane's | `instrumente/pruefe-waechter.py` |
| `grammatik` Lean build / `#print axioms gabbro_ziel` | 355 jobs no error / `[propext, Classical.choice, Quot.sound]` | `cd grammatik && lake build`, `lake env lean Nachpruefung.lean` |

---

## 9. Session 3 (2026-09-28) — H3: the Lean form of the dynamic arena, the `Spec.lean` texts, and the `atomic` refusal

*Everything below is measured on `ubuntu@simon.jocraft.cc`, in `~/Gabbro`. Isabelle is not
installed here, so `abnahme.py --voll` cannot run; that is said again at the end.*

### 9.1 What was open, and what closed

Session 2 left the TODO §0e box 1 residue as **H3** — the Lean `ArenaDyn` form and the two
`Spec.lean` (d) assumption texts — and box 3's residue as *a Gabbro `atomic` in a kernel
module*. Both are closed here. **K2/K3 (box 2) is not**, and §9.7 says what it is.

### 9.2 `ArenaDyn.lean` section `Form` — the section-9 residue

`grammatik/Grammatik/ArenaDyn.lean` carried the model of a dynamic arena as **arithmetic on a
`Nat` record**: what a commit sequence does, said about numbers. What PLAN-DYNAMISCH §9 asked
for and the file's own tail comment listed as missing was the same discipline **as a form over
the existing `Block`** — so that `theorem gabbro_ziel` covers a dynamic-arena program with no
new constructor, no new machine arm and no re-proof, exactly as `ArenaZucker.lean` does for the
static one.

Built:

| | what it is |
|---|---|
| `DynForm D` | an `ArenaForm D` whose table spans the CEILING (`count tab = M`), plus a second global — the committed prefix — over the same range, read through the `stand`-style accessor `komSt`. The field `hzwei : komm ≠ zaehl` is what every frame lemma rests on |
| `Block.dynGrowB` | `grow A by n else B;` — `Block.narrow` of `committed + n` into `0 .. M` with the store. It fits and the word takes it, or `B` runs; past the ceiling there is no other branch |
| `Block.dynAlloc` | `let i = alloc A (v) else B;` on a dynamic arena — `Block.pruefung` on `used < committed` (no binder, an `else` that does not fall through) with **`Block.arenaAlloc` taken from `ArenaZucker.lean` UNCHANGED** underneath |
| `dynGrow_commit` | the commit bumps the word by `n` — **and the frame**: the used counter stands where it stood, `slots` is `slots` |
| `dynCommit_monoton` | no admitted `grow` lowers the committed word |
| `dynAlloc_unter_commit` | below the committed prefix the `else` is not taken; the body is `arenaRumpf`, the index the old used counter. The model half of R-commit |
| `dynAlloc_ueber_commit` | at or above it the `else` IS taken — **with room to the ceiling**. The whole difference between a reservation and storage |
| `dynAlloc_simuliert` | the simulation: under the committed prefix the dynamic form IS the static-max form, run on a world that differs only in the trace — and the difference is measured (`globs` equal, `slots` equal) |

**The estimated blocker did not exist.** The file's tail comment put the alloc pair at
*"40–80 lines of dependent plumbing each"* for a narrow-on-committed sugar. There is no such
narrow: `committed` is a runtime word and `Block.narrow` takes static bounds, so the guard is a
`pruefung` and the static narrow underneath is the one that already stood. The pair is 20 lines
of statement and 10 of proof, and it **reuses** `arenaAlloc_unter_schranke` /
`arenaAlloc_an_schranke` instead of restating them.

**The witnesses are not decorative** (memory `zeugenpflicht`). `DynZeuge.DD` is a declaration
with one four-slot table and **two** globals; `Halde` is the arena over it; `halb` has the used
counter at 0 and the committed prefix at **2 of 4**, and `gespannt` has both at 2. So
`zeuge_alloc_ueber` is *an arena with two free slots whose allocation is refused* — the one
state the static form cannot name — and `zeuge_grow` moves the prefix 2 → 4 while the used
counter and every slot stay put.

```
$ cd grammatik && ~/.elan/bin/lake build
Build completed successfully (355 jobs).
$ cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean | grep gabbro_ziel
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every new theorem prints its axioms in the file (`#print axioms`, 15 new lines): all
`[propext, Classical.choice, Quot.sound]` or fewer. No `sorry`, no `axiom`, no
`native_decide`.

### 9.3 The `Spec.lean` diff — two texts, no premise

Measured: **36 insertions, 1 deletion, all inside the header comment.**

```
$ git diff --stat -- grammatik/Grammatik/Zielsatz/Spec.lean
 grammatik/Grammatik/Zielsatz/Spec.lean | 37 +++++++++++++++++++++++++++++++++-
```

Session 2's hand-over read `Laufzeit.reserve` and `Laufzeit.commit` as new **fields**, and
measured the cost: five construction sites plus every generated certificate. **This session did
not do that, and the reason is the deliverable.** A field of `Laufzeit` is a premise of
`GabbroZiel`, and a premise added is a theorem weakened. For `reserve` the premise is already
there: an arena IS a table of `M` slots in `E.sp0`, so a load that cannot provide the range
establishes no `E.sp0` and `Laufzeit.lader` is false of it. For `commit` the first clause is now
**proved** — `dynGrow_commit` says the form has exactly two outcomes — and assuming what the
model proves would put the claim in the premise, where a later weakening of the theorem would
not show.

What is left is a statement about the C runtime, which is where the two texts now stand, with
what each runtime does (`mmap(PROT_NONE)` hosted, the carved region on metal, one `vzalloc`
region per arena in a kernel module) and with the explicit NOT CLAIMED: *that the reservation
succeeds*. Full review, including the checklist a reviewer should attack:
**`messung/SERVER-0E-SPEC-DIFF.md`**.

### 9.4 The gap the diff made visible

Writing the NOT CLAIMED clarification forced a measurement:

```
$ grep -n "StmtArt::Grow" crates/gabbro-check/src/lean_g.rs
4189:        StmtArt::Grow(g) => Err(refuse("LG005", …))
```

**The exporter refuses `grow` (`LG005`)** and builds the static `ArenaForm` over `hi`, not over
the ceiling. So the new forms are covered by `gabbro_ziel` — they are ordinary `Block` terms —
but **no dynamic-arena program is CERTIFIED**, and for an uncertified program a green build
says nothing. Named in three places so it cannot be read past: the `Spec.lean` NOT CLAIMED
line, the `ArenaDyn.lean` cuts, and §5 of the diff review. Not closed here; it is exporter work.

### 9.5 A Gabbro `atomic` in a kernel module — the refusal moved to the build

Before: `laufzeit/kmodul/include/stdatomic.h` `#define`s `_Atomic` to an unknown identifier. A
real refusal in the right place — but it arrives as **a C error inside a `make` log**, over a
generated prelude line, after the build has decided the unit is fine.

Now `gabbro build` refuses it before a byte of C is written, naming the declaration:

```
REFUSED  gabbro_probe (module): this `module` declares the atomic `STAND` ((top level) in …/u.gab)
         -- a Gabbro `atomic` has no kernel-module lowering
         = C11 `_Atomic` is not the kernel's memory model (`READ_ONCE`/`WRITE_ONCE`, `atomic_t`,
           `smp_*` barriers), and the goal theorem's atomic rely (`SchwachX`) is proved about the FIRST one
         = lifting it needs a lowering onto the kernel's own primitives AND the argument that the
           kernel's model refines the one `SchwachX` assumes; neither is built
         = without this rule the refusal is `laufzeit/kmodul/include/stdatomic.h`'s, in a `make` log
```

`crates/gabbro-cli/src/bau.rs`: `AtomarFund`, one more arm in `sammle` (the SAME parse — no
second reading of the text, W7), and the new head of `modulregel`. The header stays as the
second answer, for a hand-written `Kbuild`; a rule only the build system knows is a rule the
kernel build can walk around. One CLI test with **its positive twin**
(`ein_modul_mit_atomic_faellt`): without the twin the test would also pass on a rule that
refused every module. A manifest-level refusal has no `Satz`, so no `N` code is minted — the
reading `treiberregel` and the module rule already stand on.

*Why a refusal and not a lowering:* safety is never traded for features. A lowering onto
`atomic_t` that nobody has related to `SchwachX` makes the wall green and the claim false.
What lifting it needs is written down: **OFFEN O34**.

### 9.6 The walls at the end of session 3

| wall | number | command |
|---|---|---|
| `cargo test --no-fail-fast` | rc 0, **1416 passed, 0 failed** (1415 + the new CLI test) | `cargo test --release --no-fail-fast` (`~/claude-lane/logs/test-s3.log`) |
| `pruefe-emission.sh` | rc 0, **ALL PASS — 51 durchgestochen, 319 von 319 uebersetzen, 2 umgekehrte Proben** | `instrumente/pruefe-emission.sh` (`~/claude-lane/logs/emission-s3.log`) |
| kernel module in QEMU | GREEN: loaded, allocated, refused on full (`k=3 v=3`), reported, unloaded clean | `instrumente/pruefe-kernelmodul.sh` |
| H4, the ceiling | GREEN, `.bss` 24/24, `.data` 64/64, answer 33/33 | `instrumente/miss-arena-decke.sh` |
| `grammatik` Lean build | 355 jobs, no error | `cd grammatik && lake build` |
| `#print axioms gabbro_ziel` | `[propext, Classical.choice, Quot.sound]` | `lake env lean Nachpruefung.lean` |
| `pruefe-todo.py`, `-saetze.py`, `-cformen.py`, `-ctext.py` | rc 0 each | — |
| `pruefe-zahlen.py` | rc 1, **35 findings — 36 at `d03f5d5b`**. Measured in a throwaway worktree at the base: the same 36, and the one that differed was the widerruf file count (689 → 690, my new document). `KENNZAHLEN.md` re-measured to 690; the other 35 are document-figure drift from the translation work and none is this lane's | `instrumente/pruefe-zahlen.py` |
| `pruefe-englisch.py` | rc 1, **unchanged**: 7964 German comment lines (booked 7949), 37 German feeders (26), 5 German messages at a sink (2) — the same three numbers session 2 measured. Everything this session wrote is English | `instrumente/pruefe-englisch.py` |
| `pruefe-waechter.py` | rc 1, the same five `FEHLT` rows and truncation ratchet (33), all pre-existing | — |
| `pruefe-kennungen.py` | rc 1, `N004`/`N005` assigned in both `namen.rs` and `zielbindung.rs` — pre-existing (Opus lane L), no code minted here | — |
| `pruefe-syntax.sh` | rc 1, 17 build warnings, all in files this session did not touch (`gabbro-check`, `bau.rs:1847` `KMOD_QUELLEN` from session 2) | — |
| `pruefe-manifest.py` | rc 1, the long-standing obligations gate (43 of 63), untouched | — |
| `abnahme.py --voll` | **cannot run here**: no Isabelle on this machine | — |

### 9.7 What is still open in §0e, and it is one box

**Box 2, K2/K3.** In order: `start` lowering (`C001`) and export (`LG004`, no model of
statement-level starts); then the `entry`/`boot` vector, registers and steps (today only the
dispatch root travels); then handler pinning/re-entry and `cli`/`sti` in the C (OFFEN O19 — the
model leg `KernHaltE` stands, the C masks nothing). The kernel module built here has neither a
`start` nor an `entry`: its init and exit are ordinary functions, which is what a Linux module
is entered by — so K4/K5 did not need K2/K3, and that is why the two boxes could close first.

**Not a residue, a recorded refusal:** a Gabbro `atomic` in a kernel module (OFFEN O34), and
the exporter's `LG005` (§9.4).
