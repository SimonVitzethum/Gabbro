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

**Box 2 — and K2 turned out to be stale, like box 1's row was on 2026-09-28.** Measured
here, with the commands:

| half | what the row said | what is there |
|---|---|---|
| `start` LOWERING (`C001`) | open | **stands.** `./target/release/gabbro emit beispiele/159-laufzeit-start.gab` → **0 `C001`**; the C calls `gabbro_faden_start` per root with its own stack and join word (`gabbro_stapel_0_0 + 65536u`, `&gabbro_wort_0_0`) and `__builtin_trap()`s on the same line when the kernel refuses (lane 260). The emitter refuses only shapes the checker already owns (`N459`–`N462`) |
| `start` EXPORT (`LG004`) | *"no model of statement-level starts"* | **there is a model.** The `StmtArt::Start` arm of `lean_g.rs` is `tr_rest` — it refuses nothing — and the roots travel as `gE.gestartet` (`check_gestartet`): spawn and join are steps of the THREAD machine (Opus agent A, `FadenSchritt.start`/`.join`). What the model does NOT fix is the statement's own point among the lock-free spawn points; it over-approximates, and that is OFFEN O22, recorded |

**What is actually missing is a PROGRAM, not a form.** The corpus has exactly one
statement-level `start` (`beispiele/159-laufzeit-start.gab`), and the exporter refuses it for
reasons that have nothing to do with `start`:

```
$ ./target/release/gabbro lean-g beispiele/159-laufzeit-start.gab
gabbro lean-g: [LG002] field stand is wrapping
# with `wrapping` replaced by a bounded field and the increment guarded (scratch copy):
gabbro lean-g: [LG004] function lauf falls off with a result
```

— the second is its tail being a `locks` block whose `return` stands inside. So no `start`
program is CERTIFIED yet, and closing that is **exporter-fragment work**, not `start` work.

**K3 is the box.** The `entry`/`boot` vector, registers and steps (today only the dispatch
root travels); then handler pinning/re-entry and `cli`/`sti` in the C — OFFEN O19, where the
model leg `KernHaltE` stands and the C masks nothing.

The kernel module built here has neither a `start` nor an `entry`: its init and exit are
ordinary functions, which is what a Linux module is entered by — so K4/K5 did not need
K2/K3, and that is why the other two boxes could close first.

**Not a residue, a recorded refusal:** a Gabbro `atomic` in a kernel module (OFFEN O34), and
the exporter's `LG005` (§9.4).

---

## 10. Session 4 (2026-09-28) — K3's C half: `masks irqs` is realised in a kernel module, and `H102` reaches it

**The headline, in one line.** A `module` unit with ONE `lock` did not link at all before this
session; now it does, a `masks irqs` lock becomes `raw_spin_lock_irqsave`, and the promise is
measured in QEMU against a real hardirq contender. Beside it the checker's trigger for "an
entry the hardware throws" stopped being the literal word `idt`.

### 10.1 What was measured FIRST, because the row said something else

The TODO row read *"the C still masks nothing — OFFEN O19"*. **For bare metal that was stale**
(the fourth stale row of §0e in one week): Opus agent J closed it, and `crates/gabbro-cli/src/treiber.rs`
picks `METALL_SPERRE_MASKIERT` for a `masks irqs` lock, which clears IF from before the ticket
is drawn (`laufzeit/metall/metall.h`). What was NOT stale is the third target — the one K4 built:

```
$ cat > sperre.gab   # a module unit with one `lock TAKT … masks irqs`
$ ./target/release/gabbro pruefe sperre.gab
sperre.gab: 7 items, 0 errors, 0 hints
$ ./target/release/gabbro build manifest
ERROR: modpost: "TAKT_gib"  [gabbro_sp.ko] undefined!
ERROR: modpost: "TAKT_nimm" [gabbro_sp.ko] undefined!
```

**The checker passed it without a word and the kernel's own linker refused it.** The emitter
declares `L_nimm`/`L_gib` and defines neither (the primitive is trust base, not product); the
hosted and the bare-metal drivers are GENERATED and define them from the build's lock list, and
`laufzeit/kmodul/kmodul.c` — which is deliberately not generated — had no way to learn them.

### 10.2 What was built

| | |
|---|---|
| `laufzeit/kmodul/sperre.h` | the primitives, four kinds. PLAIN is `raw_spin_lock`, **MASKED is `raw_spin_lock_irqsave`**, the two SHARED kinds take the same exclusive lock (stronger than asked, never weaker — the choice `METALL_SPERRE_GETEILT` already makes). `raw_spinlock_t` and not `spinlock_t`, because on `PREEMPT_RT` the latter sleeps and a declared `held <= N ops` would mean nothing |
| `sperren.h`, written by `gabbro build` | one `#define GABBRO_SPERREN(F)` with an `F(name, kind)` per lock, out of `TreiberPlan::sperren` — **the same register the other two drivers read**, one `ItemArt::Lock` walk in `bau.rs::sammle` (`W7`) |
| `gabbro_halter_L` | the observation, not the primitive: the core holding the lock, or −1. The kernel-module twin of metal's `metall_anspruch_L[core]` |
| `messung/proben/kmodul/sperre-takt.gab` + `takt.c` | the probe: the lock held across a 4096-slot traversal, 64 rounds, while the program's OWN C runs a 50 µs hardirq `hrtimer` whose body takes the same lock |

**The lock list does NOT go into the emitted C, and that was measured the hard way.** It stood
there first (`#define GABBRO_SPERREN(F)`, beside `GABBRO_ARENEN`), and the translation-validation
chain refused it:

```
$ cd grammatik && lake build
error: Grammatik/CText104.lean:116:0: Not a definitional equality: the left-hand side
  parseC ctext104   is not definitionally equal to   some (kFuns zert104)
```

The Lean `CParser` reads preprocessor lines with a CLOSED grammar (`#include <x.h>` and an
integer `#define`, `CParse.lean::direktiveC`), so a function-like macro makes `parseC` answer
`none` and `a2_104 := rfl` stops being a proof. **Widening the parser to skip a directive it
cannot evaluate would have been the wrong repair** — a macro the parser ignores may rename
anything below it, and that is a soundness hole in the chain, not a formatting question. The
list moved to the build instead, where its register already was. *Cost of the detour: the
emitted C of the whole corpus is byte-unchanged, `MARKE_EMIT` did not move for it, and the
`CText104` pin stands as it did.*

### 10.3 The measurement in QEMU

```
$ ./instrumente/pruefe-kernelmodul.sh
-- probe takt: gabbro_takt
   [    3.204554] gabbro-takt: k=1 v=0
   [    3.206511] gabbro-takt: ticks=26 landed=0
   [    3.218482] gabbro-takt: k=9 v=0
GREEN: halde -- loaded, allocated, refused on full, reported, unloaded clean.
GREEN: takt  -- a masks-irqs lock held across a long section, a hardirq timer
                taking the same lock, and 0 arrivals on a holding core.
```

`ticks` is the half that makes `landed` mean anything: **26 hardirq arrivals** during the run
(25–32 across runs), **0 of them on a core that was holding the lock**. A run in which the timer
never fired would report a clean `landed` and have measured nothing, so the verdict demands
`ticks >= 5` — and gift 6 is exactly that case.

Disassembly of the built module, so the claim is about the artefact and not about the source:

```
$ objdump -dr gabbro_takt.ko --disassemble=TAKT_nimm | grep R_X86_64
    21: R_X86_64_PLT32   _raw_spin_lock_irqsave-0x4
$ objdump -dr gabbro_takt.ko --disassemble=TAKT_gib | grep R_X86_64
    82: R_X86_64_PLT32   _raw_spin_unlock_irqrestore-0x4
```

**Poison: 7 of 7 caught** (`--gift all`, 1 min 39 s). The three new ones:

| gift | mutation | why the run turns red |
|---|---|---|
| 5 | `sperren.h`: `F(TAKT, MASKED)` → `F(TAKT, PLAIN)`, module re-made with the `Kbuild` the build wrote | the timer body lands inside a critical section on the core that holds it and waits for that core. **The run does not finish** — the same answer `pruefe-metall.sh`'s `metall59-gift` gives. This is the poison probe of the masking ITSELF |
| 6 | the program's own C: timer period 50 µs → 50 s | `ticks=0`, and a clean `landed` over zero opportunities is not a measurement |
| 7 | the expectation `landed=0` → `landed=1` | does the run read the kernel log, or only the exit codes? |

*Gift 5 caught the instrument once, in the right direction:* when the lock list moved out of the
emitted C, the mutation stopped applying and the gift read **NOT CAUGHT**. A gift that does not
apply looks exactly like a pass, so it now checks that its target is there before mutating it.

### 10.4 The checker half: the trigger was the word `idt`, and now it is a `via` word

`Kontext::unterbricht` — the one answer to *"can this entry preempt?"* — was
`e.via.text == "idt"`. Two shapes walked past it, and both read as a pass:

* **a misspelt path.** `via ipt` is not `idt`, so `H102` said nothing at all about a declaration
  that plainly means "hardware throws this". *A measuring instrument that goes quiet on a typo
  is the `W16` class.*
* **a host kernel's interrupt path.** A Gabbro unit built as a Linux module is entered from a
  timer or a device line, which owns no vector the program could name — so `via idt vector N` is
  the wrong word and `via irq` is the right one, and the rule did not look at it.

Widened in the three places that must agree: `kontexte.rs` (`H102`), `lean_g.rs`
(`gP.unterbricht`, so the model's handler set stays the Rust one exactly) and the source-reading
pattern of `instrumente/pruefe-akzeptiert-diff.py` (K6) — **the pattern in the same commit as
the rule**, because a pattern that lags behind its rule is a green run that measures nothing.
`bau.rs`'s `via_idt` stays the literal word: it decides an IDT slot, and `via irq` is not one.

**Measured, and it is strictly stronger.** The corpus carries NINE `via` words at an `entry` and
every one is `idt` (`grep -rhno 'via [a-z_]*' --include=*.gab .`), so no corpus file moves:

```
$ ./target/release/gabbro pruefe beispiele/gift/1364-eintritt-via-anderem-pfad.gab
error: [H102] … `zeitgeber` is thrown by hardware and takes `TAKT`, which does not declare `masks irqs`
   (0 errors before the widening — the file used to pass)
$ ./target/release/gabbro pruefe beispiele/166-eintritt-irq-maskiert.gab
beispiele/166-eintritt-irq-maskiert.gab: 6 items, 0 errors, 0 hints
```

The example is the half that keeps it a rule and not a ban: `H102` must be SILENT where the
language speaks the remedy. 166 also EXPORTS, so the model carries it
(`grammatik/Grammatik/Zertifikat/G166_eintritt_irq_maskiert.lean`, `unterbricht | .takt_verteiler => true`;
27 CERTIFIED of 208 accepted, was 26 of 207), and `pruefe-akzeptiert-diff.py --selbsttest` is green
in both directions (`masken` accepts 59, refuses the `gift/460` shape at `masken` alone).

### 10.5 Two defects found on the way, both in this lane's own earlier work

1. **`KMOD_QUELLEN` was declared and read by nobody.** `cargo build` had been saying
   `constant KMOD_QUELLEN is never used` since K4 wrote it; the effect was that a changed
   `kmodul.c` left a stale `.ko` standing as up to date. It is in the fingerprint now, with
   `sperre.h` added — which made the hole load-bearing: a module whose LOCKS changed would not
   have been rebuilt.
2. **`metallregel` refused a module unit's entry for the bare-metal driver's reason.** An
   `entry … via irq` with no vector was refused with *"the bare-metal driver cannot name its IDT
   slot"* — an artefact a `module` unit never gets. *A refusal whose reason names an artefact
   nobody asked for is a refusal in the wrong place.* The metal half of the driver rule is now
   gated on the unit's art; the checker still holds the declaration (`H102`), and the twin in
   `bausystem.rs` shows the same unit as an `object` still refused, so the rule was gated and
   not deleted.

Also repaired: a unit with LOCKS and no roots had no `TreiberPlan` at all, so its lock list came
out empty and the module did not link. It gets a plan now; it still owns no driver
(`hat_gehostet`/`hat_metall` both false), and the dry run says so instead of naming a
`.treiber.c` the build does not write.

### 10.6 What K3 still owes, named so it cannot be read past

* **A Linux hardirq callback is not an `entry` the module BUILD can carry.** The probe's
  contender is the program's own C calling a `pub fn`, and the entry declaration that WOULD give
  `H102` its door is not in the probe: a `module` unit may now declare one (10.5), but nothing in
  the build can check that the program's C actually hands that stub to the kernel — the module
  target has no twin of the metal `N561` (`eintritt.bindung`). So for the probe as it stands the
  masking is REALISED and not CHECKED; with the entry declared it is both, and the binding is the
  assumption. **OFFEN O19, the module row.**
* **The model half of K3 is untouched:** the vector, the registers and the steps still have no
  form in `Einheit` (only the dispatch root travels), and handler pinning and re-entry stay
  outside `KernPlan` (in G a handler thread runs once). That is Lean and exporter work.
* `beispiele/57`'s `halt_ipi vector 0xF0` writes no `via` at all and stays silent — the gap in
  the LANGUAGE that `saetze.rs` names under `H102`, unchanged by this session.

### 10.7 The walls at the end of the session

| wall | result |
|---|---|
| `cargo test --release --no-fail-fast` | rc 0, **1420 passed, 0 failed** (`~/claude-lane/logs/test-s4.log`) |
| `./instrumente/pruefe-emission.sh` | rc 0, **ALL PASS — 51 durchgestochen, 321 von 321 uebersetzen, 2 umgekehrte Proben** |
| `cd grammatik && lake build` | 356 jobs, no error; `#print axioms gabbro_ziel` = `propext, Classical.choice, Quot.sound` |
| `./instrumente/pruefe-kernelmodul.sh` | GREEN on both probes; `--gift all` **7 of 7 caught** |
| `./instrumente/pruefe-akzeptiert-diff.py` | all ten pins hold on 29/29 comparable programs; `--selbsttest` ok both directions |
| `pruefe-todo.py`, `-saetze.py`, `-cformen.py`, `-ctext.py`, `-widerruf.py` | rc 0 |
| `pruefe-zahlen.py` | rc 1, **35 findings — exactly the base's 35**, measured in a throwaway worktree at `ab260581` and diffed line by line. The one that moved (widerruf file count 690 → 691) is re-measured in `KENNZAHLEN.md` |
| `pruefe-englisch.py`, `-kennungen.py`, `-syntax.sh`, `-manifest.py`, `-waechter.py`, `-vergabe.py`, `-klauseln.py`, `-sondendeckung.py` | rc unchanged against the same base, output identical but for file and line counts. `pruefe-syntax.sh` is **17 → 15** build warnings (the dead `KMOD_QUELLEN` went) |
| `abnahme.py --voll` | **cannot run here**: no Isabelle on this machine |

**Emission counters re-measured and dated:** `MARKE_EMIT` 142 → 143 (`beispiele/166`),
`MARKE_EMIT_M` 157 → 158 (`messung/proben/kmodul/sperre-takt.gab`). `MARKE_EMIT_G` untouched:
the poison twin does not emit.

*And one finding came from the clang half of stage 9, which is what it is for:* the probe's round
counter `Runden` was only a traversal DOMAIN, so its storage was never touched and `clang`
refused the emitted `static Runden Runden_speicher` as `-Wunneeded-internal-declaration` while
`cc` took it. The probe marks each round now.

**Ledger:** gift **1364**, example **166**. No new `N` code — `H102` keeps its name and its
sentence; what changed is its trigger, and the sentence says so with the measurement beside it.

---

## 11. Session 5 (2026-09-28) — K6: a Gabbro `atomic` becomes the kernel's own memory model

*Acceptance point **4b**. Everything below was run on `ubuntu@simon.jocraft.cc`; every number
has its command beside it. Isabelle is not installed here, so `abnahme.py --voll` was not run
and is not claimed.*

### 11.1 What the session was handed, and what it is

Session 3 had REFUSED an `atomic` in a `module` unit before a byte of C was written, and
recorded what lifting it needs as OFFEN **O34**: *(1) a lowering onto the kernel's own
primitives; (2) the argument that the kernel's model refines the one `SchwachX` assumes.*
Simon tasked the lift the same day (`AUFTRAG-1.md` K6) and fixed the shape of (2): **a named
assumption, not a Lean proof of LKMM refinement**, architecture-neutral, naming what it relies
on per ordering.

So the refusal is now a table. The whole of the emitter's surface, measured before anything was
written (`gabbro emit` over `git ls-files beispiele messung/proben`):

| | |
|---|---|
| call forms the emitter can write | **nine** — two access arms, five `holform` rows, two compare-exchange arms |
| orderings per form | load `{relaxed, acquire, seq_cst}`, store `{relaxed, release, seq_cst}`, fetch `{relaxed, acq_rel, seq_cst}`, compare-exchange three PAIRS |
| in the corpus's emitted C | 61 loads, 45 stores, 9 weak CAS, 6 strong CAS, 2 `fetch_or`, 1 `fetch_and`, 1 `fetch_xor`; 71 atomic objects of types `bool`, `uint32_t`, `uint64_t` |

**A closed surface is what a header can cover completely**, and that decided where the mapping
goes.

### 11.2 The lowering, and why it is a header and not the emitter

`laufzeit/kmodul/include/stdatomic.h` — until this session a REFUSAL (`_Atomic` `#define`d to
an unknown identifier), now the mapping. Two reasons for the header, and the first is a hard
constraint of this tree:

1. **The emitted C is pinned byte for byte** in the translation-validation chain
   (`grammatik/Grammatik/CText104.lean`, `a2_104 := rfl`). An emitter that wrote
   `smp_load_acquire` for one target and `atomic_load_explicit` for another would fork the
   artefact the chain reads. *Measured: `0` bytes of emitted C change anywhere in this
   session.*
2. The surface is closed, so a form or ordering NOT in the table pastes to an undefined name
   and the kernel build stops. Silence is not among the answers.

The rows, each at least as strong as the C11 operation it replaces, and argued from the
kernel's portable API and not from x86-TSO (aarch64 and RISC-V come later):

| C11 | kernel | what it relies on |
|---|---|---|
| load relaxed | `READ_ONCE` | single-copy atomicity for an aligned 1/2/4/8-byte scalar |
| load acquire | `smp_load_acquire` | the kernel's acquire load, on every architecture |
| load seq_cst | `smp_mb` + acquire + `smp_mb` | the leading/trailing-fence mapping of an SC load |
| store relaxed | `WRITE_ONCE` | as above, write side |
| store release | `smp_store_release` | the kernel's release store |
| store seq_cst | `smp_mb` + `smp_store_mb` | the leading/trailing-fence mapping of an SC store |
| fetch_\* relaxed | `try_cmpxchg_relaxed` loop | a successful cmpxchg is ONE read-modify-write |
| fetch_\* acq_rel | `try_cmpxchg` loop | the unsuffixed form is fully ordered — stronger, never weaker |
| fetch_\* seq_cst | `smp_mb` + loop + `smp_mb` | as above, with the SC fences |
| CAS (relaxed, relaxed) | `try_cmpxchg_relaxed` | same shape and same answer as C11's |
| CAS (release, acquire) | `try_cmpxchg_release`, **`smp_mb` on FAILURE** | see below |
| CAS (seq_cst, seq_cst) | `smp_mb` + `try_cmpxchg` + `smp_mb` | the fences carry both paths |

**The failure path of a compare-exchange is the one place the obvious mapping would be
WEAKER**, and it is the finding of this session's design half. C11 gives a compare-exchange two
orderings and the emitter writes `(release, acquire)`; in the Linux model a failed `cmpxchg`
implies **no ordering at all — not even in the unsuffixed, fully ordered form**
(`Documentation/atomic_t.txt`). Dropping that `smp_mb()` would have been sound on success and
unordered on failure, and *no wall in this tree would have shown it, because x86 hides it.*

`_Atomic` becomes `volatile`. That is not the atomicity — it is the damage limit: it buys
strictly less than `_Atomic` and strictly more than nothing, and it is not a reason to skip the
access check below. What the header still REFUSES, each with its own sentence: a
floating-point `atomic` (a `_Generic` whose controlling expression costs no load), a
read-modify-write of a width the target's native `try_cmpxchg` does not cover
(`_Static_assert`), and any unlisted (form, ordering) pair. All three measured against a
scratch module (`~/claude-lane/kratz/s5/atomtest`, `make -C /lib/modules/$(uname -r)/build`):

```
bad1 (_Atomic double)            error: static assertion failed: "a Gabbro `atomic` of floating-point type has no kernel-module lowering: …"
bad2 (fetch_add on a u16)        error: static assertion failed: "a read-modify-write on this `atomic` needs a cmpxchg of its width …"
bad3 (memory_order_consume)      error: implicit declaration of function 'GABBRO_KMOD_LADEN_memory_order_consume'
```

### 11.3 The build refusal, narrowed and not dropped

`crates/gabbro-cli/src/bau.rs`, `modulregel`: the blanket refusal of every `atomic` became the
refusal of the FLOATING-POINT one, with the reason no barrier repairs (kernel code may not use
the FPU without `kernel_fpu_begin`/`_end`, which nothing declares). `AtomarFund` carries the
one bit the rule now needs, and an array of floats is a float atomic (`_Atomic` qualifies the
ELEMENT type). The CLI test holds all four directions —
`ein_modul_mit_atomic_wird_gesenkt_und_ein_gleitkomma_atomic_faellt`:

```
$ cargo test --release --test bausystem
   16 passed; 0 failed
```

**The `u32` half is asserted FIRST**, deliberately: a rule that kept refusing every atomic
would leave the test green while the lowering beside it went unused.

### 11.4 A module's `concurrent` roots become kernel threads (K2's module half)

The probe for 4b needs two threads, and the honest way to have them is for the PROGRAM to
declare them. Before this session that did not work: `TreiberPlan` did not know the unit's art,
so `hat_gehostet()` was true for a `module` with a `concurrent` set and **a hosted pthread
driver was written beside its `.ko`** — a file for a world the module is not in.

- `TreiberPlan` carries the art; `hat_gehostet`/`hat_metall` answer false for a module and
  `hat_kmod_faeden` answers for it. Unit test `die_art_entscheidet_welcher_treiber`: the three
  predicates are exclusive, and the ROOT LIST is the same list either way — one walk.
- `gabbro build` writes `wurzeln.h` (`#define GABBRO_WURZELN(F) F(a) F(b)`, name order, one
  line) out of the same walk `sperren.h` comes from. Unit tests `wurzelliste_tests`.
- `laufzeit/kmodul/kmodul.c` expands it into one `kthread` per root: **started after the unit's
  load function answers 0, joined before its unload function runs.** A `struct completion` per
  root and not `kthread_stop` — a Gabbro root returns when it is done and never asks whether it
  should stop. A root that fails to start completes at once and refuses the load.
- *A root that never returns hangs `rmmod`.* Named in the file, not worked around: it is the
  same contract the hosted driver's join has, and a driver that gave up waiting would run the
  unit's exit beside a live thread.
- `include/stdatomic.h` joined `KMOD_QUELLEN` (5 → 6 files): it stopped being a refusal and
  became load-bearing, so a changed ordering row must rebuild the module.

### 11.5 Acceptance point 4b, measured

`messung/proben/kmodul/atomar-faeden.gab` + `atomar.c`, probe `atomar` of
`instrumente/pruefe-kernelmodul.sh`, QEMU with **`-smp 2`** (with one vCPU a lost update would
need a preemption to show at all):

```
$ instrumente/pruefe-kernelmodul.sh
   HARNESS: mapping ok (13 rows expanded and held against their primitive)
   HARNESS: atomic accesses ok
   HARNESS: insmod ok / rmmod ok
   gabbro-atomar: k=1 v=0        load
   gabbro-atomar: k=2 v=512      the counter: 256 rounds x 2 roots, EXACT
   gabbro-atomar: k=3 v=256      the flag seen set
   gabbro-atomar: k=4 v=0        the payload never stale
   gabbro-atomar: k=5 v=3        two bits ORed through atomic_fetch_or
   gabbro-atomar: k=9 v=0        unload
   GREEN (three probes)                                        22.9 s
```

Each number is a different row of the mapping: the counter is the bounded CAS loop
(`try_cmpxchg_relaxed`), the flag is `smp_store_release`/`smp_load_acquire`, the bits are one
`atomic_fetch_or_explicit` on an ORDERED atomic (so `acq_rel`, the unsuffixed `try_cmpxchg`).
`k=3` is checked as a MINIMUM and not as a value — it depends on scheduling, and a run in which
the flag was never seen reports a clean `k=4 v=0` about a branch it never entered.

**The probe's shape was decided by a refusal, and the refusal was right.** The obvious payload
(`beispiele/117`: ordinary storage published on the flag) is `N291`/`N301` the moment the two
bodies are a declared `concurrent` set — an unguarded write-read race, and
`Zielsatz/Spec.lean` lists unguarded publish/await payloads under NOT CLAIMED. So the payload
is a second ATOMIC, which the footprint rule admits (`GeteiltV`). The pairing stays written
either way: without it `V009` refuses a flag that gates a branch behind which a payload is
read.

```
$ instrumente/pruefe-kernelmodul.sh --gift all
   gifts: 10 of 10 caught                                      2 min 4 s
```

### 11.6 What a green run does NOT say — and the two static checks that answer it

**On x86 no run can falsify a missing barrier.** Acquire and release are free there, so a
mapping that dropped `smp_load_acquire` and `smp_store_release` would boot, run and answer
every expected number. A poison probe that cannot fail is not a poison probe (`W1`). So the
mapping is measured where it CAN fail:

1. **`instrumente/pruefe-atomar-zugriffe.py`** — every access to an atomic goes through one of
   the nine call forms, TOKEN level and not line level, over the whole corpus. It is stage 22c
   of `pruefe-emission.sh` now.

   ```
   $ instrumente/pruefe-atomar-zugriffe.py
      files checked   276 (39 of them declare an atomic)
      atomic objects  75
      accesses        137
      GREEN: no plain access to an atomic in the emitted C.        4.8 s
   $ instrumente/pruefe-atomar-zugriffe.py --selbsttest
      gifts: 6 of 6 as expected
   ```

   Session 4 had measured why this cannot be a grep: a line-based one reports **61** plain
   accesses over this corpus and every one is noise — a continuation line of a multi-line
   compare-exchange, or a `#define` whose name merely contains an atomic's. Two of the six
   self-test probes are exactly those two false positives, and they must stay SILENT.

2. **The mapping expansion** — each of the 13 rows preprocessed with the kernel's headers
   stubbed out (so `READ_ONCE` and `smp_load_acquire` stay as tokens) and held against the
   primitive it must select. It reads the header **in the build directory**, i.e. the copy the
   `.ko` was built from. Gift 8 is a deliberately too-weak mapping (acquire → `READ_ONCE`,
   release → `WRITE_ONCE`):

   ```
   GIFT 8: caught (1 finding(s))
       RED: the atomic mapping did not hold:
            HARNESS: mapping FAILED -- load acquire does not select smp_load_acquire
            HARNESS: mapping FAILED -- store release does not select smp_store_release
   ```

   **It was caught for the WRONG reason the first time**, and that is a finding about the
   harness: the mutation's pattern also matched the seq_cst row, the "did it apply?" guard
   answered no, the run returned before QEMU, and every expected line was then missing — which
   reads as a fat catch of 11 findings and measures nothing. *A gift that does not apply looks
   exactly like a pass (session 4, gift 5); this is the same fact from the other side, and it
   looks exactly like a catch.* The instrument reports `DOES NOT APPLY` as its own outcome now,
   counted as NOT caught, and the two rows are matched whole and by fixed string.

Gift 9 is the third: a plain access put back into the emitted C, caught by (1) — `_Atomic` is
`volatile` here, so it compiles without a word.

### 11.7 The named assumption (M11)

`grammatik/Grammatik/Zielsatz/Spec.lean`, a block of its own between `-- BEGIN Linux kernel
module` and `-- END`:

```
$ git diff --stat -- grammatik/Grammatik/Zielsatz/Spec.lean
 1 file changed, 47 insertions(+)
```

**Comment only**, 0 deletions, and it is a REFINEMENT of the existing assumption (2) of the
memory-model reading (*"the C compiler and the hardware implement C11 atomics and the orders as
specified"*) — which has no referent inside a kernel object, since the kernel is built
`-nostdinc` and has a model of its own. The review is `messung/SERVER-0E-SPEC-DIFF.md` Part II
(§§7–11), including what a reviewer should check and the one drift risk (the table stands in
two texts; what keeps them honest is that the expansion check reads the HEADER).

```
$ cd grammatik && ~/.elan/bin/lake build                 356 jobs, 2 min 20 s
$ cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean | grep gabbro_ziel
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 11.8 The walls

| | |
|---|---|
| `cargo test --release --no-fail-fast` | rc 0, **1424 passed 0 failed** (`~/claude-lane/logs/test-s5.log`); 1420 before, +4 (2 `wurzelliste`, 1 `die_art_entscheidet_welcher_treiber`, 1 CLI `die_wurzeln_…`) |
| `instrumente/pruefe-emission.sh` | rc 0, **ALL PASS — 51 durchgestochen, 322 von 322** (`~/claude-lane/logs/emission-s5.log`) |
| `grammatik` | `lake build` 356 jobs; `#print axioms gabbro_ziel` standard |
| `pruefe-kernelmodul.sh` | 3 probes GREEN; `--gift all` 10 of 10 |
| `pruefe-atomar-zugriffe.py` | GREEN over 276 files; `--selbsttest` 6 of 6 |
| `pruefe-todo.py` / `-saetze.py` / `-cformen.py` / `-ctext.py` / `-widerruf.py` | rc 0 |
| `abnahme.py --voll` | **NOT RUN** — no Isabelle on this machine |

Emission counter: `MARKE_EMIT_M` **158 → 159**, dated with its reason (the new probe);
`MARKE_EMIT` and `MARKE_EMIT_G` untouched — no example and no poison file was added, the
instrument's ten mutations are harness mutations. README guardian count **50 → 51**
(`pruefe-atomar-zugriffe.py`).

### 11.9 What this session did NOT do

- **K7** (`AUFTRAG-1.md`, added by Simon during this session): every kernel call of the module
  target — the lock primitives of `sperre.h`, the arena's `vzalloc`, the kthread glue and the
  K6 atomic rows — is to be BOUND BY THE PROGRAM, through a library unit it `use`s, with a
  refusal for an unbound primitive and an instrument over every undefined symbol of the built
  `.ko` (acceptance point 4c). **Untouched.** K6 was built so that the move is a substitution
  and not a rewrite: the rows are one table in one file, and (M11)'s substance does not change
  when they become the program's binding (`SERVER-0E-SPEC-DIFF.md` §10).
- **K3's model half** — the `entry`/`boot` vector, registers and steps still have no form in
  `Einheit`, and handler pinning/re-entry stay outside `KernPlan` (OFFEN O19).
- No `N` code, no gift number and no example number was taken: a lifted refusal keeps no
  `Satz`, and what replaced it is a header, a probe and two instruments.

---

## 12. Session 5, second half — K7's measurement: what the runtimes hard-wire

*`AUFTRAG-1.md` **K7** arrived during this session (Simon, 2026-09-28): every Linux kernel
function the module target uses is to be DECLARED BY THE USER'S PROGRAM, through a library
unit it `use`s, with a refusal for an unbound primitive — acceptance point **4c**. The
deliverable itself is NOT built. What is built is the half K7 names as its measurement, and
what that measurement says is below: it is the worklist, as a number that has to reach zero.*

### 12.1 The criterion, and why this one

Simon's rule is *"API calls are always user-made"*, and the module target keeps it for
everything the PROGRAM wrote: `messung/proben/kmodul/atomar.c` calls `pr_info` and `panic`
because `atomar-faeden.gab` declared those two foreign functions with their ABI, effects,
costs and the assumption their bodies keep. **It does not keep it for the runtime beside it.**

A useful criterion has to tell those two apart, and `nm -u` on the `.ko` alone cannot: it
lists both. So the stage asks it per object:

| | |
|---|---|
| `nm -u <unit>.ko` | every kernel symbol the whole module still needs |
| `nm -u gabbro_kmodul.o gabbro_arena.o` | what the RUNTIME objects reference (the emitted unit is `#include`d into the first, so the program's `extern fn`s are in there too — and they resolve against `gabbro_fremd*.o`, so they never reach the `.ko`'s list) |
| the intersection, minus the toolchain's own names | **what the runtime pulls out of the kernel** |

The toolchain's names (`__fentry__`, `__x86_return_thunk`, UBSan's handlers, the stack guard)
are excluded by name: they are not API calls and no program could declare them.

### 12.2 The measurement — this is the K7 worklist

```
$ instrumente/pruefe-kernelmodul.sh
   HARNESS: kernel symbols ok (4 hard-wired by the runtime, mark 4 -- K7 brings this to 0)
   HARNESS: kernel symbols ok (7 hard-wired by the runtime, mark 7 -- K7 brings this to 0)
   HARNESS: kernel symbols ok (9 hard-wired by the runtime, mark 9 -- K7 brings this to 0)
```

| probe | count | the names |
|---|---|---|
| `halde` | 4 | `param_ops_uint`, `_printk`, `vfree`, `vzalloc` |
| `takt` | 7 | + `pcpu_hot`, `_raw_spin_lock_irqsave`, `_raw_spin_unlock_irqrestore` |
| `atomar` | 9 | + `complete`, `__init_swait_queue_head`, `kthread_create_on_node`, `wait_for_completion`, `wake_up_process` |

**Twelve distinct names over the three probes**, and each is one line of K7: the arena's
reservation (`vzalloc`/`vfree`), its module parameter (`param_ops_uint`), the driver's own
reporting (`_printk`), the lock primitives of `sperre.h` (`_raw_spin_lock_irqsave` and its
release, plus `pcpu_hot` from `smp_processor_id`), and the kthread glue of K6's root starter
(`kthread_create_on_node`, `wake_up_process`, `complete`, `wait_for_completion`,
`__init_swait_queue_head`).

**Note what is NOT in the list, because it is the point of the criterion:** `panic`, which
this module also needs, is pulled by `gabbro_fremd0.o` — the program's own C, for its own
declared `aufgegeben`. That one is already K7-shaped.

**And note what the K6 atomic mapping contributes: nothing.** `READ_ONCE`,
`smp_load_acquire`, `try_cmpxchg` and `smp_mb` are macros and inline assembly; they leave no
undefined symbol. So the "bind the atomics" half of K7 cannot be measured this way at all —
it is a source-level question about where the ROWS come from, not a link-level one.

### 12.3 A ratchet, not a wall — and its poison probe

A stage that demanded 0 would be red on every probe until K7 lands, and a red that says
nothing new every time it is read is a red nobody reads. So the mark is the measured number
and the stage refuses a run that needs MORE — and a run that needs FEWER is a finding too
(the good case: the mark is stale and belongs pulled down), in the shape
`pruefe-emission.sh` uses for its emission counters.

That makes the stage's own poison probe load-bearing, and it is gift 11: one kernel call
added to the runtime copy in the build directory (`msleep` in `gabbro_kmodul.c`), re-made with
the `Kbuild` the build wrote.

```
GIFT 11: caught (1 finding(s))
    RED: the runtime's kernel calls moved:
         HARNESS: kernel symbols FAILED -- the runtime hard-wires 5 kernel function(s), the mark is 4
             hard-wired: msleep
$ instrumente/pruefe-kernelmodul.sh --gift all
   gifts: 11 of 11 caught                                             2 min 14 s
```

### 12.4 The other two runtimes, as K7 asks — a finding, not a task

> *"The hosted (`pthread`, `mmap`) and bare-metal runtimes are NOT changed in this phase:
> measure which OS calls they hard-wire and record the list as a finding in the report."*

**Hosted** (`laufzeit/arena_dyn.c`, `faden.c`, `start.c`, `start_pool.c`). Measured two ways,
because `start.c` and `start_pool.c` do not compile alone (they `#include` the emitted unit
through a macro), so `nm -u` reaches only two of the four:

```
$ cc -c -std=c11 -I laufzeit laufzeit/arena_dyn.c laufzeit/faden.c && nm -u *.o
   abort exit fprintf fwrite mmap mprotect stderr sysconf
```

and over all four by name: `pthread_create` (9), `pthread_join` (3),
`pthread_mutex_lock`/`_unlock` (4 each), the raw `clone` (8) and `futex` (4) through
`syscall` (11), `mmap`/`mprotect`, `sysconf`, `fprintf` (19), `printf`, `read`, `write`,
`exit` (13), `abort` (7). **Roughly a dozen libc and two raw Linux system calls, none of them
declared by any program.**

**Bare metal** (`laufzeit/metall/`): no OS at all, so nothing to bind — what it hard-wires is
the MACHINE, and that is a different class: `outb` (12), `hlt` (9), `sti` (7), `cli` (5),
`inb` (3), `wrmsr` (3), `lidt`, and the `lock`-prefixed instructions of the ticket lock (25).
Those are instructions, not API calls; the entry vectors and the syscall gate a program
declares already travel through `target … abi metal` (Opus agent L, OFFEN O31).

*So K7's reach is: the module runtime first (12 names, the list above), the hosted runtime
second (about fourteen), the bare-metal one not at all.*

**And that second line stopped being a finding while this section was being written.** Simon
added **K8** (`AUFTRAG-1.md`, acceptance point **4d**) with the rule in one sentence -- *"an
die Hardware ist OK, OS nicht, das muss selbst gemacht werden"*: no OS call hard-wired in ANY
runtime, hardware access on bare metal allowed and to be confirmed. So the fourteen names above
are K8's worklist and not a note, one library unit per OS (`bibliothek/linux/*.gab`) binds
them, and every hosted example in the corpus gains its binding line with the diagnostic diff
held at zero apart from the new refusal. Order: K6 (done), K7, then K8 -- and K8 is larger than
both and is to be split over sessions with master green between them. Phase 2's user-space
network stack needs the same library (TAP, sockets, timers), so it is worth building once.

### 12.5 What K7 still needs, and why K6 was built to fit it

Not built, and named so the next session starts from a shape and not from a blank page:

1. **The binding.** A library unit (`bibliothek/linux-kmod/*.gab`) that declares the
   primitives as ordinary Gabbro items with ABI, effects, costs and named assumptions, plus
   its own C — so the references move out of `gabbro_kmodul.o`/`gabbro_arena.o` and into an
   object the program supplied. The stage above turns green by that move alone, which is why
   its criterion is per object and not per `.ko`.
2. **The refusal.** A module unit that uses a lock, an arena or an atomic without binding the
   primitive it needs is refused at check time, with its sentence and a poison probe. That is
   a new `N` code and the first thing in this phase that would take one.
3. **K8 extends all of it to the hosted runtime**, with the same mechanism and the corpus
   attached to it (§12.4).
4. **The atomics.** They leave no symbol, so §12.2 cannot see them. The rows are one table in
   one file (`laufzeit/kmodul/include/stdatomic.h`), and K6 was built that way on purpose:
   when the names become the program's binding, the table moves and **(M11)'s substance does
   not change** — the assumption is then that the BOUND primitives are at least as strong
   (`messung/SERVER-0E-SPEC-DIFF.md` §10).

---

## 13. Session 6 (2026-09-28) — K7: the twelve kernel names become the program's (acceptance point 4c)

**The question.** Simon's binding constraint is *"API calls are always user-made"* (2026-09-27).
Session 5 measured the one place the module target did not keep it and wrote the number down
(§12, OFFEN O35): **twelve kernel functions the RUNTIME called and no program had declared.**
This session moved all twelve into the program and put a refusal in front of the move, so that
a module which binds none is stopped before a byte of C.

### 13.1 What the interface is, and why the direction is that way

`laufzeit/kmodul/bindung.h` — **twelve declarations and no definition.** The runtime calls
them; the program defines them. The kernel's own names appear in the program's C and nowhere
else in the tree.

| what the runtime needs | the bound name | what it replaced |
|---|---|---|
| say why a load refused | `gabbro_kern_melden(code, a, b)` | `pr_err` → `_printk` |
| an arena's storage | `gabbro_kern_reserve`, `_freigeben`, `_vorrat` | `vzalloc`, `vfree`, `module_param` → `param_ops_uint` |
| a lock | `gabbro_kern_sperre_init`, `_nimm`, `_gib` | `raw_spin_lock_init`, `raw_spin_lock`, `raw_spin_unlock` |
| a `masks irqs` lock | `gabbro_kern_sperre_nimm_maskiert`, `_gib_maskiert` | `raw_spin_lock_irqsave`, `raw_spin_unlock_irqrestore` |
| which core holds it | `gabbro_kern_kernnummer` | `smp_processor_id` → `pcpu_hot` |
| a root as a kernel thread | `gabbro_kern_faden_start`, `_warte` | `kthread_run`, `complete`, `wait_for_completion`, `init_completion` |

**The INTERFACE is the runtime's and the IMPLEMENTATION is the program's**, and not the other
way round: a runtime that read the program's choice of name would need the program's header,
which is a second register over one fact (`W7`). It is the arrangement the lock primitives
already had in the other direction — `emit.rs` declares `L_nimm`/`L_gib` per `lock` and defines
neither, every driver flavour supplies them. What K7 added is that the kernel's side of the
runtime is the same kind of hole.

**Three things make the Gabbro declaration load-bearing rather than decorative**, which was the
design question of the session:

1. `bau.rs::bindungsregel` refuses a `module` unit that does not declare it (13.3);
2. the C compiler holds it against `bindung.h` **inside the runtime's own translation unit** —
   `gabbro_kmodul.c` includes both the emitted unit (whose prototypes come from the Gabbro
   `extern fn`) and the interface, so a program whose declaration disagrees is a build error;
3. the program's own `.c` includes `bindung.h` too, so its definitions are held against the
   same line.

**An address travels as a `u64`.** Gabbro has no pointer type (the reason a system-call binding
passes registers, Opus agent L), so a reservation's base, a lock's storage and a root's body
cross as numbers and both sides cast. **The storage stays the runtime's and the operations are
the program's:** a `raw_spinlock_t` and a `struct completion` are kernel TYPES whose size
depends on the kernel's configuration, so the runtime hands over `GABBRO_KERN_*_WORTE` words of
`unsigned long` and the program's C lays its own struct into it, with a `_Static_assert` that it
fits *against the kernel it is being built for*. A blob too small is a loud build error, never a
silent overrun.

### 13.2 The measurement: 0, and it is a wall now

`instrumente/pruefe-kernelmodul.sh`, stage `symbole_pruefe`, unchanged in method (`nm -u` on the
`.ko` intersected with `nm -u` over the RUNTIME objects only, minus the toolchain's names):

| probe | session 5 | session 6 |
|---|---|---|
| `halde` | 4 | **0** |
| `takt` | 7 | **0** |
| `atomar` | 9 | **0** |

The `.ko` still imports all twelve — the program calls them — but the reference now lives in the
object the PROGRAM supplied. *That is exactly the distinction the per-object criterion was built
for, which is why the stage could be written before the fix existed and measures the fix rather
than a proxy for it.* The mark is `MARKE_KSYM=0` on every probe, so only one direction is left:
the stage is a WALL and no longer a ratchet.

```
./instrumente/pruefe-kernelmodul.sh          # 22.7 s, three probes
   HARNESS: kernel symbols ok (0 hard-wired by the runtime, mark 0)   [x3]
   gabbro-halde:  k=1 v=0, k=2 v=33, k=3 v=3, k=9 v=0
   gabbro-takt:   k=1 v=0, ticks=41 landed=0, k=9 v=0
   gabbro-atomar: k=1 v=0, k=2 v=512, k=3 v=256, k=4 v=0, k=5 v=3, k=9 v=0
   GREEN: halde / takt / atomar
```

Every number is the one session 5 measured, with the runtime rewired underneath: the counter is
exactly 512, the flag was seen 256 times, the payload was never stale, the two bits are 3, the
hardirq timer fired 41 times and landed on a holding core 0 times.

### 13.3 The refusal, and why a measurement alone would not have closed K7

**A `.ko` can only be measured if it was built.** A unit whose binding is missing has no `.ko`:
what it gets instead is `modpost`'s *"gabbro_kern_reserve undefined"* — a linker error, in a
`make` log, about the RUNTIME's name rather than about the program's omission. *A refusal that
arrives as a linker error over a name the user never wrote is a refusal the user cannot act on.*

`bau.rs::bindungsregel` therefore refuses, per thing the unit uses, before any C:

| the unit uses | it must bind |
|---|---|
| anything (it is a `module`) | `gabbro_kern_melden` |
| an `arena` | `gabbro_kern_reserve`, `_freigeben`, `_vorrat` |
| any `lock` | `gabbro_kern_sperre_init`, `gabbro_kern_kernnummer` |
| a PLAIN `lock` | `gabbro_kern_sperre_nimm`, `_gib` |
| a `masks irqs` `lock` | `gabbro_kern_sperre_nimm_maskiert`, `_gib_maskiert` |
| a `concurrent` root | `gabbro_kern_faden_start`, `_warte` |
| an `atomic` | a `stdatomic.h` among the unit's files |

and by SHAPE as well as by name — arity and whether it answers — because C has no mangling, so a
declaration of the right name and the wrong arity links and then reads a register nobody set.
*That is the same third question the init/exit rule already asks, for the same reason.*

**No `N` code, no gift number, no example**, and the reason is `eintrittsregel`'s and not a new
one: a `Satz` says what is true of a program the CHECKER passed, and this rule is about a
MANIFEST, which no pass ever sees. The target is what makes a `lock` need a kernel primitive,
and the target lives in the manifest, not in the source. *The plan of session 5 had reserved
`N569` for it; nothing was taken, and the next free numbers are unchanged.*

### 13.4 The memory model: the row `nm -u` cannot see

`READ_ONCE`, `smp_load_acquire`, `try_cmpxchg` and `smp_mb` are macros and inline assembly and
leave **no undefined symbol**, so the stage above is blind to them by construction (O35 said so
when it was written). Session 5's header argued from that fact that the table was not an API
call — *and that argument was half right:* the lock primitives it compared itself to were on
K7's worklist the very same day. So the table moved instead:

* `bibliothek/linux-kmod/stdatomic.h` is the program's table (**160 macro lines, byte-identical**
  to the old file; only the header comment changed);
* `laufzeit/kmodul/include/stdatomic.h` is a REFUSAL again — `_Atomic` pastes to an undeclared
  name. **Not an empty file**, and that is the whole safety of the move: an empty one would let
  a unit with an `atomic` compile with plain unordered accesses, load, and answer plausible
  numbers;
* the mechanism is a new file kind in the manifest — **a `.h` in a `module` unit's file list** is
  copied into the module's include directory AFTER the runtime's shims and therefore in place of
  one. A file line and not a new manifest word, because the file list is already where a unit
  says which files are its own (`W7`);
* `gabbro build` refuses a `module` unit that declares an `atomic` and names no `stdatomic.h`,
  with the file to add in its own sentence.

**The mapping stage and gift 8 did not have to change**: they read `inc/stdatomic.h` *in the
build directory*, which is where the program's file lands. **(M11) of `Zielsatz/Spec.lean` did
not change in substance** — 5 insertions, 2 deletions, comment only, the path and a parenthesis
(`messung/SERVER-0E-SPEC-DIFF.md` Part III has the review, and Part II §10 predicted exactly this
sentence).

### 13.5 The poison probes

| | what it does | caught by |
|---|---|---|
| gift **11** (repaired) | the RUNTIME gains one kernel call (`msleep` in `gabbro_kmodul.c`, re-made from the `Kbuild` the build wrote) | `symbole_pruefe`: *"the runtime hard-wires 1 kernel function(s), the mark is 0 — hard-wired: msleep"* |
| gift **12** (new) | the PROGRAM loses its binding: the two `bibliothek/linux-kmod` lines are dropped from the manifest, nothing else | `gabbro build`, with the binding rule's own sentence demanded by the harness |
| 3 CLI tests | the report channel, the arena trio, the MASKED pair against the plain one, a wrong arity, an `atomic` with no table, a `.h` outside a module | each with its POSITIVE twin in the same test |

**Gift 11 had to be repaired, and that is the trap of this instrument for the third time.** Its
anchor was `#include <linux/printk.h>` in `gabbro_kmodul.c` — an include the runtime LOST when
its reporting became the program's. The first full run after the rewiring read
`GIFT 11: DOES NOT APPLY`, which is exactly the shape sessions 4 and 5 each paid for once. The
anchor is now `#include <linux/errno.h>`: `-EINVAL` is the runtime's load verdict, so it is an
include the runtime cannot lose. *A mutation anchored on something the fix removes stops
measuring on the day the fix lands — and reads like a pass if nobody looks.*

```
./instrumente/pruefe-kernelmodul.sh --gift all     # 2 min 12 s
gifts: 12 of 12 caught
```

### 13.6 The walls

| | |
|---|---|
| `cargo test --release --no-fail-fast` | rc 0, **1427 passed, 0 failed** (+3; `~/claude-lane/logs/test-s6.log`) |
| `./instrumente/pruefe-emission.sh` | rc 0, **ALL PASS — 51 durchgestochen, 323 von 323** (+1 file: the binding; `~/claude-lane/logs/emission-s6.log`) |
| `cd grammatik && lake build` | rc 0, 356 jobs (`~/claude-lane/logs/lake-s6.log`) |
| `lake env lean Nachpruefung.lean` | 12 `#print axioms` lines, every one `[propext, Classical.choice, Quot.sound]`, `gabbro_ziel` among them |
| `instrumente/pruefe-kernelmodul.sh` | GREEN on all three probes, 12 of 12 gifts |
| `pruefe-todo.py` | 3 findings — **exactly the base's 3**, same three (measured in a `git stash` of this diff) |
| `abnahme.py --voll` | cannot run here: no Isabelle on this machine (`REGELN.md`) |

**One counter moved, and it is a ROOT and not a number:** `bibliothek/` is the seventh booked
emission root (`MARKE_EMIT_BIB=1`). The catch-all named it the way it named `laufzeit/` on
2026-09-15 — *"NEUE WURZEL EMITTIERT: 1 … bibliothek/linux-kmod/linux-kmod.gab, gebucht sind 0"*,
return code 1, stage 22c never run — and the healing is a RATCHET and not a raised number: a
binding file that LEAVES the emission is a finding too. `MARKE_EMIT`, `MARKE_EMIT_G` and
`MARKE_EMIT_M` did not move: no emitted byte of any existing unit changed.

### 13.7 Two findings that are not K7's

1. **`instrumente/pruefe-sondendeckung.py` aborts in its own speech test, and has for at least
   three sessions.** Four teeth read NO at the base of this session. One of them was the stale
   `MARK_AUSSEN`: booked at 13 since 2026-09-04, measured at **21** before this session's work
   and **23** after it (the two new ones are `sonde_kern_bindung` and `sonde_kern_maskiert`, the
   binding's named assumptions). It is booked at 23 now, with the names and the date. **The
   other three teeth are older than K7 and are NOT repaired here** — they belong to a lane of
   their own, and the guardian measures nothing until they are. *A mark nobody reads is a mark
   that drifts; a guardian that aborts is why nobody read it* (the session-4 trap, from the
   other side).
2. **`instrumente/binaer.sh` calls a binary stale when a TEST file is newer.** Its check is
   `find crates -name '*.rs' -newer <binary>`, and a test file is not an input to the binary —
   so after any `cargo test` edit every instrument reports `NOT RUN` until a rebuild that
   `cargo build --release` alone does not perform (it does not recompile the binary for a test
   change). It cost two emission runs here. The healing used was the correct one — a real build
   (`touch crates/gabbro-cli/src/main.rs && cargo build --release`), never a `touch` on the
   binary — but the guard is wider than its own reason, and narrowing it to `crates/*/src/`
   is a one-line change for whoever next has the budget.

### 13.8 What K7 does NOT close

* **The hosted runtime** is untouched: about fourteen libc names plus the raw `clone` and `futex`
  through `syscall` (§12.4). That is K8 and acceptance point 4d.
* **Bare metal** calls no OS and never did; what it hard-wires is the MACHINE, which K8 allows.
* **The binding library defines all twelve bodies whether the program uses them or not**, so a
  module with no lock still links the lock primitives in. Dead code in the `.ko`, no kernel call
  at run time, and a program that minds can write a smaller binding — it is user code.
* **`module_init`/`module_exit`/`MODULE_LICENSE` stay in the runtime.** They are declarative
  macros that place a pointer and two strings in sections; they are what makes the artefact a
  module rather than something it does, and they leave no undefined symbol (measured: the stage
  reads 0 with them in place).
