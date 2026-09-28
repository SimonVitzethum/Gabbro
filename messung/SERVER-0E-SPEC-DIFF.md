# The `Spec.lean` diff of the dynamic arena — what moves, and why nothing is weakened

*Server lane (`ubuntu@simon.jocraft.cc`), 2026-09-28, session 3. TODO §0e item 1, deliverable
H3. The review is written by the lane that made the diff; every claim below names the command
or the file that answers it.*

**The diff is COMMENT ONLY.** No definition of `grammatik/Grammatik/Zielsatz/Spec.lean`
changes, no premise group gains or loses a member, `Laufzeit` has the three fields it had
(`lader`, `start`, `einmal`), and no proof in the tree is touched. Measured:

```
$ git diff --stat master -- grammatik/Grammatik/Zielsatz/Spec.lean
$ cd grammatik && ~/.elan/bin/lake build          # 355 jobs, no error
$ cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean | grep gabbro_ziel
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 1. What was asked, and what the previous session expected

`AUFTRAG-1.md` H3 asks for "the two `Spec.lean` (d) fault-latency assumption texts as a
reviewed diff". `PLAN-DYNAMISCH.md` §9 fixes their wording and their names,
`Laufzeit.reserve` and `Laufzeit.commit`, and says they go "in the ONE list (`Spec.lean`
header style)".

Session 2's hand-over (`~/claude-lane/STAND.md`, point 0 of *Next step*) read those names as
**new FIELDS of the `structure Laufzeit`**, and measured the consequence: five construction
sites (`Zielsatz/Ruhe.lean:538`, `:597`, `Zielsatz/FaedenZeuge.lean:381`, `:495`,
`Schlusssatz124.lean:1291`) plus every generated certificate would have to supply them, and
a half-added premise leaves `grammatik/` red.

**That reading is wrong, and this session did not follow it.** The reason is below; it is the
only judgement call in this diff, so it is the first thing a reviewer should attack.

## 2. Why the texts are NOT new fields

A field of `Laufzeit` is a **premise of `GabbroZiel`**. Premises only ever move one way: every
premise added makes the theorem say *less* — it excludes runs from the claim. So the question
"does a new field weaken the statement?" has one answer before one looks at the content: yes,
unless the field is already implied by the premises that stand.

Take the two texts one at a time.

**`Laufzeit.reserve`** — *"the loader reserves the virtual range for every dynamic arena's `M`
before any start runs; a failed reservation refuses the load, it never starts a program with a
smaller range."*

In this statement an arena **is** a table (`ArenaZucker.lean`; for the dynamic form,
`ArenaDyn.lean` section `Form`: the table spans the ceiling `M`). The loader premise that
stands, `Laufzeit.lader : sp = speicherR E.sp0`, says the loader establishes the program's
declared initial memory — and that memory *contains the table of `M` slots*. A load that
cannot provide the range establishes no `E.sp0`, so `lader` is **false** of it and the theorem
already says nothing about that run. The reservation is not a missing premise; it is the
reading of a premise that stands.

Adding it as a field would therefore (i) claim nothing new, (ii) cost five construction sites
and every certificate, and (iii) weaken the theorem by exactly the runs where the *new* field
fails while `lader` holds — an empty set if the field is stated correctly, and a silent hole
if it is not. That is ceremony bought at the price of a guarantee, which
`PLAN-EINFACHHEIT.md` and AGENTS.md §3 both forbid.

**`Laufzeit.commit`** — *"every `grow` the checker admits either commits its slots before the
next statement runs or takes the `else` branch; a commit that reports success names
readable/writable storage; commit latency is bounded by the runtime's declared per-slot
cost."*

Here the first clause is now **proved, not assumed**. `ArenaDyn.dynGrow_commit` (added this
session) says the form has exactly two outcomes: the narrow of `committed + n` into `0 .. M`
fits and one store happens — with the frame, so the used counter and every slot stay put — or
it does not fit and the `else` runs, and `Block.narrow`'s `else` does not fall through. Past
the ceiling there is no branch at all (`dynGrowListe_scheitert`, from fix lane F2). Making the
clause a premise would *assume* what the model proves, and a reader who later weakened
`dynGrow_commit` would not notice, because the premise would carry the claim.

What is left of the text after the proof takes its half is a statement about the **C runtime**:
a commit that fails below the ceiling must reach the program's `else` or fail-stop, and must
never report success over storage that faults on first touch. That is the same class as every
other "the C realises what G means" fact — covered by the NOT CLAIMED line *"the C and the
hardware"* and settled by translation validation, not by a premise. The latency clause is the
same: `ArenaDyn.growKosten` reads the per-slot cost as **data** from premise (c)'s latency
entry and proves nothing about it (`growKosten_pos` is the only claim, and it is arithmetic).

## 3. What the diff actually is

Two new bullets in THE ONE LIST of the header (the list whose entries read
`* (d) \`Laufzeit.lader\` -- …`), inserted between `lader` and `start`/`einmal`:

* **`(d) Laufzeit.reserve`** — PLAN-DYNAMISCH §9's wording verbatim, then: no new premise and
  no new field, with the argument of §2 above; then what the reservation *is* on each of the
  three runtimes that exist today — hosted `mmap(PROT_NONE)` + lazy `mprotect`
  (`laufzeit/arena_dyn.c`), the carved region of (M10) on metal, one `vzalloc` region per
  arena with a budget over it in a Linux kernel module (`laufzeit/kmodul/arena.c`); and the
  explicit NOT CLAIMED: *that the reservation succeeds* — refuse-on-load is a refusal, not a
  leg.
* **`(d) Laufzeit.commit`** — PLAN-DYNAMISCH §9's wording verbatim, then which half is proved
  (`dynGrow_commit`, `dynGrowListe_scheitert`) and which half is assumed about the C, and the
  sentence that the latency number is read and never justified.

And one clarification in NOT CLAIMED, on the line that puts dynamic unbounded data structures
out of scope (OFFEN O29): an `arena … max M` is **not** that case — its ceiling bounds it, its
form is sugar over the existing `Block` — **but** the exporter does not produce that shape, so
no dynamic-arena program is CERTIFIED (see §5).

## 4. Why nothing is weakened — the checklist

| Question | Answer, measured |
|---|---|
| Does any premise move? | No. `Laufzeit` has `lader`, `start`, `einmal`; `GabbroZiel`'s four premise groups are byte-identical. |
| Does any leg of `Ziel`/`ZielF`/`ZielX` move? | No. No definition in the file changed. |
| Does any proof change? | No. `lake build` is 355 jobs with no error; `#print axioms gabbro_ziel` is the three standard axioms. |
| Is a refusal turned into a warning? | No refusal is touched. `N426` (every `grow` against the UPPER bound) and `N466` (`R-commit`) stand unchanged; `LG005` still refuses `grow` in the exporter. |
| Is an `ensures` derived? | No. |
| Does the NOT CLAIMED list shrink? | No. It gains a *clarification* and loses no line. The clarification makes the list stricter in one direction: it now says in writing that no dynamic-arena program is certified. |
| Could the new text be read as a claim? | Both bullets say what is NOT claimed in their own body, and both are marked as comment-only. |

## 5. The gap this diff makes visible (and does not close)

Writing the clarification forced a measurement that had not been made in this lane:

```
$ grep -n "StmtArt::Grow" crates/gabbro-check/src/lean_g.rs
4184:        // **Lane 257:** `grow A by n else { … };` has no G form in this
4189:        StmtArt::Grow(g) => Err(refuse("LG005", …))
```

The exporter **refuses `grow` (`LG005`)** and, for an arena declaration, builds the static
`ArenaForm` over `hi` — not over the ceiling `M`. So:

* the Lean forms of `ArenaDyn.lean` section `Form` are covered by `gabbro_ziel`, because they
  are ordinary `Block` terms and the goal theorem quantifies over all of them;
* **no dynamic-arena program is CERTIFIED**, because the exporter cannot write one down;
* for such a program a green `lake build` says nothing — exactly what the header's
  *WHAT A GREEN BUILD COVERS* paragraph says about every UNCERTIFIED program.

This is the same status `ArenaZucker.lean` had between its merge and the closing of OFFEN O14.
It is now written into three places so it cannot be read past: the NOT CLAIMED clarification
in `Spec.lean`, the CUTS of `ArenaDyn.lean`, and this section. **It is not closed here**, and
closing it is exporter work (`lean_g.rs`: a `DynForm` model beside the `ArenaForm` one), not
model work.

## 6. What a reviewer should check

1. `git diff master -- grammatik/Grammatik/Zielsatz/Spec.lean` touches only comment lines.
2. The two bullets' first sentences are PLAN-DYNAMISCH §9's wording, unchanged.
3. §2's argument: is `Laufzeit.lader` really false of a load that cannot reserve `M`? It rests
   on the arena being a table of `M` slots in `E.sp0` — check `DynForm` in
   `grammatik/Grammatik/ArenaDyn.lean` (`hk : D.gtyp komm = Ty.int 0 (D.count tab)`, the table
   spans the ceiling) and `ArenaForm` in `ArenaZucker.lean`.
4. `dynGrow_commit` really has the frame conjuncts (used counter, slots) — if it does not, the
   `Laufzeit.commit` bullet claims a proof that does not exist.
5. The witnesses are not degenerate: `DynZeuge.gespannt` is an arena with **room to the
   ceiling whose allocation is refused** (`zeuge_alloc_ueber`, `zeuge_raum_unter_der_decke`),
   which is the one state the static form cannot name.

---

# Part II — the `Spec.lean` diff of the kernel-module atomic lowering (M11)

*Server lane, 2026-09-28, session 5. TODO §0e K6, `AUFTRAG-1.md` K6 bullet 3. Same rule as
Part I: the review is written by the lane that made the diff, and every claim names the
command or the file that answers it.*

**The diff is COMMENT ONLY, again.** 47 insertions, 0 deletions, all of them inside the
file's opening doc comment, in a block of their own between `-- BEGIN Linux kernel module` and
`-- END Linux kernel module`. Measured:

```
$ git diff --stat -- grammatik/Grammatik/Zielsatz/Spec.lean
 grammatik/Grammatik/Zielsatz/Spec.lean | 47 ++++++++++++++++++++++++++++++++++
 1 file changed, 47 insertions(+)
$ cd grammatik && ~/.elan/bin/lake build
$ cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean | grep gabbro_ziel
```

## 7. What was asked

> *"The memory-model argument is a NAMED ASSUMPTION, not a Lean proof of LKMM refinement:
> 'each kernel primitive implements at least the C11/RC11 order it replaces', added to the
> `Spec.lean` header as a reviewed diff beside the existing C-side assumptions."* —
> `AUFTRAG-1.md` K6

And: *keep it architecture-neutral; the argument must name what it relies on per order, so
that a weak-memory architecture can be checked against it later.*

So the shape was given. The question this review has to answer is the one the shape does not
decide: **where does such an assumption BELONG, and does putting it there weaken anything?**

## 8. It is a refinement of (2), not a new assumption

The header already carries five named assumptions of the memory-model reading (the block that
begins *"What replaces it, FIVE named assumptions of the reading"*). The second of them reads:

> (2) the C compiler and the hardware implement C11 atomics and the orders as specified …

On a hosted or bare-metal build that sentence has a referent: the toolchain's `<stdatomic.h>`
and the CPU. **Inside a Linux kernel object it has none.** The kernel is built `-nostdinc`, so
`<stdatomic.h>` is whatever the include path supplies (here `laufzeit/kmodul/include/`), and
the kernel does not use C11 atomics at all — it has a memory model of its own.

That leaves exactly two honest options:

| | |
|---|---|
| refuse the target for units with atomics | what session 3 did, and recorded as OFFEN O34 |
| name what (2) means there | what this diff does |

There is no third option in which the goal theorem says the same thing on that target for
free. **(M11) is therefore not an addition to what is claimed — it is the part of (2) that
had no content on this runtime and would otherwise have been silently assumed.** That is the
same move (M1)–(M10) make for the bare-metal runtime: the legs do not change, the sentence
that says what the premise MEANS on that machine does.

## 9. Why nothing is weakened — the checklist

1. **No definition, no premise, no leg.** `git diff` shows 47 `+` lines and no `-` line; every
   one of them is inside the doc comment. `Laufzeit`, `Hardware`, `SchwachX`, `ZielX` are
   untouched, and so is every proof.
2. **The direction of every row is the strong one.** Each mapping row provides at least what
   it replaces; where the kernel has no exactly-matching suffix (`acq_rel`), the row takes the
   FULLY ORDERED form. A reviewer can check this row by row against
   `laufzeit/kmodul/include/stdatomic.h`, whose table is the same table.
3. **The one place the obvious mapping would be weaker is named, not glossed.** C11 gives a
   compare-exchange a failure ordering; LKMM gives a failed `cmpxchg` none, in every variant.
   The row therefore carries `smp_mb()` on the failure path. *Had this been missed, a
   `(release, acquire)` exchange would have been sound on success and unordered on failure —
   which no wall in this tree would have shown, because x86 hides it.*
4. **No refusal became a warning.** Two refusals stay and one was NARROWED with its reason:
   a floating-point `atomic` in a module is still refused before a byte of C
   (`bau.rs::modulregel`), an unlisted (form, ordering) pair is an undefined name at the
   kernel build, and a read-modify-write of an unsupported width is a `_Static_assert`.
5. **Nothing was claimed that a run could not have falsified — because the runs cannot.**
   This is the uncomfortable half and it is written into the block: on x86 acquire and release
   are free, so a green QEMU run says nothing about the barriers. The two things that DO
   constrain the mapping are static, and both are named in the block: the token-level
   corpus check that every access goes through a call form, and the preprocessor expansion of
   each row against the primitive it must select. The instrument's gift 8 is exactly the
   too-weak mapping, and it is caught by the second of those and by nothing else.

## 10. What this diff does NOT do, and what should follow it

- **It proves nothing about LKMM.** Simon asked for an assumption and this is one. A proof
  that LKMM refines the orders `SchwachX` over-approximates is a statement about Linux; if it
  is ever wanted, it is its own project and its own model.
- **It does not make the kernel primitives user-declared.** They are macros of the target's
  memory model, in the runtime header, and the file argues why (the emitted C is pinned byte
  for byte in the translation-validation chain, so a per-target emitter would fork the
  artefact the chain reads). **Simon's K7 (added 2026-09-28) asks for the names to come from
  the program**, through a library unit the program `use`s. When that lands, (M11)'s text is
  unchanged in substance and one sentence of it moves: the rows are then the program's
  binding, and the assumption is that the BOUND primitives are at least as strong. The
  assumption does not get weaker or stronger by moving — which is the reason it is worth
  writing it down now, in the form the checker and the instruments already measure.

## 11. What a reviewer should check

1. `git diff -- grammatik/Grammatik/Zielsatz/Spec.lean` touches only comment lines, and the
   new block sits between its BEGIN/END markers.
2. The rows in the block and the rows in `laufzeit/kmodul/include/stdatomic.h` are the same
   rows. (They are two texts over one fact, and that is a drift risk — the thing that keeps
   them honest is the expansion check, which reads the HEADER and not the block.)
3. `instrumente/pruefe-kernelmodul.sh --gift 8` is caught by the mapping stage and not by a
   boot failure. *It was caught by a boot failure the first time, because the mutation did not
   apply; the instrument now reports `DOES NOT APPLY` instead of counting it.*
4. `instrumente/pruefe-atomar-zugriffe.py` is green over the corpus and its `--selbsttest`
   catches four mutations while staying silent on the two false positives a grep produced.
5. `#print axioms gabbro_ziel` is still `[propext, Classical.choice, Quot.sound]`.

---

# Part III — the table moved into the program, and (M11) did not change (K7, session 6)

*Written 2026-09-28 by the server lane, session 6, beside the work it reviews.*

## 12. What moved

Part II §10 predicted this in the sentence *"when that lands, (M11)'s text is unchanged in
substance and one sentence of it moves"*. It landed the same day. What happened, exactly:

| | |
|---|---|
| the table | `laufzeit/kmodul/include/stdatomic.h` → `bibliothek/linux-kmod/stdatomic.h`. **`git mv`, then a rewritten file header and one paragraph; not one macro line changed.** *`git diff -M` does NOT report it as a rename, and that is worth saying rather than claiming otherwise: a new file took the old path, so git sees two files.* The check that does hold it is a direct one — everything from `#ifndef GABBRO_KMOD_STDATOMIC_H` down, **160 lines, byte-identical** (measured: `git show HEAD:laufzeit/kmodul/include/stdatomic.h \| sed -n '/^#ifndef GABBRO_KMOD_STDATOMIC_H/,$p'` against the same range of the new file, `diff` silent) |
| what stands in the runtime now | a REFUSAL: `#define _Atomic GABBRO_KMOD_ATOMIC_NICHT_GEBUNDEN_…`. A unit with no `atomic` needs nothing behind the name and compiles; a unit with one, and no bound table, does not |
| how the program's file reaches the build | a `.h` in a `module` unit's manifest file list is copied into the module's include directory **after** the runtime's shims, and therefore in place of one (`bau.rs::kmod_modul_binden`) |
| the door before that | `bau.rs::bindungsregel` refuses a `module` unit that declares an `atomic` and names no `stdatomic.h`, before a byte of C — with the file to add in its own sentence |
| `Spec.lean` | **one comment line and a parenthesis**: the path in (M11), plus a note that the assumption is about the rows and not about the file. `git diff --stat -- grammatik/` is **5 insertions, 2 deletions, one file**, all inside the doc comment |

## 13. Why this is not a weakening, and what would have made it one

1. **The rows are the same rows.** The claim (M11) makes is per (call form, ordering): the
   kernel primitive provides at least the order the C11 operation it replaces provides. That
   claim is about a table, and the table is byte-identical below its header comment. *A
   reviewer can check this with `git show HEAD -- bibliothek/linux-kmod/stdatomic.h` against
   the old path: the rename is detected and the macro block has no diff.*
2. **The measurement that constrains the rows did not move either.** The expansion check of
   `instrumente/pruefe-kernelmodul.sh` reads `inc/stdatomic.h` **in the build directory** —
   the copy the `.ko` was built from — and that path is unchanged, because the program's file
   lands there under that name. So the 13 rows are still expanded and held against the
   primitive each must select, and **gift 8 still bites** (measured: caught, and by the
   mapping stage alone).
3. **What would have made it a weakening**, and was deliberately not done: dropping the
   runtime's `<stdatomic.h>` to an EMPTY file. Then a unit with an `atomic` and no bound table
   would have compiled, every access would have been a plain unordered one, and the module
   would have loaded and answered plausible numbers. The refusal is what makes the move safe,
   and it is the reason the runtime's file is a `#define` to an undeclared name rather than a
   deletion.
4. **The assumption is no longer about a file this tree ships.** That is the honest reading of
   what the move BUYS: (M11) now speaks about the table the PROGRAM bound. A program that
   binds a different one — a different kernel, a different architecture's needs — carries its
   own (M11), and the sentence in `Spec.lean` is the shape of the obligation rather than a
   claim about one file. *Nothing in the goal theorem depended on which file it was; §10 of
   Part II said so before the move, which is why this paragraph is a confirmation and not a
   repair.*

## 14. What a reviewer should check (Part III)

1. `git diff --stat -- grammatik/Grammatik/Zielsatz/Spec.lean` is 5 insertions and 2
   deletions, comment only, inside the (M11) block.
2. The macro block of `bibliothek/linux-kmod/stdatomic.h` and of the old
   `laufzeit/kmodul/include/stdatomic.h` are the same 160 lines (`diff` over the range from
   `#ifndef GABBRO_KMOD_STDATOMIC_H` down). **Not `git diff -M`** -- a new file took the old
   path, so git reports two files and no rename.
3. `instrumente/pruefe-kernelmodul.sh --gift 8` is still caught by the mapping stage.
4. The runtime's `laufzeit/kmodul/include/stdatomic.h` refuses `_Atomic` and defines nothing
   else, and `crates/gabbro-cli/tests/bausystem.rs::ein_modul_mit_atomic_ohne_speichermodell_faellt`
   holds the door in front of it, with its positive twin in the test beside it.
5. `#print axioms gabbro_ziel` is still `[propext, Classical.choice, Quot.sound]` (measured,
   session 6, `~/claude-lane/logs/lake-s6.log`: 356 jobs, and 12 `#print axioms` lines all
   standard).
