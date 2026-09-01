# Gabbro — what is finished

> **This file carries exclusively what is done.** What is open stands in [TODO.md](TODO.md),
> what is refuted in [dokumente/HISTORIE.md](dokumente/HISTORIE.md), what is measured in
> [dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md).
>
> **Every entry carries its evidence** — a file, a refusal code or a re-runnable command line.
> *A done report without evidence is the same number without a source list that W7 stands
> against* ([dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md)).

---

## The pattern, with its third data point *(2026-08-20)*

> **The corpus is written from the language outward; the faults sit at the combinations.**

That is the same finding as at the hand-written mutations — *dense near the refusals, thin at
the arithmetic*. **What someone has in mind while writing covers the AXES, not the surface.**
Two tools, one cause; and the prediction was that it would appear a third time.

**It did, within the hour.** `pruefe-reichweite.py` — the counterpart to `gabbro
blindstellen`, where the zero means *no pass READS this body* rather than *nobody wrote this
form* — named exactly two item kinds that carry a body and that **exactly one pass** knew:

| | what it let through |
|---|---|
| `format`'s `where` clauses | `where a <= nirgends_erklaert` — a name that stands nowhere — **0 errors**. And the clause is what `PFLICHTEN.md` F10 rests on: *after a `format` access no length check is needed, because the reader NEVER delivers a structure that violates it.* |
| a `boot`'s steps | a boot sequence in the **wrong phase order** (`caps` before `mmu`) — **0 errors**. *The construct that exists FOR the boot order did not check its own.* |

Closed as `N032`, `N033` and `O007`. **And the first version of `N033` was wrong, not the
corpus:** it reported two errors in `beispiele/07`, where `step write_cr3(…)` names an `axiom`
with a falsifier — a privileged instruction is exactly what a boot sequence does.

> **The line for the history:** *the most expensive faults of this project do not sit in what
> was thought wrongly, but in what nobody read* — and the last three guardians are answers to
> that sentence.

### A second pattern, and it now has four instances

> **A check built for the OBVIOUS reason does not cover what the LOAD-BEARING reason demands.**

| | the obvious reason | what the load-bearing reason demanded |
|---|---|---|
| `diverges` | a divergent function does not return | …and therefore `on_exceeded` must name one, or the bound is a number without a consequence |
| the ghost erasure | a ghost has no lowering | …and therefore the erasure must reach the RETURN too, which no example ever exercised |
| a ghost in storage | a ghost has no lowering — *technical* | a **linear** value has storage but no PATH: *consumed exactly once* is a statement about a control-flow path, and a field in one of N slots has none. **The sharper reason caught the case the weaker rule missed.** |
| the call graph | a transition is a callee with declared effects | …and a device CONSTRUCTOR is not a call at all — the hint stood in `beispiele/09` for months |

**The question this leaves open, and it is worth carrying:** *which other rules stand on the
technical reason rather than the load-bearing one?* The four above were found one at a time,
by writing programs; a systematic answer would read every rule's stated reason against what it
actually has to hold.

---

## `gabbro blindstellen` — the instrument that finds the class *(2026-08-20)*

On 2026-08-20 the first driver that did not come from the design found five faults in an
afternoon. Three were **unbuilt halves** — the model was right and a pass was not finished.
None had shown up for months, and the reason was the same in all three: **the corpus is
written from the language outward, one file per construct, and the faults sit at the
combinations.**

```
gabbro blindstellen beispiele/*.gab -- beispiele/gift/*.gab
                                     ->  130 blind, 22 GUARDED over 38 examples
```

**A blind spot has three causes and only one of them is work**, and the tool must say which:

| state | what it means | work? |
|---|---|---|
| covered | the clean corpus realises it | no |
| poison-only | empty in the clean corpus, occupied in the poison one | a *hint*, not a proof — see the correction below |
| impossible | the grammar does not allow the pair at all | no — it is not a cell |
| BLIND | legal, meaningful, and nobody wrote it | yes |

> **And the instrument reported its own miscalibration as work — twice.** The first version
> ran `atomic` under `read`/`written`; an atomic is neither read nor written, it is awaited,
> published or exchanged — that is the whole point of the word. *I fixed the instance and left
> the class:* `slot field in position publishes` and eight more stood there afterwards, and
> they are just as much not cells. **The columns belong to their rows, not to the table.**
> 151 → 130 without a single line of corpus.

### The four numbers are reported apart, and the tool says them itself

```
== 125 blind · 125 covered · 20 poison-only · 15 no cell (of 285 pairs) ==
```

`151 → 112` reads like thirty-nine progress. It was twenty-one **written** and eighteen
**removed** — and a removal improves the figure twice over: it leaves the numerator *and* the
denominator. As long as every removal carries its reason beside it, that is clean; as long as
the NUMBER is quoted in one part, it stops being clean in two weeks, when it reads
"39 closed" and nobody can recompute it. **So nobody recomputes it — the tool says it.**

*And the same output shows the honest direction of travel:* the blind count went **104 → 154**
when a pointer position was separated from a by-value one. Nothing got worse; the map got
finer, and the denominator grew with it.

### And the state was over-claimed — the acceptance of the first agent files found it

The first version called it **GUARDED** and wrote beside it: *„the strongest state a cell can
have."* **That was too much claimed.** Taking in two new corpus files moved five cells from
`guarded` to `covered`, among them *assignment in a `traverse`* — and the four poison files
that occupy that cell expect `P001`, `M109`, `E011` and `M101`. **None of them forbids an
assignment in a traverse.** It stands there as SCAFFOLDING, not as the subject.

> *A poison file tests ONE rule; everything else in it is scaffolding.* From „the shape occurs
> only in the poison corpus" it does not follow that a rule forbids it — only that no clean
> program has needed it yet.

**What a real `guarded` would require is exactly the booked item**: a probe *per combination*
instead of per construct. Until that exists, the state is called what it is — `poison-only`.

*The check that found this is the one worth keeping:* **zero errors on a new corpus file is
the weaker of the two possible reports.** The question is not whether it compiles but which
cells it closes — and whether the cells it claims were really empty.

### The exclusion table is falsifiable, and it was refuted within the minute

`no cell` is a list of **judgements** — *this pair is not a question* — and a judgement that
takes a cell out of the denominator must be refutable. **The corpus is the falsifier:** if the
combination stands somewhere, the judgement was wrong.

The check fired on its first run, on my own entry:

```
!! CONTRADICTION  table x `static` is declared no cell -- and the corpus HAS it.
```

`beispiele/38` writes `static tz : ptr<normal, rw> Platz`. **The reason was right and the
instrument was wrong:** a table as a VALUE does not exist, a table behind a POINTER is the
normal case — and the two stood in the same cell. *An exclusion no probe can ever contradict
is not an exclusion but a convenience.*

**The number must not become a target.** Zeroing it by writing 128 small files would grow the
corpus *from the instrument outward* — the same mistake as growing it from the language
outward, one level up, and the next real driver would still find five faults. *The evidence
for the right mechanism is already there: writing three real programs closed four cells
without anyone aiming at one.*

It counts **form × position** and names the empty cells. *What has 0 sites is not checked but
UNREACHABLE:* no probe, no guardian and no mutation can trigger it — the same shape as
`mutiere-pruefer.py` one level up.

> **The speech test is the point.** Run against the corpus as it stood one day earlier, it
> names exactly the two findings a real driver was needed for:
>
> ```
> BLIND  ghost in Stellung `rueckgabe (rumpf)`   ->  the ghost return that was never erased
> BLIND  formatfeld in Stellung `geschrieben`    ->  the `format` writer that did not exist
> ```

**And what it does NOT say stands in its own output:** an occupied cell says only that a pass
*can* see the form, not that it handles it. Two of the five it does not catch at all — the
device counterpart («V9») was a missing CATEGORY, not a missing form, and a body a pass does
not READ is present in the corpus all the same.

---

## Emission is COMPLETE — 38 of 38, and all 38 compile *(2026-08-20)*

> **The record below is of 2026-08-20 and stays as one.** Re-measured 2026-08-30:
> `EMISSION: ALL PASS -- 24 durchgestochen, 52 von 52 uebersetzen`. *A dated record is
> not made wrong by growth — but a heading that says COMPLETE about a moving
> denominator needs the date beside it, and this one has it.*

```
./instrumente/pruefe-emission.sh     ->  19 durchgestochen, 38 von 38 uebersetzen, 0 benannte Ausnahmen
```

**The nineteenth unit is the tree walk, and it is the one that mattered here.** *Compilable is
not correct* — this guardian's own opening says so — and the stackless post-order descent is
exactly the shape where the difference could hide. Four numbers, each separating a different
failure:

| | separates |
|---|---|
| 7 | ALL descendants seen. A descent running along `parent` instead of `child` sees none. |
| 0 | none seen TWICE. Without the "arrived from below" flag the walk re-enters the same child and never terminates. |
| 0 | the ROOT is not among them — a node is not its own descendant. |
| 1 | *post-order*: every child before its parent. That is what `by consuming` promises, and what `blatt_loeschen` demands as `requires ist_blatt`. |

> **And the probe fell at the pass it presupposes.** The first version wrote `static mut
> zaehler : u32` and `zaehler + 1` — a full word plus one, so `M104`. *The emitter's own test
> was caught by M1 before it could test anything.*

Twelve examples produced no C. **Every one of the twelve refusals was named and reasoned**
(`C001`) — that was the point of the emitter and it stays the point. What closing them cost
was **seven decisions**, and each is written where it can be checked:

| Refusal | Decision | Where |
|---|---|---|
| `forever` | `for (;;)`; `on_exceeded` becomes a **checked reference**, not a comment | `emit::forever` |
| `descendants of` / `ancestors of` | «B41b»: `tree { parent, child, sibling }` at the **table**, checked once (`D006`-`D008`) | `SYNTAX.md`, `kbedingung::baumkanten` |
| `let … else` | «C3a»: `-> T or R` in the **signature**; `bool f(T *_wert, R *_grund)`. `N028`/`N029` hold both directions | `SPRACHE.md` §8.1 |
| `exchange update` | «C4b»: the bounded CAS loop, with `bounded … ops on_exceeded …` — the same words a `retry` carries | `ast::XForm::Update` |
| `format` bit gap | `bool @N` is a bit field, `embeds […] scale K` is a **position**, and the word width comes from the group's integer fields | `emit::format_` |
| `static` over an array | the length stands **behind** the name in C, so it cannot live in `ctyp`; `= 0` is `{0}`, any other value is written out | `emit::feldstatisch` |
| `linear type T;` | a **token**: one byte that carries a right and no data. The ghost is erased, the token is not | `emit::Namen::marken` |

Plus the four item kinds `walk`, `entry`, `entrust`, `boot` — and with them **the catch-all
arm of the item match is gone**. *An `_` arm does not only let new things fall through; it
lets you forget what is already there:* writing the four out produced three refusals for
constructs that had been lowering for weeks, and `rustc` said so in the same minute
(*unreachable pattern*).

> **And the emitter found five faults in ITSELF**, every one of them hidden behind an earlier
> refusal: the name resolution was GLOBAL (a parameter called `m` in two functions produced a
> dot where an arrow belongs), a `format` field became a field access instead of a reader
> call, `gabbro_kern()` was called and never declared, types stood at their place instead of
> before their first use, and the eight-byte reader called a four-byte reader that nobody
> collected.

---

---

## «B8» — `fnptr`, all four halves *(2026-08-21)*

The item stood in `TODO.md` as *„BLOCKED, not demand-less"* while the build was already
committed — **the bookkeeping aged inside a single day this time.**

| # | half | before | now |
|---|---|---|---|
| 1 | producer `&f` | `P011` / `M119` | `ExprArt::FnWert`, `M127`/`M128` |
| 2 | call through a place | `P017` / `P001` | `CallTarget::Place`, `M129` |
| 3 | lowering | `C001` | `bool (*bereit)(void);` · `t->senden(b)` |
| 4 | contract at the pointer type | — | `effects`+`costs`, `N035`–`N037` |

**The design move matters more than the construct:** `Ruf.pfad: Pfad` became
`Ruf.ziel: CallTarget` — a sum type **without a catch-all**. The compiler then enumerated
**72 pass sites in 14 files**; *silence was not a default branch but a compile error.* The
effect hull survives: `gift/242` falls at `E008` through an **indirect** call, and the
mutation that removes it is caught.

> **What does NOT cross an indirect call says so instead of staying silent.** `locks`,
> `masks`, `consumes`, `publishes` are keyed by the callee's name; **`N036` refuses them AT
> THE TYPE.** The measured justification: Caprock's four indirect call sites take no lock.
> *The gap refuses rather than passing.*

And the unbooked finding was the more valuable one: **`fn(…)` mapped to `Typ::Unbekannt`,
which is compatible with everything** — `let x : u32`, `: bool` and `: ptr<…> Treiber` from
the *same* `t->bereit` gave **zero type errors in one file**. *A type that accepts everything
is not a type*, and the rule was silent from absence, not from intent.

---

## Three K100 records that had been sitting in the OPEN list *(moved 2026-08-21)*

> **`TODO.md` carries exclusively what is OPEN**, and these three said in their own text that
> they were closed — two of them since 2026-08-19, one since the same morning. *A record in a
> list of open items is a list that no longer sorts.*

### `K010` — under a lock the frame may NOT be parametric

The finding before it was the **silence**, not the line: `lock KAPPEN … held <= 40 * eintraege
ops` over a `locks` block with five operations gave **4 items, 0 errors, 0 hints** —
`haltezeiten` took only what `konst_wert` yielded, **and with the map `K002` fell too.**
*A promise that switches off the guardian it was supposed to feed is more expensive than none.*
Evidence: `beispiele/gift/75`, a four-way speech test in `rechenwerk.rs`, and the mutation
`haltezeit-darf-symbolisch-sein`.

### `N010` — a `bank` with `stride 0` produces EMPTY cells

Flushed out while proving `device.konstruktor` (2026-08-17), closed on 2026-08-19 in
`namen::schritt_pruefen`. A `bank … stride 0 count 4` now gives exactly one refusal:
*„bank FRR has `stride 0` -- every cell is empty"*. **The item stood in the open list while the
template register beside it already carried the opposite statement** — two books over the same
thing, and only one of them tended.

### `PL.1` — the pass register, laid down 2026-08-21

`struct Pass` carries its statement field, **51 statements over twelve passes**, and the second
tooth stands: `./instrumente/pruefe-saetze.py`, mark 45, driven red from the outside in both
directions. **45 measured, 6 conjectured, 0 PROVED** — *the third column is empty, and it is
the whole rest.*

> **The ratchet bit before anyone needed it.** The register tree was eight commits older than
> `master`; after the merge the guardian reported **48 instead of 45** — the three identifiers
> from stage 6 had no statement. *They were deliberately NOT entered in advance, because that
> would have made the merge artificially green.*

**And the register's first day produced nine findings that no tool had reported.** A tool can
find that a clause has no reader; that a reader reads the WRONG thing is found only by whoever
writes down the sentence the rule must hold. *That is why PL.2 is not a bookkeeping item.*

---

## Wave 4's two conditions, both settled *(2026-08-21)*

### «B38» — the side condition on the named carrier, built as `H101`

*„The continuation re-checks **or** names what it carries instead"* got its second half:
**a carrier `masks IRQ` counts only if the entry context carries `nested masked`**
(`kontexte.rs`, wired in behind `geteilt`, no new pass number).

**And the price was measurable.** Before it, one word in an effect list bought the exemption
from `H013` — the same file, with `nested never` at the entry:

```
gabbro pruefe probe-schlupfloch.gab    # masks IRQ + assume ein_kern  ->  0 errors
gabbro pruefe probe-ohne-masks.gab     # the same file without it     ->  [H013]
```

*That is the assurance from R15 in its purest form — satisfied as soon as the checker stays
silent.* `nested never` does not count: `never` is about re-entry, `masked` about the state.

> **The side finding is the more uncomfortable half:** `Verschachtelt::Maskiert` had no reader
> outside its producer, so the remedy `H101` demands would have triggered `H013` **anew** —
> *a rule whose remedy triggers another rule is not a rule.* `ein_kern_deckt` now takes
> `nested masked` along.

Measured before building: **4** carriers `masks X` in the whole corpus, **0** of them at an
entry with `nested masked`, and `nested masked` itself had **zero** occurrences although the
grammar has always carried it. Effect: 2 sites, both in poison, **0 of 47** clean examples.

### «B39» — measured, and deliberately NOT built

`hardware A, D;` was a candidate for a new word. **Measured: the collision does not occur and
cannot** — `group` has no `ops` clause, `walk` has no `by ops`, and `R001` sees a `walk` in
**no** address space at all (control probe: `beispiele/gift/58` does fall). *Rule A would have
forbidden the build*, and it would have been column 1 of the convergence bet.

> **Four measured zeroes are the result, not the absence of one.**

What stayed open is smaller and has an address, and it moved back to `TODO.md`:
`mmu_schreibt_nur_a_und_d` is tied to nothing — `ein_kern` is the only assumption name any
pass reads at all.

---

## Moved out of TODO.md on 2026-08-31 — the reach counter counted per VALUE, not per CELL

`pruefe-zahlen.py` asked whether a bold table cell is guarded by looking up its NUMBER in a
set of guarded numbers per file. So a cell counted as guarded the moment **any other** cell
of the same file happened to carry the same digits and have a command.

> **Measured on 2026-08-31, and the occasion was a mark that fell for the wrong reason.**
> `H` went from 5 to 4, two register cells in `dokumente/PLAN.md` became a bold four, and a
> completely unrelated row dropped out of the unguarded list — **without ever having been
> given a command.** The mark sank from 146 to 145 and read like progress.

The key carries the PLACE now — line and column of the match, derived from the pattern's own
position, so no register entry had to be rewritten (the entry in `TODO.md` predicted *"a
rebuild of the register and not a line"*; it was a line). Two numbers came out of it:

| what | before | after |
|---|---:|---:|
| bold cells without a command | 145 | **180** |
| register entries that really point at such a cell | — | **9** of 76 |

**35 cells had been hidden by a collision.** The counter-direction is the same defect and
worse: a cell that DOES get a command failed to lower the count whenever its value stood once
more in the same file.

A second, smaller one came with it, and the entry had demonstrated it while being written: a
**quotation** of a table row was read as a table cell of its own — *a register counting its
own work list*. Block quotes are excluded now, with their count printed beside the figure.

Evidence: `./instrumente/pruefe-zahlen.py` — three new directions in its speech test
(`Ortsschluessel`, `Gegenprobe`, `Blockzitat`), and the second is the one that counts: the OLD
key has to be blind at the very same spot, or the probe measures nothing.

---

## Moved out of TODO.md on 2026-08-31 — three producer faults `-Wextra` does not see

> **The W24 prelude asked for the SHAPE, and the shape is the finding.** Over all 83 emitting
> files of eight roots — not the two of stage 9 — `cc -Wconversion` names **4 sites in 3
> files**, and each hangs on exactly ONE construct. *A refusal that fell eighty times would be
> a statement about the language; these are statements about three lines in `emit.rs`.*

| | what it was | who says it now |
|---|---|---|
| **A** index narrowing | `a.slots[i].kopf = i;` writes a `uint32_t` index into a `u16` field and into a `u16` atomic, silently. `index into T` lowers to `uint32_t`, `count QGROESSE = 8` needs three bits | the **producer** writes `(uint16_t)(i)`. `M101` already refuses the case that does NOT fit — measured with `count 100000` into a `u16` field — so the cast is the checker's sentence, carried into C |
| **B** two prototypes | `beispiele/29-undurchsichtig.gab` declares `pa_aus_zahl` as `pub impl fn` and as `extern fn` in a second module, one prototype with `__attribute__((const))` and one without | the **producer** drops the second declaration. Giving the `extern` half the attribute was the other way and `wirkungsattribut` had already refused it: at an `extern fn` the effects clause is an ASSUMPTION, an attribute an INSTRUCTION |
| **C** float width | in `messung/proben/probe-f32-literal.gab` a literal without `f` beside an `f32` lifts the whole computation to `double`; `39 990` of 200 000 values differ from `v * 0.1f` | the **producer** appends the `f`, inherited through parentheses and binary nodes |

**Three times the same outcome, and that is not chance:** all three are places where the
checker HAS a fact and C cannot see it. *A refusal would have been wrong in all three — the
programs are correct.* What was missing was the translation of the fact into the language the
C compiler reads.

**The one refusal that did come with it** hangs on B: where the two declarations of one name
lower DIFFERENTLY, nothing is dropped and `C001` speaks. `impl fn f(z : u64)` beside
`extern fn f(z : u32)` passes `gabbro pruefe` with **0 errors** and `cc` rejects the C —
*silently dropping the second declaration would take that error away*, so the refusal is what
makes the dropping safe.

**Evidence:** `messung/DREI-ERZEUGERFEHLER.md` · `crates/gabbro-check/src/emit.rs`
(`gleitkommatext`/`ausdruck_breit`, `prototyp_kern`/`eigene_ruempfe`, `verenge`) · probes
`f32_literal_traegt_seinen_suffix`, `ein_name_ein_prototyp`,
`index_in_ein_schmaleres_feld_wird_umgewandelt` · mutations `f32-literal-verliert-sein-f`,
`zweiter-prototyp-kommt-zurueck`, `index-verengt-sich-wieder-stillschweigend` — each set by
hand, built, and measured to kill exactly one probe of 123; anchor count 355 → 358, with
`veroeffentlichung-nimmt-die-vorgabeordnung` re-anchored.

**The counter after the work: 0 of 83** under `-Wconversion -Wdouble-promotion
-Wredundant-decls -Wsign-conversion` and ten further sharper switches. No file left the
emission — 83 emit before and after, `pruefe-emission.sh` unchanged at `79 von 79`, ratchets
54 / 25.

**`-Wconversion` was NOT put into the gate.** It costs nothing today, and that is a
measurement and not a decision; `TODO.md` carries it, along with the representation question
(should `index into T` lower to the narrowest width its `count` needs?) and the checker rule
against the contradictory pair.

---

## Moved out of TODO.md on 2026-08-30 — `result-in-ensures` carried two cases, and named a third

> **The W24 prelude turned the entry around.** It stood as *"`LeanReason::Result` carries two
> cases under one name, one of them a gate away"*. Measured on the unchanged checker: the case
> the NAME describes — `result` in an `ensures` — does not refuse in the obligation channel at
> all. It became a goal on 2026-08-28, `bindLocal s'.local' "result" v`. *The sentence beside
> the label had outlived its own gate.*

What really stood under the label were two others, refusing for opposite reasons: `result` in a
**BODY**, where the word names nothing and never will — a program error — and an `ensures`
dropped **on purpose** by the export datum, the conservative direction. Split by making the
`bool` a three-valued site (`ResultSite::{Body, Contract, Bound}`), so the distinction sits at
the PLACE the word stands in and not at which tool is running — both channels translate a body
first.

**Evidence:** `messung/ERGEBNIS-ZWEI-NAMEN.md` · `crates/gabbro-check/src/lean.rs`
(`LeanReason::ResultInBody`) · probes `lean_ergebnis_bleibt_im_rumpf_abgesagt` and
`lean_export_sagt_die_zusage_unter_dem_klauselnamen_ab` · mutations
`lean-ergebnis-auch-im-rumpf` (re-anchored) and `lean-ergebnis-rumpf-unter-klauselnamen` (new),
each set by hand, built, and measured to kill exactly one probe of 234.

**It buys no goal**: 75 · 9 · 66 before and after — no corpus file writes `result` into a body.
*It heals a label, and the honest report says so.* What it uncovered instead is open in
`TODO.md`: `gabbro pruefe` accepts `result` in a body with 0 errors.

---

## Moved out of TODO.md on 2026-08-28 — `ops insert, remove, relabel` is built

> **Found by `./instrumente/pruefe-todo.py`, a day late, and the delay is the more useful
> half of the record.** The entry stood as `- [x]` in a file that claims to carry exclusively
> what is OPEN — and the guardian built to catch exactly that had been aborting inside its own
> speech test, because the speech test measured the README instead of itself. *A guardian that
> stops before reaching its object produces silence, not a pass.*

The three words stood in the lexer, in the EBNF and in the vocabulary table; what was missing
was the **generator** — and with `relabel` a condition that `insert` and `remove` do not need.
Built on 2026-08-28: `insert`/`remove` in the morning
([`messung/OPS-ERZEUGER.md`](messung/OPS-ERZEUGER.md)), the call form in the afternoon
([`messung/OPS-RUFFORM.md`](messung/OPS-RUFFORM.md)), `relabel` with its condition in the
evening ([`messung/OPS-RELABEL.md`](messung/OPS-RELABEL.md)).

**And the condition is the message, not the generator.** `beweise/Table_Ops_Erhaltung.thy`
carried only the counterexample (`umhaengen_faellt`), so the generator refused `relabel` — a
word of a closed set that generates nothing and that nobody can call, at 127 measured corpus
sites. The proof came first (K100's second gate): `umhaengen_erhaelt` (U-3) now says WHAT the
relinking falls on, `G-1`/`G-2` show that the old counterexample fails at exactly that
premise, and `D012` holds it at the call site — in a form that costs no new word
(`!(t.slots[p] reaches t.slots[s] via elter)`).

*The residue is named and stayed in [`TODO.md`](TODO.md):* the proof that the emitted C
bodies ARE the three model functions — the same gap `beweise/Table_Absenkung.thy` names in
its own words.

---

## Moved out of TODO.md on 2026-08-21 — Stufe 6, three items that closed

> **`TODO.md` carries exclusively what is OPEN.** These three are done with no residue; what
> is left over from the same run stands there, not here.

### The certificate now separates the two CURRENCIES of an assumption

*„An overriding assumption WITHOUT a `falsifier` is a refusal — not because the probe proves
anything, but because it makes the claim refutable."* **Half of it was already closed:** the
grammar forces either `falsifier <probe>` or `unfalsifiable "<reason>"`
([`dokumente/SYNTAX.md`](dokumente/SYNTAX.md):1101), and the certificate's *list* has carried
the distinction all along. Open was only the **verdict line**, which threw both currencies
into one pot. Since 2026-08-21:

```
13 assumptions (5 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), …
```

Exactly the shape of its neighbours (`N of them UNPROVED`) — and the same class that was
closed one day earlier at the foreign narrowings: *an assumption of a different currency,
counted with the rest.*

### The dividing line, argued at a case that EXISTS

*„The first disputed case belongs in `dokumente/BEWEIS.md`, not in a footnote."* The case is
the reclamation of a dying thread's kernel stack, read in `caprock` (read-only). By the
criterion it is **plumbing** — **and it does not fall by construction.** Caprock does not
discharge it either; it **counts the opportunity** and records *„0 thefts over 4295 windows"*
— R15/W10 in real kernel code.

> **The line holds, but the sentence riding along with it breaks.** *„Plumbing = falls by
> construction"* is not true: there is a third kind, and that is the axiom layer.

### `M120` — and `Self` was the SMALLER half

`sammle_namen_pred` did not know `Self`. Measured while building it: **five of six probe
units passed with 0 errors before.** Blind were the five `PredArt` connectives
(`Klammer`/`Nicht`/`Und`/`Oder`/`Folgt`) and `ExprArt::Eingebaut` (`sizeof`/`lenof`/
`aligned`) — **every compound postcondition was unchecked.**

> *`M111` fell silent along with them, and that is the lesson:* its condition carries
> `!namen.is_empty()` — **a blind branch collects no names, so the rule saw „nothing to say"
> instead of „nothing seen".** A catch-all that stays quiet mutes the rule above it without
> touching it.

The `match` no longer carries a catch-all. Poison 223–225 / 227–229, six mutations, all
caught.

---

## Moved out of TODO.md on 2026-08-20 — three closure records

> **`TODO.md` carries exclusively what is OPEN**, and these three sections said in their own
> headings that they were closed: *„all nine closed the same day"*, *„two blocking findings,
> and both sat in the tool"*, *„executed 2026-08-19, all five columns"*. They stood in the open
> list as a record of what the closure cost — *and a record in a list of open items is a list
> that no longer sorts.*

### From the review of 2026-08-19 — **all nine closed the same day**

*Each came with a measured output and each leaves a poison probe behind. The list stays here
as a record of what the closure cost; the details are in
[`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md).*

| was open | closed as |
|---|---|
| `effects { locks L }` never redeemed | **`H011`** — redeemed by a `locks` block, a callee's hull, or `requires Held(…)` |
| M2 tracks only linear PARAMETERS | **`L107`** — a value that arises in the body is consumed or leaves through `return` |
| the pairing compares payload NAMES | the key is now **`(atomic, payload)`** — and it found a real error in `beispiele/05` |
| the frame ends at the argument boundary | the graph **maps callee parameters to caller arguments**; `wirkungen` drops what is discharged locally |
| the lock order is intraprocedural | **`H012`** — the rank order runs THROUGH calls, over the callee's hull |
| `claim` injects C | `emit::kommentartext` at one place — verified to `nm` finding no injected symbol |
| a recursive type overflows the stack | the guard is threaded through compound fields, and **`N019`** names the type that has no size |
| `own` is a synonym for `rw` | **the specification was wrong, not the pass** — `SYNTAX.md` §3 now carries the measurement |
| lexer panic · licence entry | **`P038`** (measured depth limit) · `license = "AGPL-3.0-only"` |


### From the SECOND review of 2026-08-19 — two blocking findings, and both sat in the TOOL

*The grade rose to 2− and was held there by two sentences: the test suite did not run without
a `RUST_MIN_STACK` that stood nowhere, and a diamond in the call graph counted as a cycle.
Neither was a rule that was too weak — both were measuring apparatus that could not measure.*

| was open | closed as |
|---|---|
| a diamond `f → g,h → k` reported «cycle over k», and `E008` fell silent | `pfad` (who lies UNDER me — only that is a cycle) split from `fertig` (memo, so the diamond stays linear); poison 161/162 |
| `cargo test` died without `RUST_MIN_STACK` — the third attempt at the depth limit | **32**, measured on the whole chain on 2 MiB in **debug**; a test on its own 2 MiB thread now holds the number |
| `0` plus a multibyte character killed the compiler | `lex.rs` read a **byte** as a character; now `L006` — and the umlauts in `ist_buchstabe` were never read either |
| `rust-version = "1.75"` | measured: 1.75 and 1.80 end with `E0658 float_next_up_down`, **1.86.0** builds |
| a sixth of the mutation catalogue measured nothing | 25 dead anchors repaired; `--anker` checks it **without a build**, and the full run now FAILS on one |
| `pruefe-luecken.py` always returned 0 | a speech test, a null-run precheck and an exit contract — **13 of 13**, plus two entries proven to be NULL mutations |
| the frame ends at the call boundary | **`E008` compares the PLACE**, not merely the kind — and the corpus corrected for the fifth time (`beispiele/09`) |
| `own` is only a synonym for `rw` | **`R004`** — the same place at two `own` parameters of one call; the alias question stays M3's |
| `on_exceeded` on an undeclared name stays silent | **`S007`**, the third state — the name pass never took the responsibility that was handed to it |
| the poison corpus accepts only errors | `-- erwartet: Hinweis S007`; until then **no hint code had a probe**, not even `E009` |

*Three entries below this table were removed on 2026-08-19 because they had been closed the
day before and nobody struck them: `check` has four poison probes (`pruefe-konstrukte`: **0
without a probe**), its four promised errors are `N020`–`N022` plus a grammar that makes
`can_fail` obligatory, and NL.2's four clauses without readers are `V008`/`N020`/`N023`/`N024`
(**`ZUSAGE 0`**). **A list of open items that carries closed ones is the same second register
as a stale figure** — and `pruefe-todo.py` cannot see it, because the prose is right about a
world that no longer exists.*


### «K5» — **executed 2026-08-19, all five columns** ([`dokumente/PLAN.md`](dokumente/PLAN.md))

| column | built | evidence |
|---|---|---|
| K5.1 publication ordering | `V006` `V007` | poison 147, 148 |
| K5.2 rank without a value | `H014` | poison 149 |
| K5.5 argument mapping | — | the message names the caller's own place; a non-place argument gives `E009` |
| K5.3 context matrix | `gabbro kontexte` | poison 152 · exemptions only under `assume ein_kern` |
| K5.4 `decreases` | `K008` `K009` | poison 150, 151 · `beispiele/33` |

**And a find that only the building showed:** `costs` was *unsatisfiable* for recursion — a
call counts the callee's DECLARED cost, so on a cycle it counts its own, and the body
necessarily exceeds its own promise. `K001` fell on every correct recursive function, **which
is why the corpus contained none.** *That looked like a style choice and was a language limit
nobody had marked as one.* With a `decreases`, `costs` is the promise of ONE pass.


## The compiler — ~~**ten**~~ **twelve** passes, none open (plus two more: «B37» and the lock discipline)

`cargo run --bin gabbro -- paesse` · ~~**3 fully built, 7 partial, 0 open**~~ — **2026-08-31: `SENTENCES: 71 over 12 passes -- 64 measured, 2 ARGUED, 5 CONJECTURED, 0 proved`**. *Die Zahl der Pässe ist gewachsen, und die Zeile darunter nannte noch die alte Aufteilung; die neue liest man am Befehl ab, nicht hier.*

> **The tenth is NEW, and that is a change to the specification.** `SPRACHE.md`
> part III §6 fixes nine and says *"the specification is the pass list"* — a tenth therefore
> does not mean "one module more" but **the list has grown**. The reason is
> measured (SWEEP, V4), not designed: an invariant **between** carriers has no place in the
> nine passes.

| # | Pass | Codes | Evidence |
|---:|---|---|---|
| 1 | **Namen** | `N001`–`N003` | `crates/gabbro-check/src/namen.rs` |
| 2 | D1/D2 *(partial)* | `D001`, `D002` | `kbedingung.rs` — the K condition, `by ops` per **field** |
| 3 | **M1 + V1–V3** | `M101`–`M105` | `m1.rs`, `typen.rs` |
| 4 | M3 *(partial)* | `R001`–`R003` | `m3.rs` — spaces, rights, placement rule |
| 5 | M2 *(partial)* | `L101`–`L105` | `m2.rs` — real linearity |
| 6 | **M4/loops** | `S001`, `S002` | `schleifen.rs` |
| 7 | Pairing *(partial)* | `V001`–`V004` | `paarung.rs` |
| 8 | effects *(partial)* | `E001`–`E010` | `wirkungen.rs` — since 2026-08-16 **with the read half** (reading A) |
| 9 | costs *(partial)* | `K001`–`K004` | `kosten.rs` |
| **10** | **Group** *(new, partial)* | `U001`–`U007` | `gruppe.rs` — lock imprint, move **and connection statement** |

> **"Partial" for M2, M3 and pairing does not mean "half finished" but "finished, resting on a
> named item"** — ghost deletion, the barrier out of the space, the memory model. **Three
> of them are the same item: the axiom layer.**

**Plus the call graph** (`aufrufgraph.rs`, 268 lines) — it solved three blockers at once:
`H005`, the call effects in pass 8, and the separation at the class *Phase*.

## The plumbing classes — **9 of 11** carried

Newly collected 2026-08-15, **not reconstructed**, x86 only
([dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md), *Neuerhebung*):

| carried | by what |
|---|---|
| **Index** | `index into T` inherits `count N` · `M103` |
| **Overflow** | M1 range types · `M101`/`M104`; intended wraparound since «B32» at the slot **and** at the register |
| **Alias** | dissolved rather than closed — core state needs no pointer (A1); where it does, `own` makes it linear. Evidence: `beispiele/09-ohne-zeiger.gab`, `beispiele/15-own-traegt-beide-rechte.gab` |
| **Lock** | `rank`/`held`/`shared held` · `H001`–`H006` · `K002`/`K004`; the **lock order has been recomputed since 2026-08-16**, not merely declared |
| **Termination** | three loop forms · `bounded`/`on_exceeded`/`progress` · `S001`/`S002` in `schleifen.rs`, `beispiele/04-schleifen.gab` |
| **Leafness** | `descendants of` + `by consuming` with a witness ordering · domain bound in `kosten.rs`, `dokumente/FRAGMENTE.md` (`revoke`) |
| **Publication** | `publishstmt` at the store · pairing pass · `relaxed` carries no payload · `V001`–`V004` in `paarung.rs` |
| **Frame** *(booked in retrospect 2026-08-16)* | `effects` holds writes, `locks` **and reads** (`E010`, reading A) and the call effects (`E008` over the call graph). **The named limit:** `E010` speaks only about declared world state — in an excerpt it has zero bite, in a complete translation unit the name pass covers the rest |
| **Phase** *(closed 2026-08-17 with «B37»)* | the linear ghost token carried the order as **linearity**, not as **order** — all 720 orderings of F7's six boot steps type-checked. `order { … }` on the token plus `advances a -> b` at each step; `O002` forces the step forward, `O003` refuses a step that meets the token on the wrong stage. Since K11.1 the branch is **decided**, not reported: all branches must reach the same stage (`O006`), a branch ending in `return` does not join, and a step inside a **loop** is refused — *a step happens once, a loop often.* **The named limit:** the softer reading — carrying a SET of stages and letting the next step accept all of them — is not built. *From the strict form one can loosen; the other way never* |

**The two that are NOT carried, and each for a different reason:**

| open | why | Evidence |
|---|---|---|
| **Race** *(carried in part since K11.2.1/.3)* | **`protects` now bites** (`H007`): every access to a protected place stands under its lock, and a lock nobody takes is reported (`H008`). **The ordering lowers** — `atomic_store_explicit`/`atomic_load_explicit` carry the ordering the source declared, not C's default, under **A10**. **The named limit, and it is the whole class:** Gabbro does not say **who runs concurrently**. `entry`/`boot` declare contexts, but all four `dispatch` targets in the corpus are `extern fn` — the hull over a context root is empty, so *„every place two contexts touch is locked or atomic"* cannot fire once. *And a differential test cannot show the absence of a race* | `geteilt.rs` (`H007`/`H008`), poison 74, `pruefe-emission.sh` unit 9, `gabbro annahmen` A10 |
| **Refinement** | *the lowering.* Eight translation units stand, measured by execution; seven of the ten fragments have no C at all. `gabbro zeugnis` says per file what its translation rests on — **but a certificate over THIS translation is no statement about ALL inputs** | `./instrumente/pruefe-emission.sh` (8 units, each certificate against a booked finding), `crates/gabbro-check/src/zeugnis.rs` |

## Constructs that are built and evidenced

| Construct | Reason | Evidence |
|---|---|---|
| **`locks shared`** | measured: 33 `read()` against 44 `write()` — the hottest path was not writable | `H001`–`H005`, `beispiele/10`, poison 38–42 |
| **`wrapping` at the register** («B32») | virtio's ring counter wraps by design; the intent stood nowhere | `beispiele/12-umlaufendes-register.gab`, `beispiele/gift/48-register-ohne-umlauf.gab` |
| **`heldpred`** | the strength of the witness, without weakening the expression | `dokumente/SYNTAX.md` (`atompred`), `beispiele/13-zeuge-mit-staerke.gab` |
| **`Some`/`None`** («B35») | `option` had **no constructor** — the existing code has always written it | `optionexpr` in `dokumente/SYNTAX.md`, `beispiele/01-tabelle.gab` |
| **`table … count N`** | `index into T` inherits the bound | `M103` in `m1.rs`, `beispiele/01-tabelle.gab` |
| **Placement rule** | an `ops` carrier lies in no `dma` space — a device writes past every grammar | `R001`, poison 58 |
| **`ancestors of`** («B41») | **the first measured need for a construct**: 4 bodies walk the device topology upwards, 226 of the 584 non-traversable lines lie there | `beispiele/18-vorfahren.gab`, `beispiele/gift/69-vorfahren-ohne-schranke.gab` |
| **`by ops` at the field** | the K condition turns from a **checking prescription into a grammar property**: `refcount -= 1` by hand is not writable | `D002` in `kbedingung.rs`, `beispiele/16`, poison 60 |
| **`shared held` (N3)** | `held` is computed for **exclusive** holders; the shared side has a computed quantity of its own | `K004` in `kosten.rs:497`, its own pot `geteilte_haltezeiten` |
| **Lock order checked** | `rank` was declared and was **never recomputed** — and two constructs appealed to it | `H006` in `geteilt.rs`, poison 67 (descent) + 68 (tie) |
| **`group … over { … }`** | an invariant **between** carriers has no room in any `table … invariant` — measured: V1–V4 in the existing code | `U001`–`U007` in `gruppe.rs`, `beispiele/17`, poison 63–66 |
| **The record constructor** («B7») | a function could not **produce** a record. **And the braced literal is refused on purpose:** it would have been the first expression form continuing with `{`, and 76 corpus sites have a `{` right after an expression — *a wrongly set context flag misreads all 76 silently* | `P(a: …, b: …)`; `M106` = `deckt fs zs ⟷ map fst zs = fs` (`beweise/Verbund_Konstruktor.thy`), `M107`, `P036`, `P037`, `beispiele/21`, **six counter-probes** in `pruefe-notation.py` |

## Measurements run, with gate and outcome

| Measurement | Outcome | Evidence |
|---|---|---|
| **Gate P2** — the corpus parses | **passed, 10 of 10** (and `dokumente/SYNTAX.md` 6 of 6) | `gabbro fragmente dokumente/FRAGMENTE.md` |
| **Mutation generator** | **passed** — `7 von 39` against `54 von 54` by hand | `erzeuge-mutationen.py`, `dokumente/MESSUNGEN.md` |
| **The 15 generator gaps** | **13 closed, 2 provably equivalent** | `./instrumente/pruefe-luecken.py` |
| **`narrow` count** | **gate missed** — N = 2, and the protocol was contradictory | `./instrumente/zaehle-bereichspflichten.py` |
| **Eleven plumbing classes** | **gate missed** — `N_neu = 5` (today 4) | `dokumente/MESSUNGEN.md`, *Neuerhebung* |
| **K/A/W over N_L** | **gate missed** — `W = 38 von 73` | `dokumente/MESSUNGEN.md`, *Buchung* |
| **Loader fragment, class *Phase*** | **the token carries: 7 against k = 5** | `dokumente/FRAGMENTE.md` F7 |
| **All four domain fragments** | **convergence metric: 0 new constructs** | `dokumente/FRAGMENTE.md` F7–F10 |
| **`Stale(T)`** | **refuted** — 2 of 5 transitions rest on `masks IRQ` | `dokumente/FRAGMENTE.md` F8, «B38» |
| **Base rate `format`** | **does not carry `format`** — 5 formats, 0 errors of the class | `dokumente/MESSUNGEN.md` |
| **`delete_leaf`** | **1,75 : 1** instead of the booked 3,6–6 : 1 | `dokumente/BEWEIS.md` |
| **`programs/`** | the reason for the breach no longer carries | `dokumente/MESSUNGEN.md` |
| **C emission, two units** | **the first yes-statements**: `.gab` → C → `cc -Werror` → executed → **result compared**. `beispiele/16` yields `42 1 8 0`; **`FRAGMENTE.md` F7 yields `123456`** — six boot steps, in order, each exactly once | `./instrumente/pruefe-emission.sh`, `crates/gabbro-check/src/emit.rs` |
| **Three fail-open paths closed** | the emitter's whole design is *refuse by name*, and it had **three exceptions** — `option index into T` → `uint32_t` (**no bit pattern left for absent**), an unknown expression form → literal `0`, `None` → the call `None()`. All three compiled; two computed something else | `crates/gabbro-check/src/emit.rs`, poison `option-wird-vergroebert` |
| **`traverse` lowered, `forever` refused — and the pair is the point** | `traverse … over slots of` becomes a plain bounded `for`: **no runtime counter**, because the domain is finite by construction. `retry` becomes a `while` **with** one, because its condition depends on the world. *The C now shows side by side why the grammar demands `on_exceeded` there and not here.* And `forever` is **refused with the folder's own finding**: `per_pass … ops` is a compile-time claim, so `on_exceeded` has no runtime trigger — the clause could only be dropped silently. Measured `16 6 0 0` | `beispiele/19-traversierung.gab`, `./instrumente/pruefe-emission.sh` |
| **F10 lowered — `retry` and `format`** | **`bounded N ops` is an operation BUDGET, not an iteration count** — divided by the per-pass cost the cost pass computes (body **plus** the `until` condition, which F4 shows can be the expensive half). And a **`format` is not a C struct**: padding and bit order are implementation-defined, so it becomes a byte pointer with accessors in the *declared* order plus **one** validity function from the `where` clauses. Measured `1 0 0 0 0 65`, and the 65 was predicted before the run | `./instrumente/pruefe-emission.sh`, `crates/gabbro-check/src/emit.rs` |
| **F8 lowered — three decisions, not translations** | `option index into T` carries the **sentinel `N`** (free, because `count N` bounds the index to `0 ..< N`; and Caprock already does it by hand as `NIL`) · a `lock` emits **two prototypes and no body** (rank and hold time are compile-time, `H006`/`K002`) · **`locks X { … return … }` releases before EVERY return** — the C8 class, and the new exit path inherits the duty because the writer does not write it. Measured: `1 1 1 0 0 1 1 1` | `./instrumente/pruefe-emission.sh`, template `option.sonderwert` |
| **Two more silent lowerings found by reading** | `x += 1` was emitted as `x = 1` — **the operator stood in the tree and the emitter never looked at it** — and `-> never` became plain `void`. Neither occurs in the three guardian units, *which is exactly why both survived* | `crates/gabbro-check/src/emit.rs`, poison `zuweisungsoperator-egal` |
| **Ghost erasure** | **`linear ghost type` costs nothing at run time** — `BootPhase` carries F7's whole safety argument and leaves **no trace** in the C. Erased in the signature, at the call site and at the `let` binding; the counter-probe on the third produced `6` instead of `123456` | `crates/gabbro-check/src/emit.rs`, `./instrumente/pruefe-emission.sh`, poison `geist-let-verschwindet-ganz` |
| **N1 (Caprock)** | **`MEM` is a leaf**, `system.rs:724` is wrong | `arbeitsprotokoll/03-N1.md` |
| **Closures by kind of use** | **gate VOID** — the population does not reproduce (89 → 64), and V-b is **empty** | `dokumente/MESSUNGEN.md`, *ERGEBNIS Verschlüsse* |
| **K100.2 — five obligations rebooked into the axiom layer** | «B19» barriers · «B38» `masks IRQ` · «B39» the MMU writes `A`/`D` · `at dma` · `atomic release` — all five are statements about the **machine**, and the right home exists. **A rebooking is not a discharge**: it carries them **by name with a probe**, which is exactly the trust the brief grants. `gabbro annahmen` now reports **19** (was 14), and **two of the five have no probe** — the MMU one would have to stop the MMU. `H = 29 → 24` | `beispiele/06-annahmen.gab`, `gabbro annahmen` |
| **Der Schnitt der Aufgabenliste — nach dem PLAN statt nach der ROLLE** | Die Datei stellte sich diese Frage am 2026-08-14 selbst, beantwortete sie am 16. mit *vier Rollen* — und **die Antwort war die falsche Achse.** Eine Rolle sagt, WAS ein Punkt ist, und nie, WANN er dran ist; 194 Punkte in vier Faechern sind keine Reihenfolge. Seit dem 2026-08-20 tragen sie die neun Stufen des Plans, und **die Reihenfolge ist die Aussage**. 194 hinein, 194 heraus. *Zurueckgestelltes steht unter NICHT JETZT mit Grund — eine stillschweigende Zurueckstellung ist von einem Vergessen nicht zu unterscheiden.* | `TODO.md`, `./instrumente/pruefe-todo.py` |
| **K100.1 — the yardstick sharpened, without a line of code** | Three hand-written `narrow` sites were counted as the same thing and are not: an **reachable** `else` branch is the programmer's statement *"this input is hostile"* (`FRAGMENTE.md`:1660, a hostile DTB) or a deliberate second net (`:268`); an **unreachable** one is a hole in M1 (`:1100`). *A yardstick that cannot tell a check from a ritual measures the wrong thing.* **The gate moved from "24 are allowed" to `N_ritus = 0` — one is too many** — and is almost met, because the old number summed two different things. `H = 31 → 29`, `L = 65 → 67` | `dokumente/PFLICHTEN.md`, `dokumente/MESSUNGEN.md` |
| **`verbund.konstruktor` machine-checked — and it was proved BEFORE the construct** | K100's second gate (`L ≤ 4`) says a template may not move from *designed* to *carried* without a proof first. Building «B7» would have done exactly that. **So the proof came first**: under `distinct fs`, `map fst zs = fs` makes *"each field set exactly once"* and *"none uninitialised"* **the same statement** — and the content lies one step further than the entry said: **the read-back is unique**. `ungedeckt 16 → 15`, `bewiesen 4 → 5`, `L` unchanged at 4 | `beweise/Verbund_Konstruktor.thy` |
| **`option.sonderwert` machine-checked — and it flushed out a premise nobody had written** | the encoding `None ↦ N`, `Some i ↦ i` is **injective**, which is what *lossless* means — **under `N < 2^w`.** At `N = 2^w` the sentinel falls onto slot 0 and `None` is `Some 0`. **The premise stood in none of the three places** (register, `SPRACHE.md`, emitter); the emitter emitted `#define T_NONE (N)` for `count 4294967296` without a word. *Satisfied in practice, unchecked in fact.* Now a check | `beweise/Option_Sonderwert.thy`, poison `sonderwert-ohne-wortgrenze` |
| **`atomic` payload-free, `check` as a function — and `descendants of` turned out to be a FINDING** | `publishes nothing relaxed` becomes `_Atomic`; **`release` is refused** — that a release store ESTABLISHES the visibility the pairing claims is a memory-model statement, and the class *Race* hangs on exactly that. A `check` becomes a `bool` function **carrying its claim and its counterprobe** — *a probe shipped without its claim is a number without a subject.* And `descendants of` **does not name the edge it walks**: `CapSpace` offers four candidates, and `chain(a, b) in` shows the grammar knows how. **An asymmetry in the grammar, not missing emitter code** | `crates/gabbro-check/src/emit.rs`, poison `release-wird-abgesenkt` |
| **Three more lowerings, and one of them names «B17»** | `x = None` resolves the **target** table's sentinel (not its own — a distinction that only shows with two tables) · `bank … at CAP.FRO * 16` becomes an indexed accessor whose base is **read from a field**, the address the stock computes by hand at `vtd.rs:442` · and **`transset` sets several bits in ONE write** — possible at a register word, *impossible at two slot fields, and that is «B17» one level up* | `beispiele/02-geraet.gab` now emits, poison `transset-nimmt-nur-den-ersten` |
| **TRAP 4 in the generated C, not in a comment** | `mirrors GCMD from GSTS;` — **one line per device** — becomes `write(GCMD, (read(GSTS) & ~changed) \| new)`. GCMD is `class w`, i.e. unreadable, so a read-modify-write is impossible; the state bits to carry sit in the register **next to it**. *In the measured code this is a mask plus a wall of comment (`vtd.rs:42-52`).* Measured `1 1 1 1` — **the second and fourth numbers ARE the trap**: without `mirrors` they are 0 and the unit switches translation off mid-operation. And the `requires` becomes **no runtime check** — the same kind of clause as `requires Held(…)`, i.e. a caller obligation; asserting here and not there would be the silent exception | `beispiele/20-falle-vier.gab`, `./instrumente/pruefe-emission.sh` |
| **The assumption set now travels WITH the code** | `SYNTAX.md` §12 demands *"the assumption set is emitted into the artefact ('proved under A1…An'), as a set of NAMES WITH CLASS"* — and until 2026-08-17 nothing did it: `gabbro annahmen` printed to the console and the artefact knew nothing. *A promise that lives only in a tool invocation does not travel with the code.* It now stands in the generated header, beside the licence notice and for the same reason | `crates/gabbro-check/src/emit.rs`, poison `annahmen-fahren-nicht-mit` |
| **Device bit fields — read yes, write no** | `v.GSTS.TES` becomes `((word >> 31) & 1u)`. **Writing one is refused**: a write to a single bit is a read-modify-write on the WHOLE register, impossible for `class w` — *and that is exactly trap 4*, for which `mirrors` exists and is not lowered. A bit position beyond the declared register width is an **error**, not an open point («B24» is about a `format` spanning two words, where the width is unsaid) | `crates/gabbro-check/src/emit.rs`, poison `bitlage-darf-herausragen` |
| **`device … at mmio` lowered** | a register is **not a field**: `r.AVAIL_IDX += 1` becomes `(*(volatile uint16_t *)(r->basis + 258)) += 1`. *`volatile` is the one place where the lowering must FORBID the C compiler something.* **`at dma` is refused** — which barrier a `dma` access needs is a memory-model statement, and M3 does not build it either. Measured `8 0 64 8`, the second number being «B32»'s intended wraparound | `beispiele/12-umlaufendes-register.gab`, `./instrumente/pruefe-emission.sh` |
| **Four templates machine-checked** | `table.induktion` · `table.indexschranke` · `consuming.ordnung` · `consuming.leermenge` — **5 silent assumptions flushed out, 2 statements REFUTED**, register 17 → 19, unproved 16 → 15; **20/16 since `option.sonderwert`** (2026-08-17) | `beweise/*.thy` (Isabelle2025-2), `gabbro schablonen` |
| **B3 — non-traversable bodies** | **passed, `p = 0,96 %` against a mark of 5 %** — but **R1 missed** (rule written down after the run) | `./instrumente/zaehle-b3.py ../caprock-messbasis`, `dokumente/MESSUNGEN.md` |
| **The 74 reassigned** | **238 obligations, each with `file:line`** — 173 K / 65 L; **gate MISSED at `H = 36`** hanging plumbing obligations. R1 kept this time (pre-registration in its own commit), R14 calibration **refuted the rule** and was repaired before the run | `dokumente/PFLICHTEN.md`, `./instrumente/zaehle-pflichten.py` |
| **The escalation of 2026-08-14** | **6 of 7 items built**, 1 open («B19»), 1 unrecoverable — and the 36 sorted onto the eleven classes **refute two booked-as-carried classes by name** | `dokumente/MESSUNGEN.md`, *The escalation … settled* |

> **The B3 entry is the only one in this table that carries a protocol breach beside its
> outcome** — and it stands here rather than in a footnote, because a done table that carries
> only outcomes conceals the most expensive line: **the token rule was sharpened in four
> versions with visible numbers.** What saves the result is not care but **rule invariance**:
> all four versions (0,03 % · 4,36 % · 0,74 % · 0,95 %) pass the mark. *The number depends on
> the choice of rule, the verdict does not.*

> **And the reassignment turned the folder's headline metric against itself.** The same
> function, the same dividing line: the **Rust** original of `delete_leaf` gives **1,75 : 1**, the
> **Gabbro** fragment gives **0,62 : 1** — because Gabbro *writes down* nine plumbing obligations
> that Rust leaves unwritten. **The language does not create them, it makes them visible**, and
> `L : K` punishes it for exactly that (**R18**). *Hence the measurand is no longer the ratio but
> `H` — the plumbing that stays on the human: **36 of 173**, i.e. **79 % carried by
> construction**.*

## Grammar — the findings from P2

**G1–G11 closed** ([dokumente/SYNTAX.md](dokumente/SYNTAX.md), `beispiele/11`, poison 43–45):
`atomicdecl publishes` · `axiom -> typeexpr requires` · the `->` ambiguity **in the
grammar** · trailing comma · `u64::max` · `O`/`@version` as a named `Sonderform` ·
`clobbers { }` empty · `count N` · `cast` disappears · the `forever` example · eight domains.

**Label collision resolved** (2026-08-16): the counter-check findings in
`dokumente/MESSUNGEN.md` are now called `GP1`–`GP3`; `G1`–`G11` belong to the grammar.
*Two label systems with the same names are the same error class as two prose orderings that
nobody checks against each other.*

**Plus:** the payload form decided from the existing code (22 × `nothing`, 11 × parentheses,
2 × without — the grammar follows the 33), the `pub` laxity (`P041`, `P034` until 2026-08-30), `pub const` in the
`table` body, and **`dokumente/SYNTAX.md` now holds its own grammar** (test
`die_beispiele_der_grammatik_gehen_selbst_durch`).

## The guardian chain — ~~nine~~ ~~44~~ **45**, each with a speech test in both directions

> **Counted 2026-08-30 with `./instrumente/pruefe-waechter.py`: `45 von 45 tragen die
> vier STATISCHEN`.** The block below was written when there were nine, and it was still
> saying nine after the chain had grown to forty-four. *A hand-kept list of tools is the
> one list nobody rereads, because it looks like documentation and behaves like a
> measurement.* The nine below are therefore a SAMPLE, not the chain; the chain is what
> the command prints.

### `pruefe-aufloesung.py` — the ratchet fell from **27 to 2**, and not one line of the checker moved (2026-08-30)

The ratchet stood red at **28 in tray 1, 27 allowed**. `TODO.md` held all three usual exits
shut, and the third one expressly: *„the guardian measures something other than its subject —
that does NOT apply here, it measures exactly what it says."*

**That sentence was the error.** It had been checked against the guardian's output and never
against its subject. Full record: [`messung/AUFLOESUNG-BEZUGSGROESSE.md`](messung/AUFLOESUNG-BEZUGSGROESSE.md).

* `emit.rs` keeps its **own** namespace, `struct Namen`. **All 61 of its signatures take
  `u: &Namen`; not one takes an `Umgebung`.** `Namen` carries three fields named like
  `Umgebung`'s — `funktionen`, `geraete`, `formate` — and fills all three with a **bare** key
  (`emit.rs:652`, `:649`, `:838`), while `umgebung.rs` fills its own **17 times** with
  `q(…)` and never bare. *A bare name on a bare-keyed map is correct; it is the opposite of
  the trap.* The old regex matched the FIELD NAME and could not see which struct `u` was.
* **Measured over 38 commits:** raw tray 1 grew 2 → 28 between 08-14 and 08-30, and **every
  step of that growth is in `emit.rs`**. The corrected number was **2 the whole time**, while
  `emit.rs` grew from nothing to 8 239 lines.
* **A ratio would have worked and been the wrong answer.** `tray 1 / lines of emit.rs` is
  stable at 2.8–4.1 per 1 000 lines — stable precisely because `emit.rs` produces both
  quantities. One would have got a clean figure while writing down that the generator is the
  subject.
* **All three cases where the trap actually bit are alive, and none is in `emit.rs`** —
  `M103` (`umgebung.rs:402`), `M108` (`m1.rs:2599`), `ist_weltname` (`m1.rs:2657`). Three of
  three in `Umgebung` code. *The surface where it ever bit is exactly the surface the
  correction keeps.*
* The fix is **tray 0**, and a site falls into it only when **both** criteria hold: the file
  declares no `u: &Umgebung` **and** fills that very map itself with a bare key. Either alone
  suffices for `emit.rs` and both agree across all 38 commits — but requiring both keeps a
  doubtful site in tray 1. *An instrument that goes quiet is the failure it is here to catch.*
* **63 sites before, 63 after.** Nothing vanished, everything was re-sorted, and tray 0 is
  printed. Fifth speech test added in both directions.

**The mark was not raised — it fell by 25.** And it stood five days beside its own refutation:
*„27 sites, **25 of them in the emitter**"* (comment of 2026-08-25). That sentence was the
finding. It was written, read, and booked as background.

### `instrumente/abnahme.py` — **one command that runs EVERY guardian** (2026-08-30)

There were 26 `pruefe-*` guardians and **no run that drove all of them**. `PLAN-AUTONOM.md`
§1.7 named eleven; every session assembled the rest from memory. Seven stood in **no list and
no collective run at all** — `pruefe-abstieg.py`, `pruefe-aufloesung.py`,
`pruefe-reichweite.py`, `pruefe-widerruf.py`, `pruefe-lean-beweis.sh`,
`pruefe-lean-programm.sh`, `pruefe-p6-beweis.sh`. **Two red ratchets rode along underneath for
two days and four merges.**

> **A guardian nobody runs cannot be told apart from one that does not exist.**

* **The cast comes from the DIRECTORY**, never from a list in the script (`pruefe-*`,
  `mutiere-*`) — a list would put the same failure one level down. A new guardian is in the
  acceptance on the day it is written.
* **Four verdicts, and the third is the reason it exists:** green · RED · NOT RUNNABLE ·
  skipped. *A crash is not a refusal* — `pruefe-wortschatz.py` dies without a file argument
  with an `IndexError` and looks exactly like a finding.
* **An unannounced crash is RED.** Its argument belongs in `pruefe-waechter.py:ARGUMENTE`; a
  declared hole has a name, an undeclared one is a claim.
* `SCHWER`, `ARGUMENTE`, `FREMDER_KORPUS` and `FRIST` are **read** from `pruefe-waechter.py`,
  not copied — two registers over one thing is `W7`. The two tools ask different questions:
  that one asks *is this a serviceable instrument?* and treats return code 1 as a proper end;
  this one asks *is the tree green?* and reads exactly the code the other ignores.
* Six speech tests on **invented** guardians, among them *an artificially red one turns the
  collective run red* and **an empty directory is red, not green** (W17).

**First run, `fisch`, 2026-08-30: 24 of 27 driven, 22 green, 2 RED** — precisely the two
booked ratchets. *The acceptance found on its first outing what five days of sessions had
walked past.*

```
./instrumente/pruefe-syntax.sh        forbidden forms, prose drift, closure, reachability,
                          terminal coverage — and ZERO build warnings
./instrumente/pruefe-wortschatz.py    terminals against the table, Sonderform counter (3 of 5)
./instrumente/pruefe-todo.py          holds the task list against itself, eight classes
./instrumente/pruefe-kennungen.py     no refusal code in two files
./instrumente/mutiere-pruefer.py      damages one rule at a time:  345 anchors (2026-08-30)
./instrumente/erzeuge-mutationen.py   twists systematically:         7 of 39   NOT re-measured
./instrumente/pruefe-luecken.py       the named gaps one by one:    13 of 15   NOT re-measured
./instrumente/pruefe-emission.sh      .gab -> C -> cc -Werror -> run -> compare, 52 units,
                          24 of them run and compared (2026-08-30)
./commit.sh               R19 — commit messages only via file
```

> **The mutation density is a diagnostic in its own right, and on 2026-08-17 it found four
> things.** Measured per checker file, `1 310` of 6 823 lines carried **zero** mutations — *and a
> surface with zero mutations is not covered, it is undamageable.* **Today it is zero of 8 163.**
>
> 1. **The template ratchet's second tooth had been dead for a day.** It read *"all unproved AND
>    longer than 18"*, so **the first proved template made it false forever** — the register could
>    then grow without limit, and it grew 17 → 19 on that same day. *A ratchet with a single
>    detent is a stop, not a ratchet.* Repaired as the literal generalisation of the sentence
>    already standing beside it: **base mark plus one slot per proved template.**
> 2. **A pass could silently not run.** `SPRACHE.md` part III says *"the specification is the
>    pass list"*; 241 lines of `lib.rs` carried no mutation, so nothing enforced it.
> 3. **The call graph's collection side had never been looked at.** All seven probes called on
>    the top statement level only — a call in a `match` arm, under `locks` or in a loop body could
>    have gone missing, and **the corpus has exactly that shape** (`delete_leaf` calls three times
>    in `match` arms, `revoke` inside `traverse`).
> 4. **`gabbro annahmen` reported 15 assumptions where there are 14** — see below.

> **The axiom layer was the ratchet everything else was measured against, and it had no test.**
> `schablonen.rs` cites it as *the* example of a ratchet that already exists; `manifest.rs` had
> neither probe nor mutation. The first probe found that `beispiele/06` and `beispiele/07` both
> declare `axiom write_cr3` identically, and the command **concatenated instead of uniting** —
> *a promise "proved under A1…An" with a duplicated A claims a larger assumption set than it
> has.* **The dangerous case is the other one**, and the repair is built for it: two files
> declaring the same NAME with different content are a **contradiction**, not a duplicate, and
> the command now refuses by name instead of printing both lines silently.

**Plus three tests, each of which comes from a paid-for error:** no pass without registration ·
`dokumente/SYNTAX.md` against its own grammar · corpus test anchored at the content instead of at
the line number.

## The working rules — ~~W1 to W12~~ **W1 to W24**

Complete in [dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md). Each comes from a
**paid-for error in this folder**, each names the damage.

## Probes

**63 clean examples, 381 poison probes, 359 tests · 53 translation units** —
`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab` · `./instrumente/pruefe-emission.sh`

> **Measured 2026-08-30, and every one of the four was wrong.** It read ~~*25 clean
> examples, 78 poison probes, 123 tests · 11 translation units*~~ — a line that had not
> been touched while the corpus grew to four times its size.
>
> | | booked | measured | by what |
> |---|---:|---:|---|
> | clean examples | 25 | **54** | `ls beispiele/*.gab` |
> | poison probes | 78 | **316** | `ls beispiele/gift/*.gab` |
> | tests | 123 | **233** | `cargo test` — 15 suites, 0 red |
> | translation units | 11 | **53** | `./instrumente/pruefe-emission.sh`, of which **24 run and compare** |
>
> **And the cause is not carelessness, it is that nobody was counting.**
> `pruefe-todo.py` has held *`N` clean examples* and *`N` poison probes* against the file
> system since 2026-08-16 — **but only in `TODO.md`**. The same words in `DONE.md` went
> past the same guardian untouched. *A rule that names one file guards one file.* Since
> 2026-08-30 rule 8 runs the two counts over `DONE.md` as well, which is why this line
> can no longer age quietly.
>
> *All four moved in the same direction: the register understated what is here.* That is
> the harmless direction — and it is still an unmeasured number.
