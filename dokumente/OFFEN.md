# Open — what is known to be missing, by name

**This file is a ledger, not a work list.** `TODO.md` says what should be done; this says what
is *known to be absent*, so that an absence cannot be mistaken for an oversight later. Every
entry names the thing, why it is open, and what would close it.

*Started 2026-09-03, out of `AUFTRAG-GABBROV.md` §2.3, §7 and §10. §10 asks that a blocked
gate land here rather than in a head; §7 asks that every yellow row of the correspondence
table stand here by name.*

---

## O1 — The big step: four obligations the semantics cannot state

**`L24`, `L34`, `L50`, `L52`.** `programmlogik/Gabbro/Body.lean`'s `exec` is big-step: it maps
a state and a statement list to an `Outcome` and produces no intermediate state. All four rows
are statements about what holds *between* the pre and the post — that no third state exists
(L24), that one does and the invariant fails in it (L34), that one effect precedes another
(L50, L52).

**It is not a gap in the specification fragment.** A fragment is a language of predicates over
the objects the shared semantics provides; a new construct in §7 would have nothing to range
over, and the plausible-looking substitute (`flush ∧ reply`) is strictly weaker while carrying
the obligation's name.

**And it is the class where GabbroV was supposed to be worth most**: `GABBROV.md` §3 picks out
§8.3.1's finding — `D013` checks that the invariant exists, expressly not that the block
restores it, so *"a `breaking` on the wrong-but-existing invariant still passes"* — as the one
place the tool would create value beyond convenience. The statement that site needs is `L34`.

| | |
|---|---|
| **what would close it** | a small-step or trace semantics for `exec` |
| **why it is not being attempted** | `AUFTRAG-GABBROV.md` §9 stop-list — `exec`'s big-step character carries the Isabelle proofs |
| **also recorded at** | `dokumente/AUSNAHMEN.md` rows 1–4, `dokumente/HISTORIE.md` (2026-09-03) |

---

## O2 — `G1` and `G5` are falsifiers that cannot be evaluated

`GABBROV.md` §11 lists five falsifiers. **Two of them cannot go red, and both looked
evaluable from the outside.**

* **`G1`** — *"a **noteworthy** part of the 66 L obligations is not sayable"*. No number, so no
  count clears it and no count trips it. Withdrawn 2026-09-03 rather than given a threshold
  after the fact (`R2`); `E1` and `E2` of `AUFTRAG-GABBROV.md` §1 take over, and they stand
  before the runs they judge.
* **`G5`** — *"the assumption set has no model"*. A question about formulas, asked of eight
  German prose sentences (`messung/GABBROV-V2.md`, `messung/GABBROV-V1.md` §6). It can neither
  fire nor be cleared until the assumptions are formalised, and that is itself on the
  stop-list.

| | |
|---|---|
| **what would close `G1`** | nothing, deliberately — a threshold set now would be set to be met |
| **what would close `G5`** | formalising the eight assumptions — the expensive half of V2, `AUFTRAG-GABBROV.md` §9 |

---

## O3 — ~~The manifest does not carry the obligation text~~ — **it does since 2026-09-03, and the half that stays open is a different one**

> **Carried out, and the counter-check moved the entry rather than closing it.**
> `MANIFESTFASSUNG = 2` writes `obligation <name> <class> <anchor> <state> <text>` per line,
> in the order `AUFTRAG-GABBROV.md` §4 demands: version field, then all three readers on
> both formats, then the format. Over the whole corpus **110 of 110 lines carry a text and
> an anchor**, none truncated, none empty.
>
> **What the counter-check found is that closing it does not close the ratchet.** Swap the
> two conjuncts and the two manifests now differ — *in the text column only*. The name
> `aushaengen :: ensures #1` and the anchor `:91` are unchanged, so **a ratchet over NAMES
> still cannot see the exchange.** §15's sentence *"the ratchet runs over names; exchange is
> visible"* has a second half that does not follow from its first: what is visible is the
> LINE. Whoever wires the ratchet takes the line, or the name has to become derived.
>
> Working, numbers and the five counter-checked rows: `messung/gabbrov/MANIFEST-COMPLETENESS.md`.

**The original entry, kept because it is what was measured:**

`SPRACHE.md` §15 promises *"Nothing is silently lost"* and lets the ratchet run over **names**.
The emitted manifest carries `aushaengen :: ensures #1` — a function name, a clause kind and an
**ordinal**.

**Measured 2026-09-03, and the failure is stronger than "the text is missing":** exchange the
first and third `ensures` conjunct in `beispiele/01-tabelle.gab` and the two manifests are
byte-identical apart from the file name in their header. `ensures #1` means
`c.slots[s].elter == None` before and `c.slots[s].naechstes == None` after. **The name the
ratchet runs over does not identify the obligation it names**, and nothing reports the change.

| | |
|---|---|
| **what would close it** | ~~`AUFTRAG-GABBROV.md` §4 — version field first, all readers on both formats, then the format~~ — **done 2026-09-03, in that order** |
| **material already present** | `gabbro pflichten --lean` carries the text as a datum (`post_duty_2 : Expr`) — *and it was measured to be a dropped field, not a missing computation, before anything was designed* |
| **what stays open** | the ratchet's subject. It runs over the NAME, and the name is unchanged by the exchange; a ratchet over the manifest LINE sees it. **Not repaired here, because it is a decision about §15's own sentence and not a defect of the emitter** |

### The subject is decided, and the entry stays open — measured 2026-09-03

**The key is `(name, class, text)`, and the anchor is only a last resort.** The four
alternatives were priced rather than argued; the working, the probes and every denominator
stand in `messung/BERICHT-O3-RATSCHE.md`, and
**`./messung/gabbrov/ratschenschluessel.py`** re-measures all of it in one second.

| | |
|---|---|
| **how far the hazard reaches** | **28 of 113** lines a SWAP can move (11 sibling groups over 6 files) · **79 of 113** an INSERTION can (every line whose name carries an ordinal, the lone `#1`s included) · **113 of 113** an EDIT of the text can, the four NAMED kinds too. *Three severities, and they must not be added up.* |
| **has it happened** | **No.** All 1091 commits of the merged tree against every parent: 459 modified `.gab` pairs, 398 clause lists compared, **0 changes** — no swap, no shift, not one edit. Independently: of 282 lines ever removed from a `.gab`, **not one** is a contract line. *So no mark stands on the wrong obligation — and none could, because `ZUSTAND` is the constant `"open"` and V4 is not built* |
| **why not a content hash in the name** | it breaks on exactly the same edits as the text does, and it additionally destroys a name that **twelve documents and three instruments** already key on, the two proof channels' `duty_2 … :: ensures #1` among them. **Strictly dominated** |
| **why not an identity written in the source** | §7's gate — and it is *not sufficient anyway*: a hand-given label stays put while the predicate under it is rewritten, which is this very transfer one edit further out. It would buy stability under a swap and nothing under an edit |
| **the price of the decided key** | measured over five edits that mean the same thing: re-indenting, wrapping a conjunct across lines and a trailing comment leave every key standing (`schnitt_bis` collapses whitespace runs); redundant parentheses and any rewording move it. **A moved key loses `closed`, which is the safe direction** (W10: it may oblige, it may not acquit) |
| **why the anchor stays out** | one added comment line at the top of `beispiele/01-tabelle.gab` moves **13 of 13 anchors and 0 of 13 texts.** The anchor is the least stable field of the record. It is kept for reading — and as the tie-break where two lines of one unit agree in name, class and text, which **17 lines of Gabbro reach**: two calls to one callee with one `requires` (`ratschenschluessel.py::DOPPELRUF`). Today the triple is a key over the whole population, **0 collisions of 113** |
| **why the entry stays open** | nothing keys on anything yet. §15 still says *"the ratchet runs over names"*, and the sentence is **false as the emitter writes names** — its own example (`revoke.functional`) is an authored name, not an ordinal. What is written down here is the key V4 must use; **the entry closes when V4 uses it**, not when it is written |

---

## O4 — `cdt_wohlgeformt` cannot hold over a table with a free slot

**Found 2026-09-03 by a solver run, not by reading.** `messung/fragmente/F01.gab`:199-200:

```gabbro
spec fn cdt_wohlgeformt(c : ptr<normal, r> CapSpace) -> bool
    = forall s in slots of c : c.slots[s] reaches WURZEL via parent;
```

It quantifies over `slots of c` — the whole table — and a slot that is not in the tree has
`parent == None` and is not `WURZEL`. `reachesIn` returns `false` on `.absent`.

```
messung/gabbrov/L05c.smt2      unsat, 0.02 s
   the invariant AND one detached slot have no model
```

`release_slot` (`F01.gab`:233) leaves exactly such a slot behind, so **no removal path in F1
can restore the invariant**, and the invariant cannot hold over any table that is not full.
`unlink` declares `maintains cdt_wohlgeformt` and does not maintain it: it sets
`parent[s] := None`, and unless `s` is `WURZEL` slot `s` then reaches nothing
(`messung/gabbrov/L05.smt2` — `sat`, with `s = 1`).

| | |
|---|---|
| **what would close it** | `forall s in used slots of c`, or a different home for the invariant |
| **why it is not being done here** | rewording an obligation decides what the fragment meant — the same shape as the `L44`/`L53` tautology finding of `messung/GABBROV-V2.md` |
| **measured at** | `messung/GABBROV-AUFTRAG.md` §2.4 |

---

## O5 — «B14» may be a fourth demand on the specification fragment, and it is not on the list

`messung/GABBROV-V1.md` records **three** demands on §7's fragment: aggregation, folds that are
not `count`, and bounded reachability. **A fourth candidate turned up in §3's run**, and it is
the difference between *refuted* and *passed* on a real row.

`L01` — *"a root has no predecessor"* — is refuted under the premises `F01.gab` declares, and
proved the moment `L02` is added:

```
messung/gabbrov/L01.smt2    sat    0.021 s   the declared premises only
messung/gabbrov/L01b.smt2   unsat  0.019 s   with L02 added
messung/gabbrov/L01c.smt2   sat    0.021 s   with cdt_wohlgeformt added instead
```

`L02` is the mutual sibling chain, `slots[s.next].prev == s`. `F01.gab`:181-183 says why it is
not declared: **«B14» — a `pred` cannot resolve an `option index into`.**

**The distinction that keeps this from being just another gap:** the other three demands are
about what the LEAN side must carry. This one is about what the GABBRO side must be able to
declare, so that a checker has the premise at all. *A demand on the specification language and
a demand on the predicate language are different work, and §7 does not currently distinguish
them.*

| | |
|---|---|
| **the question for Simon** | is «B14» a fourth demand, or a fourth *kind* of demand? |
| **measured at** | `messung/GABBROV-AUFTRAG.md` §2.4 |

---

## O6 — DEMAND 3 may not be buildable in the shape V1 assumes

`V1.lean` says of bounded reachability that the bound *"is what makes the helper total and the
unrolling finite, and it is the whole reason the row reads DEMAND and not NOT."* **Finite is
right and it is not the same as tractable.**

```
./messung/gabbrov/lauf-L05.sh 16 17 18 19 20 21 22 24 32 48 64
  bounds 2-19, 21, 24, 32, 48   sat       <= 0.4 s  (17 takes 6.6 s)
  bounds 20, 22, 64             unknown   60 s timeout, reproduced
```

**The failure is not monotone in the bound.** 20 and 22 time out while 21 and 24 answer in
under a third of a second. *A solver that answers at 21 and not at 20 gives no bound to plan
with* — a tool built on "unroll to the table's `count`" would be fast, fast, fast and then
silent, with nothing about the input predicting which.

And the bound the corpus asks for is `NSLOTS`: **80 256** in `F01.gab`, **4 096** in
`beispiele/01-tabelle.gab`. Five of the 63 rows hang on this means — `L04`, `L05`, `L09`,
`L15`, `L16`.

| | |
|---|---|
| **what would close it** | an axiomatised transitive closure instead of an unrolling — different work from the other two demands |
| **measured at** | `messung/GABBROV-AUFTRAG.md` §2.5 |

---

## O7 — ~~`N030` compares opaque types at a PARAMETER and not at a FIELD~~ — ~~**it reads the field since 2026-09-03; the half that stays open is a different one**~~ — **CLOSED 2026-09-03: the pass half was built, the construct half fell at Rule A**

> **Closed as a pass change, and the claim was re-measured before anything was built.**
> Each of the five sites of `probe-opak-am-feld.gab` was also run **alone, in its own
> file** — because *one error in a run that did not stop* is the shape of a masked
> measurement, and this tree has that class booked. Sites 3, 4 and 5 were silent alone
> too, so the four missing refusals were the rule not reaching the position, not one
> refusal hiding another. A three-mistake file reports **three** `N030`s, so the run
> does not stop either.
>
> `N030` now walks `.f`/`->f` from the binding's declared record and reads the WRITE
> end as well — `p.dev = c` is `retarget_device_view`'s own shape
> (`caprock-virtio/src/owned.rs`:127), and a rule that guards the read and not the
> write leaves the half that corrupts the record for every later read.
>
> **Over all 635 `.gab` files it newly refuses NOTHING** — the only file whose verdict
> moves is the probe itself, 1 error to 4. *And the denominator is said with it:* three
> files in the corpus hold a nominal type in a record field at all, and one of them
> (`probe-region-schnitt-und-nullen.gab`, six such reads) is a working programme that
> stays green. **A rule that refuses nothing because nothing exercises it is a
> different result from one that refuses nothing because every site is right**, and
> here it is a little of both.
>
> Probes: `beispiele/gift/669` (read) and `beispiele/gift/670` (write). Mutations:
> `ein-feld-traegt-keinen-namen`, `in-ein-feld-darf-jede-sicht`.

**What stayed open is the OTHER half:** an `opaque` record does not close its fields,
so accessors cannot be forced. It is no longer needed to catch the mixing — `N030`
bites at the field itself — but `opaque` on a record still promises a privacy it does
not have.

### It went to §7's cost gate on 2026-09-03 and **fell at Rule A, before criterion 1**

*Rule A: no construct without measured demand. The bar to argue against is
`beispiele/18-vorfahren.gab`:3–11, where `ancestors of` was admitted on **584
non-traversable kernel lines, 226 of them in DMAR/PCIe** — a measurement, not a design.*

**Denominator: 639 `.gab` files in the tree at `9b5c067`**
(`find . -name '*.gab' -not -path './.git/*' | wc -l`). *Taken at the branch point and not
after* — the four files this commit adds were written to answer `C1`, not because a programme
wanted them, and counting them as demand would be the measurement financing itself.

| what was counted | command | result at `9b5c067` |
|---|---|---|
| `opaque type X = { … }` — an opaque RECORD, which is what this item is about | `grep -rn 'opaque type [A-Za-z_0-9]* *= *{' . --include=*.gab` | **1 of 639**, and it is `messung/proben/probe-opak-am-feld.gab`:84 — *the probe written for this very question* |
| `opaque type` declarations of every shape | `grep -rhE '^ *(pub )?opaque type ' . --include=*.gab \| wc -l`, and `-rlE … \| wc -l` for the files | **75** in **50** files — 74 over a scalar carrier (`u64` 56×, `u32` 9×, `u8` 4×, `u16` 2×), one record |
| files with more than one `module` block — **the only door `opaque` privacy has** | `grep -c '^ *\(pub \)\?module '` per file, count those `> 1` | **13 of 639**, and **8 of those are poison** under `beispiele/gift/` |
| an opaque record used across a module boundary — the intersection, and the thing actually at issue | the two rows above | **0 of 639** |

*After this commit the first three read 1 of 643, 77 in 52, and 15 of 643 — the two new
`opaque` declarations are scalars (`Beleg`), so **the last row is still 0**, and the verdict
does not depend on which of the two states it is read in.*

**Zero programmes want it, and the one declaration in the tree is the measurement's own
apparatus.** That is two orders of magnitude below `beispiele/18`'s bar and below it in
kind as well: 584 lines that a real kernel already contains, against one line written
this afternoon to ask a question.

**And the door matters more than the count.** Privacy is a statement about a boundary,
and the sentence register says which boundary `opaque` uses: *"Inside the declaring
module the representation is known — the door is the MODULE BOUNDARY"*
(`d.undurchsichtig`, `D003`/`D004`, `saetze.rs`:838). Field privacy would be a claim
about the same door. **Thirteen files in 639 have a second module at all**, and none of
them declares a record.

> **What the construct would have bought is already bought.** The five files that hold a
> nominal type at a record field are all covered by `N030` since `4326830`, measured the
> same day: the mixing is a type error at the field, in both the read and the write
> direction. *Caprock needs field privacy because `cpu` and `dev` are both bare `u64`
> there (`owned.rs`:72, 74) and only visibility can tell them apart. Gabbro tells them
> apart by type, so the thing privacy was for does not arise.*

**The gate's four criteria were not run, and that is the correct outcome rather than an
omission.** Rule A stands before them; a construct that reaches criterion 1 without
demand has had its cheapest refusal skipped. *Two constructs went through this gate on
the same day and both fell at criterion 2 — this one does not get that far.*

**Booked, not built.** If a second programme ever declares an opaque record across a
module boundary, the denominator changes and the item comes back with a number. Until
then the honest entry is a refusal with its apparatus beside it.

> **One reconciliation, because both sides were right.** The lane that closed the pass
> half reported *"3 of 635 `.gab` files hold a nominal type in a record field"*. Re-derived
> over the merged tree the figure is **5 of 639** — the same three plus `beispiele/gift/669`
> and `670`, which that lane wrote *after* its own baseline run, and plus `beispiele/66`
> and `67` in the denominator from the lane beside it. **Neither number is wrong about its
> own tree, and the merged truth is a third one.**

**The original entry, kept because it is what was measured:**

*Measured 2026-09-03, out of `PLAN-HARDWARE.md` §50 #6, the second pass at the fifth mark.*

Two `opaque type`s over `u64` are two types, and handing one where the other is wanted is a
compile error. **At a bare parameter.** Read the same wrong value out of a struct field, or
out of a binding taken from that field, and nothing fires:

```
messung/proben/probe-opak-am-feld.gab: 11 items, 1 errors, 0 hints
error: [N030] …:48:24: `c` is a `Cpusicht`, and `deskriptor_stellen` takes a `Geraetesicht` there
```

Five sites in that file, four of them wrong, **one error** — and the run did not stop, so
this is *which* fire rather than *whether any*. **The obvious way out is closed too:** an
`opaque` record does not close its fields, so accessors — which would take the view at the
parameter position where `N030` does bite — cannot be forced.

**Why it is not cosmetic.** The shape it misses is the shape the case exists for. Caprock's
`Owned` (`../../caprock-messbasis/crates/caprock-virtio/src/owned.rs`:62–77) holds the CPU
view and the device view of one DMA buffer in **one record**, and its own note names the bug:
with an IOMMU window ≠ 0 the two numbers differ, and a driver that mixes them programmes the
device an address it cannot resolve. Caprock buys the guarantee with field privacy. Gabbro has
no field privacy and does not need it — `opaque` is the stronger instrument — but the check
does not reach the position where the two axes actually sit.

| | |
|---|---|
| **what would close it** | ~~`N030` reading the declared type of a field access, not only of a parameter — the same move `R013` made for pointer rights, one position further~~ — **done 2026-09-03, and the write position with it** |
| **what it is NOT** | `S2`. The language states this correctly; a pass did not read it. Same family as `R008`/`R013` in `messung/PASSREGISTER.md` — *and it closed the same way they did* |
| ~~**what stays open**~~ | ~~an `opaque` record does not close its fields. A construct question, priced and not built~~ — **priced on 2026-09-03 and REFUSED: 1 opaque record in 639 `.gab` files, and it is the probe itself; 0 across a module boundary, which is the only door `opaque` privacy has.** Rule A, before criterion 1 |
| **measured at** | `messung/FUENFTE-MARKE.md` §3, `messung/proben/probe-opak-am-feld.gab`, `beispiele/gift/669`, `beispiele/gift/670` |

---

## O8 — ~~A `tagged type` value has no constructor~~ — **closed 2026-09-14, lane 167**

> **Closed by building the producer, the same move `reasonval` was for `reason`.**
> A `tagged` case constructs in a body as `Case(payload)`, `Case()` or the bare
> `Case` -- no new keyword, no new production (the shape parses as an ordinary
> `Ruf`/`Ort`; the resolution stands in the checker, `Umgebung::variante`). The
> payload is held against the case's type, the construction answers the owning
> sum (the model's `Expr.fall cs i nutz`), and the lowering writes the SAME
> `marke`+`union` representation the `match` reads. Refusals `N280`-`N284`
> (unknown/ambiguous case, arity, labels) with gift probes `944`-`947` (plus the
> rewritten `938` for the ambiguous shape) and clean examples `120`/`121`. What
> stays unbuilt, deliberately: the qualified spelling `Aufsatz::Keine` (`M126`
> -- cases carry no type name) and a case that shares its name with a function
> (`N280` -- the emitter reads callees unit-wide). The four O8 spellings read
> today: bare `Keine` builds, `Aufsatz::Keine` still falls at `M126`, `Keine()`
> builds, `let x : Aufsatz = Keine` builds.

*Measured 2026-09-03, same run.*

**Fifteen `tagged type` declarations stand across nine corpus files**, every one taken apart
by `match`. **Not one is put together anywhere** — and that is not a habit: no spelling
exists. Four of them, each measured on its own:

```
Keine                        error: [M119] `Keine` is declared nowhere
Aufsatz::Keine               error: [M126] `Aufsatz` is not a declared `reason`
Keine()                      error: [K003] `f` promises costs, but `Keine` is not declared here
let x : Aufsatz = Keine;     error: [M119] `Keine` is declared nowhere
```

**This is the «B9» shape a third time** — *a form that exists at the declaration and has no
way to be written.* Its second instance is `dokumente/PFLICHTEN.md`:483, whose finding 1 —
*"`A::B` parses and never resolves … whether `IpcResult` is a `module`, a `reason` or a
variant type"* — is still standing. The `reason` half was closed by adding a producer
(`reasonval`, `SYNTAX.md`:591); **the variant half never was.**

> **It blocked no capability in the run that found it.** Three caprock functions return an
> `Option`, and Gabbro's error channel does the same job and says more — the absence carries
> a name. *That is why this is a ledger entry and not a hole in the fifth mark.*

| | |
|---|---|
| **what would close it** | a producer production for a variant, the same move `reasonval` was for `reason` |
| **what it costs today** | a `tagged` value can be a slot field, a parameter and a `match` subject, and can come out of a call — but no body can build one |
| **measured at** | `messung/FUENFTE-MARKE.md` §4, `messung/proben/probe-tagged-wird-gebaut.gab` |

---

## O9 — ~~a narrowing M1 has PROVED reaches C as an implicit conversion~~ — **closed 2026-09-03, in `emit.rs`**

> **Repaired the same day it was measured** (`messung/ERZEUGERREST.md` `D20`). The question
> the entry below poses — *soundness gap, or cosmetic?* — was answered by a run, not an
> argument, before anything was changed: `f_implicit`/`f_explicit` and `g_implicit`/
> `g_explicit` (the mask and the shift, each written both ways) compile to **byte-identical
> instruction sequences at `-O0` and at `-O2`** — only compiler-generated labels differ. That
> is not a coincidence of this one case: `verenge` only ever narrows into an UNSIGNED C
> target (`c_obergrenze` returns `None` for anything else), and for an unsigned target C's
> assignment conversion and an explicit cast invoke the *same* rule (6.3.1.3p2) whether or
> not the value is in range. **`M1` proving the value in range makes the two forms identical
> in every case this emitter ever writes — cosmetic, not soundness, confirmed by a run.**
>
> The repair reads two independent things `verenge` did not read before:
>
> * `ausdruck_obergrenze` — a structural bound for a mask (`x & MASKE`, bounded by the
>   literal) and a literal right shift (`x >> N`, bounded by the operand's own bound shifted
>   the same amount), tried after `indexschranke` and before falling through.
> * the register-WRITE target type, via `register_ctyp` — `ort_typ` alone never resolved a
>   register at all, so `verenge` had no target width to narrow against on a `g.REG = …;`
>   assignment regardless of what the bound side could prove. The read side already fell
>   back to it (`wert_ctyp`'s `Ort` arm); the write side did not.
>
> `zaehle-c-formen.py --uebersetzer` over the probe named below: `-Wconversion` and
> `-Wsign-conversion` both report **zero** hits, where before the repair the shift alone
> reported one. `MARKE_TABELLE`/`MARKE_UNERLAUBT` fall back with the named exit the mark
> already carried. The original entry stands below, unedited, as what was measured.

*Measured 2026-09-03, out of `PLAN-HARDWARE.md` §50 #6, the second pass at the fifth mark.*

`BEWEIS.md` §2 line 7 says of implicit conversion in the emitted C: *"none, but to be checked
mechanically."* `instrumente/zaehle-c-formen.py --uebersetzer` is that mechanical check, and
until this run it reported **zero hits over the whole corpus**. It now reports one:

```
(*(volatile uint32_t *)(g->basis + 12)) = wunsch >> 32;
warning: conversion from 'uint64_t' to 'uint32_t' may change value [-Wconversion]
```

`wunsch >> 32` on a `u64` provably fits in 32 bits; **`M101` accepts the assignment for
exactly that reason.** gcc cannot reproduce M1's reasoning, so what the checker proved
arrives in C as a bare narrowing assignment with no cast.

**And there is no way to write it otherwise today.** Measured, three forms, same emission:

| written | emitted |
|---|---|
| `g.R = w & 4294967295;` | `… = w & 4294967295;` |
| `g.R = w >> 32;` | `… = w >> 32;` |
| `let h : u32 = w >> 32; g.R = h;` | `uint32_t h = w >> 32; … = h;` |

*No Gabbro form produces an explicit cast for a proved narrowing.*

**Why it appears only now, and why that is the interesting half.** The corpus had no program
that narrows through a proved range until a virtio feature word — 64 bits reached through a
32-bit register — was written. The property held, and it held of a corpus that never asked
the question. *A guard is only as strong as the programs it has been shown.*

> **The tree's own gate does not see it.** Stage 9 of `pruefe-emission.sh` compiles with
> `-Wall -Wextra -Werror`, and `-Wconversion` is in neither. `zaehle-c-formen.py` is stricter
> than the gate on purpose.

| | |
|---|---|
| **what would close it** | ~~the emitter writing the cast M1 has already justified — the same repair shape as `D1`, at a different site~~ — **done 2026-09-03, `D20`** |
| **the mark it is on loan from** | ~~`MARKE_TABELLE` 66 → 67, `MARKE_UNERLAUBT` 31 → 32, with the named exit written at the mark in `zaehle-c-formen.py`~~ — **the named exit was taken; the marks fall back with it** |
| **why it is not repaired here** | ~~`emit.rs` belongs to another lane. The measurement is this lane's; the repair is not~~ — **repaired 2026-09-03, this lane owned `emit.rs` for this round** |
| **measured at** | `messung/FUENFTE-MARKE.md` §4, `messung/proben/probe-transport-merkmale-aushandeln.gab` — repair booked at `messung/ERZEUGERREST.md` `D20` |


---

## O10 — *"measured writable"* is a weaker claim than the fifth mark spends it as

*Measured 2026-09-03, out of `PLAN-HARDWARE.md` §50 #6, attacking the empty third bucket.*

`messung/FUENFTE-MARKE.md` books **24 of 30** driver capabilities as *unwritten and measured
writable*. Every one of those rows was established the same way: a probe was written, the
unchanged checker accepted it, the unchanged emitter lowered it, and `cc` took the result.
**That procedure answers "is this shape admissible?" and the question underneath it is "does
the admissible shape carry what the original carried?"**

**The two came apart on a measured case, which is why this is an entry and not a worry.**
`C1`, the ownership handover, closed on `beispiele/66-transport-rueckgabe.gab`:
`11 items, 0 errors, 0 hints`, emits, compiles at `-O0` and `-O2`. Re-measured, that probe
keeps caprock's **order** — `L104`, `L107`, `O003` each fire, each measured in its own file —
and loses caprock's **exclusion**: the linear thing is a ghost token, the buffer rides beside
it as an ordinary `ptr<normal, rw>`, and writing into a buffer the device owns is
`8 items, 0 errors, 0 hints`. That is the one bug `caprock-virtio/src/owned.rs` exists
against, and its own note says so at the type (`owned.rs`:60).

**The capability survived; the artifact did not.** Two `linear type`s with the write path
declared over the driver side alone give all three lost halves back, with no new word and no
pass change — `messung/proben/probe-besitz-zwei-typen.gab`, with `beispiele/gift/671`, `672`
and `673` as the refusals. So `C1` stays closed and the bucket stays empty.

**What stays open is the METHOD.** The checker cannot report a dropped guarantee, because the
dropped guarantee was never written down for it to check; a probe that goes green has, by
construction, no way of saying *"and the thing it should forbid is still forbidden."*

| | |
|---|---|
| **what would close it** | for each *measured writable* row, a **negative** probe beside the positive one — the poison file that fails if the property is gone. `671`/`672`/`673` are that pair for row #25; the other twenty-three rows have positive probes only |
| **how big it is** | 24 rows, of which 8 have a probe recorded in `FUENFTE-MARKE.md` §2 and none has a negative one. Row #27 is additionally not separately measured at all and says so in its own footnote |
| **why it is not repaired here** | it is 23 poison files against a document that will be re-derived when the driver is actually assembled. *The finding is worth more than the backlog*: it is a rule about how a capability gets booked, and it belongs at the next booking rather than retroactively |
| **the general form** | **the test is not "does it check", it is "does the thing it forbids still get forbidden".** The same shape as `W16` one level up: an apparatus that measures something adjacent to the question and looks plausible doing it |

---

## O11 — A `table`/`group` invariant that no function `maintains` is booked by NOTHING

> **STATUS 2026-09-26 (Opus agent D, `messung/OPUS-D-INVARIANTEN.md`): the booking is now a
> DUTY, in the checker and in the goal theorem.** Counting it as `W` (below, 2026-09-04) said
> *nobody owes it*; that was the gap. Now:
>
> * **Rust `N496`** (`m1.rs`, `invarianten_buchen`): a function with a body whose declared
>   effects, or derived hull, write, publish or consume a carrier of a `table`/`group`
>   invariant must name it in `maintains` -- every writer owes it, exactly as the model's
>   `schuldet` says. Poison probes `beispiele/gift/1231`-`1234`, positive probe
>   `tests/invarianten_buchung.rs`. Corpus diff: `beispiele/09` (its invariant was FALSE --
>   the zeroed table and its own writer broke it; replaced by `frei_ohne_elter`, maintained by
>   both writers), `beispiele/17` (now maintains its group invariant), gifts 66, 108 (other
>   codes, N496 joins).
> * **Model**: every writer owes the invariant at its returns (`InvGutS`/`InvGutGrund` in
>   `LogikPflicht`), an invariant no function writes is carried by the frame
>   (`inv_ohne_schreiber`), and the goal theorem's new leg `invRuhe` says it holds wherever no
>   unfinished thread is inside a writer (Zielsatz/Invarianten.lean, SATZKARTE §53).
>
> **Still open under this heading: the `ops` condition** (last paragraph below). A `table …
> ops` stays exempt from `N496`, carried by the generated mutations; a hand-written body
> touching the same slots is not asked. And an `E` obligation is booked, not proved, on the
> Rust side (the model proves it: `InvGutS`).

**Found 2026-09-03 while re-deriving the manifest split, and it contradicts a sentence the
checker's own source carries.** `Art::Walkinvariante`'s docstring weighs a refusal and drops
it with the words *"`runs online` at a `table … ops` IS carried (by `table.ops.erhaltung`),
and at a `table` without `ops` it becomes an `E` per `maintains`."* **The second half does not
hold.** An `E` arises only where some function names the invariant in `maintains`; where none
does, the invariant is declared, read by the name pass, and owed by nobody.

**GESCHLOSSEN 2026-09-04 — and the census that found it was itself wrong in every number.**

The docstring is corrected, `pflichten::lauf` has an `ItemArt::Tabelle` and an
`ItemArt::Gruppe` arm, and the fourteen sites are booked as `W`. **No ninth `Art` was built**,
and that is the point of the entry: the refusal below rested on the premise that a ninth kind
was needed, and *the argument in the row above it says the opposite* — if the statement IS
`W`'s, it needs no new kind to be booked under. A ninth `Art` buys a separate LETTER, not a
separate duty.

### The census, re-measured

The first cut said *"over the clean corpus"* without naming one. Re-measured over the
**145 of 196** `.gab` files under `beispiele/` and `messung/` that emit a register at all —
which is the only denominator on which "booked nowhere" means anything, because a file with
checker errors books nothing anywhere:

```
                                                 2026-09-04   was
named `table`/`group` invariants                     22        19
  a function `maintains` it   -> booked as `E`        4         2
  under a `table … ops`       -> carried by U-3       4         2
  NOTHING maintains it        -> booked NOWHERE      14        15
(`walk` invariants, booked as `W` since 2026-08-31:   6         4)
```

**Every one of the five numbers had moved, and the fifteen were not a subset of the
fourteen.** Three of yesterday's fifteen have a `maintains` naming them —
`beispiele/53-zwei-orte.gab`:47, `beispiele/55-kindkette.gab`:72 and
`messung/netz/udp-echo.gab`:135 — all three already present at `340ef3c`, the commit that
wrote the census, so no tree moved underneath it. Two sites were missing:
`messung/caprock/kapraum.gab`:72 and :76.

> **And the contradiction was one file away.** `pflichten.rs::spezpraedikate`, a hundred lines
> below the docstring, names `antwortpflicht_paarig` (twice), `kind_zeigt_zurueck` and
> `belegt_hat_adresse` as **the four `maintains` lines whose wording sat at a `table`/`group`
> invariant** — the same three files, written the same day, in the same source file, saying
> they ARE maintained. *Two registers over one set is the `W7` shape, and here both were
> inside one module.*

The fourteen are re-measured twice on the same day and agree: once from the SOURCE
(`invariant <name>` against every `maintains` of the unit) and once from the ARTEFACT (the `W`
lines of `gabbro pflichten` that are not a `walk`'s). The anchors are listed in
`messung/gabbrov/PFLICHTEN-KORRESPONDENZ.md` §7.

| | |
|---|---|
| **why it is an obligation** | the argument the `W` kind was built on, one construct over: *"an `E` is owed by a FUNCTION that names the invariant in `maintains`. A walk invariant is owed by no function at all."* A table invariant that no function names is owed by no function either |
| **what it is NOT** | a refusal. The same answer `D` and `W` got applies: do not refuse it, do not pretend to check it — **count it**. *A price that stands nowhere looks like zero* |
| **what closed it** | a collection site at `ItemArt::Tabelle` and `ItemArt::Gruppe` under the condition *no `maintains` names it and no `ops` carries it*, booked as `W`, plus the heading correction `Art::name()` needed to stop naming one of the three constructs it covers |
| **why it needed no format step** | **the closing line's last word is read by nobody.** `pruefe-manifest.py` matches `^== (\d+) obligations: `, `manifest-lage.sh` matches `^== [0-9]+ obligations`, and `pruefe-zahlen.py`'s awk pattern is a prefix ending at `precondition` whose sum takes fields 2–12. `MANIFESTFASSUNG` stays at `2`. *`AUFTRAG-GABBROV.md` §4's three steps are for a change a reader can misread* |
| **how it was found** | not by a check — by asking, obligation by obligation, whether a tool reading only the manifest could reconstruct each row of `PFLICHTEN.md`. **Row 1 of 63 was the first one asked** |

**What is still open under this heading is the two conditions, not the booking.** An invariant
under a `table … ops` is treated as discharged by `table.ops.erhaltung`
(`beweise/Table_Ops_Erhaltung.thy`), which covers the GENERATED mutations; whether a
hand-written body that touches the same slots can break it is a question this entry did not
ask and does not answer.

---

## O12 — `beispiele/124`'s `setze` promises too little for its own locked section

*Found 2026-09-15 by the stage (b) Opus agent while writing a G model for the program
(`messung/OPUS-BERICHT-STUFE-B.md`, `grammatik/Grammatik/Korpus124.lean`), not by a guardian.*

> **STATUS 2026-09-17 (lane 204, merge `5ececd63`, `messung/muse/MUSE-REPORT-204.md`): half
> (1) is DONE, half (2) is still OPEN.** The corpus file now promises both slots
> (`ensures konto.slots[0].stand == konto.slots[1].stand && konto.slots[0].stand == x`, the
> `kP` shape). No checker rule was added: `gabbro obligations --g` and `gabbro counterexample`
> now print a per-section `RELEASE OBLIGATIONS` row (syntactic, one-sided, a comment in the
> output, never a diagnostic). The rule half was measured, not built: a promises-only refusal
> would fall 1 of the 2 measurable files (`119`, a false positive as a refusal). **The blind
> spot below therefore still stands in the checker**, as this entry's last two rows demand.
> (Review 2026-09-21, G02: the `RELEASE HOLDS (syntactic)` row could also acquit a section in
> which a later statement or callee overwrites a promised cell; see
> `messung/review-2026-09-21/G02.md`. **Repaired by fix lane F7, 2026-09-22:** one shared,
> order-aware analysis in `crates/gabbro-check/src/freigabe.rs` -- writes and callee writes
> after the last promise break the hold, every block is walked, early exits are releases,
> bound indices are never countable. The row is still syntactic and still not a proof;
> **it is not the rule half (2) below**, which asks for a checker REFUSAL and stays open.)
>
> **STATUS 2026-09-26 (lane 263, `messung/muse/MUSE-REPORT-263.md`): half (2) is DONE --
> the refusal is `N511` (`crates/gabbro-check/src/freigabe_pruef.rs`, sentence
> `sperren.freigabe`).** At every locked-section exit (`release`, early `return`,
> `leave`, `next`) the invariant must FOLLOW from the invariant at acquire (the
> frame), the section's own direct writes (`cell == const` facts) and the callees'
> `ensures` equalities -- never their bodies -- decided over cells and constants with
> `ptr`-parameter-to-carrier resolution. The verdict is the shared
> `freigabe::beurteile`, so the `RELEASE HOLDS` row and the refusal agree by
> construction (pinned by `freigabe_zeile_und_n511_stimmen_ueberein`). 119 is silent
> (its `k.slots[0].x = 40` through `k : ptr A` establishes `40 <= GRENZE` -- the false
> positive lane 204 measured is closed by reading the write, not by weakening the
> rule); 124 and 157 hold from the promise; 118 has no section. Corpus verdict diff:
> no clean file falls; `beispiele/119`'s row moves UNPROVED to HOLDS. Poison probes
> `beispiele/gift/1261`-`1264` (weak `setze`, overwrite after promise, early return,
> one-cell direct write), each `N511` alone.
>
> Model correspondence (stated, not proved): `N511` discharges the release half of
> `SperrWechselG` (`Zielsatz/Spec.lean`: every release leaves a memory where the
> invariant holds), with the acquire half as the frame premise. The bridge from the
> Rust verdict to the G term stays open: the analysis runs on surface syntax, the leg
> on `RufMaschineG` memories -- the same standing as every other checker sentence
> against its leg.

`setze`'s contract promises only `konto[0] == x`. `hauptA`'s locked section writes both slots
and then has to re-establish the lock invariant `konto[0] == konto[1]` at `release`; with a
postcondition that says nothing about `konto[1]`, the caller cannot conclude it. **So premise
(b) of the goal theorem (`NutzerPflicht`, the user's own obligation) does NOT hold for the
source as written** — while the Rust checker accepts the file, because no rule of the checker
asks the question the model asks.

| | |
|---|---|
| **what is NOT open** | the model side. `Korpus124.lean`'s `kP` carries the stronger contract (the one the hand model `mP` always had), every premise group is proved on it, and `schlusssatz_124` is about `kP`. Nothing is claimed about the `.gab` file |
| **what IS open, and it is two things** | (1) the corpus file: either `setze`'s `ensures` is strengthened to speak about both slots, or the program is rewritten so the locked section does not need it. That is a corpus change with a re-measurement of tests and emission attached, and it was deliberately NOT made inside the proof lane. **DONE by lane 204 (see STATUS above).** (2) ~~**the more interesting half: no checker rule refuses this.** A locked section whose callees cannot re-establish the lock invariant is exactly the shape `N275`–`N277` were built for; that they pass here is a measured blind spot, not a design decision~~ -- **DONE by lane 263 (`N511`, see STATUS above)** |
| **why it must not be closed by strengthening alone** | strengthening the file makes the corpus green and leaves the blind spot in place. *The finding is about the checker; the file is only where it became visible* |
| **what would close it** | the rule half: at a `release` (and at every exit of a locked section), demand that the lock invariant follow from what the section's callees PROMISE, not from what their bodies happen to do. Then re-measure: how many corpus files fall, and is each fall a real one -- **built by lane 263 (`N511`), with the section's own writes and the acquire frame beside the promises; re-measured there (no clean file falls)** |

---

## O13 — ~~Two chain files need 72 GB of memory, so almost nobody can replay them~~ — **CLOSED 2026-09-15: the whole library builds from empty in 5 min 20 s at a peak of 6,86 GB**

> **THE CLOSING MEASUREMENT** (`ki-pc-fisch-101`, idle, Lean 4.33.1, empty build directory,
> 248 jobs, exit 0, `/usr/bin/time -f "WANDUHR %e s SPEICHER %M kB"`):
>
> | Target | before | after |
> |---|---|---|
> | `Grammatik.Kette104` | 4 min 40 s / **72 GB** | 1,6 s / **0,92 GB** |
> | `Grammatik.Kette108` | 6 min 50 s / **72 GB** | 1,1 s / **0,87 GB** |
> | `Grammatik.Parser.Uebersetze` | 47,6 s / 9,17 GB | 10,5 s / 1,99 GB |
> | `Grammatik.Schlusssatz104` | 32,5 s / 8,91 GB | 2,4 s / 0,93 GB |
> | the whole library from empty | about 25 min / **72 GB** | **5 min 20 s / 6,86 GB** |
>
> **AND THE CAUSE WAS NOT WHERE THIS ENTRY SAID IT WAS.** The `String.toList` finding below
> is right about the mechanism and was only part of the bill. Cutting `Kette104.lean` into
> prefixes and elaborating each puts the whole 72 GB on **one theorem**: `low_some` (a
> `decide` over the entire generic lowering) costs 0,73 GB, `parse4` 0,98 GB, `elab4`/`low4`
> 0,90 GB — *every stage of the pipeline is cheap under kernel reduction* — and
> `uebersetzt4` costs **69,9 GB and 291 s**. It is the theorem that glues the stages
> together, and its first tactic was `unfold uebersetzeAllg` **at the concrete source**:
> the equation lemma's right-hand side is `match lex s with …`, simplification looks at the
> discriminant, and whnf of `lex src104real` runs the UTF-8 decoder over 2064 bytes inside
> the kernel.
>
> **THE REPAIR, in two parts, both needed.** (a) The sources are pinned as CHARACTERS —
> `SRC-BEGIN`/`SRC-END` blocks of short `"…".toList` pieces, `def src104real : String :=
> String.ofList srcQuelle104`, with the bridge `lex_ofList` (`Parser/Lexer.lean`) proved by
> rewriting with the core lemmas `String.toList_ofList` and `String.length_ofList`, so the
> decoder is never run at all. (b) The unfolding happens ONCE, at a VARIABLE character list:
> `uebersetzeAllg_von_zeichen` (`Schlusssatz.lean`) takes the four stages as hypotheses, and
> the chain files apply it in one term. The same two moves fixed `u104lex`
> (`Parser/Uebersetze.lean`) and `uebersetze104_ok` (`Schlusssatz104.lean`).
>
> **NOTHING WAS WEAKENED.** Every theorem statement is unchanged character for character —
> `uebersetzt4`, `uebersetzt8`, `lex104real`, `lex108`, `kette_104 : Kette src104real`,
> `kette_108 : Kette src108`; `Kette` is still indexed by a `String`. `src104real` IS the
> text by definition, and `zaehle-kette.py` still decides whether the pin is the file byte
> for byte (it reads the `SRC-BEGIN` block now, with four new speech-test directions,
> including *the same text cut differently is the same text*). Measured after the repair:
> **chain count 2 of 2 CLOSED**, all five sieves green with `--lean`. `#print axioms` is the
> standard three for every theorem touched.
>
> **What is the peak NOW, and why this entry does not stay open for it.** The library's
> largest single module is `Parser/ElementTiefProben.lean` at **6,84 GB** — 59 agreement
> probes of the shape `lex "…" = .ok […]`, the longest literal 489 bytes, so it is the same
> `String.toList` cost in a file that has nothing to do with the chain. It fits in 16 GB
> with room, so it is a cost note and not an absence; the cheap fix, if anyone wants the
> library under 3 GB, is the same one — pin those probe texts as pieces and state them with
> `lex (String.ofList …)`. `CText104Zeuge.lean` (2,95 GB) and `CText108.lean` (2,91 GB) come
> next, then `Parser/UebersetzeAllg2.lean` (2,97 GB) and `Parser/Lexer.lean` (2,35 GB,
> `lex_keywords` over 243 words). Everything else is at or below 1,12 GB.
>
> **And the second pathology recorded below is WITHDRAWN**, see the end of this entry.
> Report: `messung/muse/OPUS-BERICHT-O13.md`.

*The original entry, kept because the finding is the interesting part. Measured 2026-09-15
on `ki-pc-fisch-101` (110 GB, 16 cores), from an empty build directory, while writing
README §0. Not found by a guardian — found by trying to be a reviewer.*

| Target | Wall clock | Peak resident |
|---|---|---|
| `Grammatik.Zielsatz.Beweis` + the two probe files (the goal theorem, 90 modules) | 4 min 33 s | **2,3 GB** |
| `Grammatik.Kette104` alone | 4 min 40 s | **72 GB** |
| `Grammatik.Kette108` alone | 6 min 50 s | **72 GB** |
| the whole library (240 modules) | about 25 min | 72 GB |

**What happens on a normal machine.** The first cold run of the full build died at exactly those
two files with `error: Lean exited with code 137` — the OOM killer. *That reads like a proof that
does not go through, and it is not one*; it is the same class as the 3 GB watchdog in CLAUDE.md,
one machine further out.

| | |
|---|---|
| **why they are expensive** | `Kette104`/`Kette108` run the WHOLE pipeline of a program — lex, parse, preprocess, elaborate, lower, and the checker Bool — by kernel reduction (`rfl`/`decide` on closed terms). Every intermediate term of a real source file lives in the kernel's memory at once |
| **what is NOT the cause** | the built library is 801 MB over 181 modules, so this is not olean loading; the cheap path proves it by peaking at 2,3 GB with the same imports |
| **what it costs us** | the ten-minute checkability of §0 holds for the goal theorem and NOT for translation validation. A reviewer with 16 GB can confirm the central claim and must take the chain on trust — which is precisely the position §0 exists to end |
| **what would close it** | (a) `Nat`/`String` reduction inside the parse pipeline replaced by compiled evaluation with a proved bridge, or (b) the pipeline equations proved by rewriting instead of evaluation (each stage a lemma, as `Uebersetze.lean`'s `Bool` pins already are in part), or (c) the certificate checked in Lean but PRODUCED outside it, so the kernel only re-checks a small witness. (c) is the direction the correspondence certificate already goes; the parse side has not followed |
| **what must not close it** | `native_decide`. It moves the cost out of the kernel by moving the trust out with it, and this tree's whole point is the axiom list |

**MEASURED 2026-09-15, and it moves the cause: the cost is `String.toList`, not the
pipeline.** The A2 lane (PLAN-UEBERSETZUNGSVALIDIERUNG §6.6) built a Lean parser for the
emitted C and ran into the same wall at a 1419-byte text -- 44,6 GB. Cut apart on
`ki-pc-fisch-101` (Lean 4.33.1), with the other agents' load beside it:

| what the kernel was asked to reduce | wall clock | peak resident |
|---|---|---|
| `lexC` over the 1419-byte text as ONE `String` literal | 364 s | **44,6 GB** |
| `(String.toList s).length = 1419`, same literal | 235 s | **38,2 GB** (OOM-killed) |
| `(String.toList s).isEmpty = false` -- the FIRST character only | 217 s | **33,7 GB** |
| the same text as 45 short `String` literals joined by `++` | 449 s | 34,6 GB |
| the same text as a `List Char` of 45 short `"…".toList` pieces, lexed AND counted | 20 s | **3,3 GB** |
| the whole parse of that `List Char` against the certificate (`a2_104`) | 11 s | 2,7 GB |

*Forcing ONE character of a long string literal costs 33,7 GB.* In Lean 4.33 a `String` is
an array underneath (`String.toList s = (String.Internal.toArray s).toList`), and
`String.length` is `s.toList.length`, so `lex s = scan s.toList (s.length + 1)` -- the shape
of `Parser/Lexer.lean` and of every `src…real` pin -- pays that conversion twice. Splitting
the literal at the `String` level does NOT help; `String.append` goes through the array too.
**What helps is pinning the text as a `List Char` built from short `"…".toList` pieces**, and
having the lexer take `List Char`. That is what `Grammatik/CText104.lean` and
`CParser/CLexer.lean` do, and it is a factor of 13 in memory and 18 in time on the same
theorem.

This did not close O13 by itself -- the conversion was made on 2026-09-15 and is only half
the story; see the closing measurement at the top. The re-measured figure for the same probe
on an IDLE machine is **17,8 GB / 95 s**, not 33,7 GB / 217 s: the original was taken with
the other lanes' load beside it. Growth is about `n^1,9`, and the 1419 bytes as 57 pieces of
25 bytes cost **1,46 GB FULLY FORCED** against 17,8 GB for one character of the literal.

**THE SECOND PATHOLOGY RECORDED HERE IS WITHDRAWN.** It said: *a MUTUAL recursion through a
fuel argument compiles to a mutual `Nat.brecOn`, and reducing it is EXPONENTIAL in the fuel
-- a seven-token probe grew to 112 GB before it was killed*, with the rule *"fuel that comes
from a token count must never reach a mutual recursion"*. **Measured again on 2026-09-15
(O13 lane) and it does not hold**: two-way and three-way mutual recursions whose first
argument is fuel, fuel really traversed, stay at the bare `lean` baseline (0,477 GB) from
fuel 10 to fuel 320, flat, with no trend. And this tree refutes the rule directly --
`Parser/Anweisung.lean`, `Parser/Element.lean` and `Parser/ElementTief.lean` are exactly
that shape, `parseTopTief` runs them at fuel `toks.length * 8 + 32` = **2032** for `tt104`,
and `parse4` reduces it in **0,98 GB**. The 112 GB had another cause, which was not
identified. `CParser/CParse.lean` §4 carries the withdrawal beside the design it used to
justify; the design (no recursion in the C expression parser) stands on its scope reason.

*A note on the measuring apparatus, because it cost an hour: **`ulimit -v` is the wrong bar
for a Lean build.** Lean reserves far more address space than it touches, and two `lean`
processes under a 30 GB virtual cap DEADLOCKED (`futex_wait`, VmSize 16 GB, RSS 0,5 GB, zero
CPU) instead of aborting -- a bound that hangs the run looks exactly like a run that is slow.
A watchdog on RESIDENT memory is the honest bar. And it must count only its OWN directory's
processes: the first one read `ps -C lean` for the whole machine, saw ANOTHER lane at 72 GB
and killed this run -- the `W16` family again, a measuring device that counts the neighbour.*

---

## O14 — An arena program cannot close a chain: the specification and the exporter have the form, TWO STATEMENT SHAPES do not

*Found 2026-09-15 by the emitter-side grammar lane (`messung/muse/OPUS-BERICHT-GRAMMATIK-EMIT.md`
§2.2 and §5.3), taken up the same day by the `alloc` lane
(`messung/muse/OPUS-BERICHT-ALLOC.md`, `dokumente/SATZKARTE.md` §33).*

`let i = alloc A (v) [else …];` and `reset A;` are **accepted with zero diagnostics**
(`beispiele/98`, `beispiele/99`: `0 errors, 0 hints`), `emit.rs` writes C for them
(`A_arena_speicher.buf[A_arena_speicher.used++] = (v);`, `…used = 0;`) and that C compiles.
`Syntax.lean` had **no `Stmt` constructor for either**, and `Arena.lean` carried the
arithmetic of the monotone region with no tie to the syntax at all.

| | |
|---|---|
| **what is NOT open since 2026-09-15** | **the specification has a form.** `Grammatik/ArenaZucker.lean` gives `reset` and `alloc` as SUGAR over the existing constructors — an arena is a table of `count = hi` slots beside a global `used` counter, `reset` is `Stmt.assignGlob`, `alloc` is `Block.narrow` + `Stmt.assignSlot` + `Stmt.assignGlob`. Because it is sugar, an arena program is an ordinary `Block` term, so `theorem gabbro_ziel` covers it with **no new case and no re-proof** (`#print axioms gabbro_ziel` unchanged, whole library green). The `else` semantics are proved on both sides of the bound, and the bridge to `Arena.lean` is proved |
| **what is NOT open since 2026-09-15, second half** | **the exporter builds the pair.** `gabbro lean-g` synthesises a table `A` of `count = hi` with one field `wert : T`, a global `A_used : int 0 hi` starting at zero, and `def gArena_A : ArenaForm gD` beside them; `reset A;` lowers to `Stmt.arenaReset`, `let i = alloc A (v) else { … };` to `Block.arenaAlloc`, and `A[i]` to the slot read of the one field. *Measured:* a probe unit with all four forms exports and **compiles under `lake env lean`.* The reservation `lo` travels nowhere, as planned (Opus lane `export`, `messung/muse/OPUS-BERICHT-EXPORT.md`) |
| **what IS STILL open, and it is not the declaration** | **two statement SHAPES, each refused by name.** (1) An `alloc` **without `else`**: `Block.arenaAlloc` always carries a full-arena branch, the emitted C carries none (`buf[used++] = v;`, no bound check), and what makes the branch dead is the checker's static count `N212`, which does **not** travel into the term. Inventing a `return` the user did not write would put a guard into the exported term that neither the source nor the C has, and the chain would then compare two different programs. (2) An `alloc` at the **top level of a body**: `Block.arenaAlloc` is a `Block` former (its first half is `Block.narrow`) and a body is an `Endblock` — the same wall `let x = f()` and `let … else` hit there. **`beispiele/98` and `99` stop at (2)**, and both refusals name the shape and the reason. Closing (1) needs a decision about the emitted C, not about the exporter; closing (2) needs an `Endblock` form for the `Block` binders, which is a change to `Syntax.lean` |
| **what is NOT the gap, measured** | *"nothing says so at the site"* was the original wording, and it is **false for the chain tools**: all four refuse BY NAME, in every statement context probed (top level, inside an `if`, inside a `traverse`, `reset` alone). What was missing is this ledger entry and a refusal that names a reason a reader can act on — the arena arm of `lean_g.rs` was a CATCH-ALL (`"{} has no G form"`), and a catch-all that happens to fire stops firing, without a word, the day an arm is added above it. It is by name since 2026-09-15 |
| **what would close it** | ~~`lean_g.rs`: read an `ArenaDecl` into a `TableModel` of `count = hi` with one field plus a `GlobModel` of type `int 0 hi`, and lower `StmtArt::Alloc`/`ResetArena` to `Block.arenaAlloc`/`Stmt.arenaReset`.~~ **Done 2026-09-15.** What remains is the two shapes in the row above, and after either of them `gabbro certificate` (`CS001`) and `gabbro corr-lean` (`GREFUSAL`) still have to be taught the two statements — the export is one gate of five. **The reservation `lo` does not travel** — it is the checker's static count (`N212`), and its model-side consequence is already proved (`arenaAlloc_unter_schranke`: below the hard bound the `else` cannot run) |
| **why the other route was refused** | refusing `alloc`/`reset` by name in the Rust checker would have made the hole loud at the cost of **deleting a feature that has a proved Lean model (12 theorems in `Arena.lean`), four checker rules with five poison probes (`N210`–`N214`, gift 885–889), 756 lines of `arena.rs`, its own EBNF in `SYNTAX.md` §9.1 and two clean corpus programs**. Two clean files would have fallen and five poison probes would have changed code. *That is a retreat, and the gap it would have closed was already named at all four chain gates* |

---

## O15 — A record as a VALUE has no `Ty`, and the extension was PRICED AND REFUSED: it gains ZERO corpus programs

*Measured 2026-09-15 by the Opus lane `produkt`, `messung/muse/OPUS-BERICHT-PRODUKT.md`. The
census row it was sent at comes from `messung/muse/OPUS-BERICHT-LINEAR.md` §1.2 and §5.*

`Typen.lean` §1 lists every `Ty` there is — `int`, `bool`, `opt`, `sum`, `grund`, `never`,
`fl`, `fnptr`, `ptr` — and **there is no product**. A record travels as a CARRIER (a `Tab`
with `count 1`, reached through a pointer; `Syntax.lean` §1/§9, built since 2026-09-15), and
it does NOT travel as a value: `impl fn fertig(k, n) -> Completion` with
`return Completion(id: k, len: n);` names no type the specification can carry, and
`gabbro lean-g` refuses it by name (`LG002`).

| | |
|---|---|
| **what the extension would be** | a `Ty` constructor `prod (fs : List Ty)` with its `Val`, its `einpassen` arm, its two `Expr` formers (construction, projection), its place in the checker Bool `Akzeptiert`, and a `#print axioms gabbro_ziel` that is still `propext`/`Classical.choice`/`Quot.sound` |
| **what it would gain, MEASURED** | **ZERO of 113 corpus programs.** A probe (`GABBRO_PROBE_SKIP_PRODUCT`, and a generous second one `GABBRO_PROBE_SKIP_FIELD` that also skips array and function-pointer fields a product would NOT close) was applied, the whole 113-program sweep re-run, and the source restored byte for byte (SHA-256). **Sieve (b) stays 15 of 113 in both runs.** Seven programs reach a product-shaped refusal; none of them exports once it is skipped. The only pure case, `beispiele/21-verbundwert`, has **four** walls, and the last two are not the product: a top-level `let` of a call, and a call in value position — *exactly the `Endblock`-binder wall of `O14` (2)*, confirmed by exporting a record-free rewrite of the same program step by step (`.claude/kratz-prod/21-ersatz*.gab`) |
| **why it is refused and not merely postponed** | *a specification extension that pays for nothing is worse than a named absence.* The extension enlarges the set of declarations `gabbro_ziel` quantifies over, so it cannot WEAKEN the statement — but every leg of `Ziel` gains a case, and `Ty` stops being a non-recursive inductive (all nine constructors take first-order data today; `prod (fs : List Ty)` is a NESTED inductive, and the checker Bool is settled by `decide`, so the kernel would reduce over the new recursion). Seventeen `Ty` match arms in eight model files would each gain an arm. **That is a re-proof of the goal theorem bought for zero programs** |
| **what pays FIRST, measured on the same run** | (1) the `Endblock` form for the `Block` binders (`O14` (2)) — it unblocks `21-verbundwert`, `beispiele/98`, `99` and every `let x = f();` at a body's top level; (2) the C side of AGGREGATE VALUES, which is **already owed by a form the specification HAS**: `beispiele/120-tagged-construction` exports today (one of the 15) and its emitted C is `static Nachricht baue(…)` with `return (Nachricht){ .marke = …, .last.Kurz = x };` — a struct returned by value. `korrOk` cannot carry it: `CTy` is `int (sgn, w) \| ptr` and `CVal` is `int \| ptr \| undef` (`CSpeicher.lean` §1–§2), and every place a C type appears in `GRow` (`setVar`, `bindLet`, `call dst`, `ret`) takes a `CTy`. **A product former would add a SECOND G form with the same unbuilt C side** |
| **a guardian finding on the way** | `instrumente/pruefe-cformen.py` builds its row key from the statement TEXT and not from the C type, so it books `return (Completion){ … };` as `stmt:return-expr` (state (i), lemma `scorr_ret`/`ergCorr_run`) and `Completion c = fertig(k, 7);` as `stmt:bind-call-unit` (state (i), lemma `bsem_bindCall`) — **two aggregate forms under scalar lemmas.** Measured, not read: `.claude/kratz-prod/klass.py` calls the guardian's own `classify_stmt`. The corpus carries **8 aggregate returns in 6 programs** and **3 aggregate binds in 2 programs**; `28` emitted functions in `13` programs return a `typedef struct` by value. *The row counts 287 (`stmt:return-expr`) and 6 (`stmt:bind-call-unit`) include them* |
| **what would close it** | the two rows above, in that order, and only then the `Ty` constructor — and its warrant is then a re-measured sweep, not this census row. **The number is booked BEFORE (`PLAN-ZIELSATZ.md` §8): `gabbro obligations` reads 1 obligation on `beispiele/21-verbundwert` (1 precondition, open) and 126 over the corpus of 113.** Nothing was built, so the AFTER number is the same, and it is written down so the next lane measures a movement rather than a memory |

---

## O16 — The C side cannot carry an AGGREGATE VALUE, and the extension was PRICED AND REFUSED: it unblocks ZERO corpus programs

*Found 2026-09-15 by the Opus lane `produkt` (`messung/muse/OPUS-BERICHT-PRODUKT.md` §3),
measured and decided the same day by the Opus lane `aggregat`
(`messung/muse/OPUS-BERICHT-AGGREGAT.md`). The guardian repair named below is that lane's.*

`CSpeicher.lean` §1 is `CTy := int (sgn : Bool) (w : CWidth) | ptr` and §2 is
`CVal := int | ptr | undef`. **A C cell in this model holds a scalar**, and every place a C
type appears in the certificate's row language takes a `CTy`: `GRow.setVar x tc ce`,
`GRow.bindLet x tc ce`, `GRow.call fc cargs (dst : Option (Nat × CTy))`,
`GRow.ret (cr : Option (CTy × CX))`. So a C value of STRUCT type has no row at all — neither
as a return, nor as a bound local, nor as a stored value, nor as a call argument. A struct
RETURN has no shape even in principle: it is the SysV ABI's business (two registers, or a
hidden pointer), and the model has no ABI.

**The emitter writes all four, and has all along.** `beispiele/120-tagged-construction` is
one of the 15 programs that export today, and its emitted C is
`static Nachricht baue(bool kurz, uint32_t x) { … return (Nachricht){ .marke = …, .last.Kurz = x }; }`.

| | |
|---|---|
| **what was BOOKED WRONG until 2026-09-15** | `instrumente/pruefe-cformen.py` built its row key from the statement TEXT, so `return (Nachricht){ … };` and `return c.len;` were the same row `stmt:return-expr` — state (i), lemma `scorr_ret`/`ergCorr_run`. **Measured by running the guardian of `HEAD` and the repaired one over the same emitted C** (`.claude/kratz-agg/vergleich.py`): **19 occurrences in 15 programs moved from state (i) to state (iii)**, and 2 more from `stmt:bind-call-foreign` into the new aggregate row. The four destinations: 16 returns in 14 programs (`stmt:return-expr` → `stmt:return-aggregate`), 1 bind (`stmt:bind-call-unit` → `stmt:bind-aggregate`, `beispiele/21`), 1 slot store of a whole struct (`stmt:store-slot-ptr` → `stmt:store-aggregate`, `beispiele/40`: `p->slots[i].lage = s;`), 1 struct passed by value to a call (`stmt:call-foreign` → `stmt:call-aggregate-arg`, `beispiele/54`: `nimm(m);`) |
| **the repair** | the classifier now reads the unit's `typedef struct`/`typedef union` names (a `typedef enum` is a scalar and is NOT one), the C return type of every function and the aggregate-typed names of every body, and classifies by the DESTINATION of a value: return slot, fresh local, memory, parameter. `(void)x;` on a struct is deliberately NOT one — it has no destination and the certificate emits no row for it. `zaehle-kette.py` passes the same body context, and its speech test plants all four rows **in both directions**: the three aggregate statements must be uncovered AND the scalar `return p.id;` of the same unit must stay `stmt:return-expr`/lemma |
| **what the extension would gain, MEASURED** | **ZERO of 113 corpus programs.** Not a first-refusal count: a probe in which the four rows carry a lemma name — *the obstacle removed* — was put in place and the whole 113-program chain sweep re-run (`.claude/kratz-agg/sonde-lauf.sh`, tree restored, SHA-256 identical). Sieve totals honest vs obstacle-removed: **(b) 15 / 15, (c) 15 / 15, (d) 55 / 60, (e) 2 / 2**. Of the **15 programs that export**, **not one** fails sieve (d) on aggregates alone: `120-tagged-construction` fails on `expr:union-payload`, `stmt:decl-union-payload` and `stmt:switch-tag` besides — the tagged-union READ side, uncovered since 2026-09-13 for its own reason. Over the whole corpus exactly **5** programs have the aggregate as their only (d) obstacle (`80`, `94`, `95`, `100`, `101`), and every one of them is stopped **two sieves earlier**, at (b), by something else: `LG001 assume … has no G form` / `requires profile has no G form` (100, 101) and `LG001 function … is not \`impl\`` (80, 94, 95) |
| **why it is refused and not merely postponed** | *a model extension that pays for nothing is worse than a named absence* — the rule `O15` was decided under, applied to the C side this time. Carrying an aggregate means a `CTy`/`CVal` that is no longer flat, a memory that stores composites, an ABI decision for the struct return, a `korrOk` arm per destination with a planted defect each, and `korrOk_fnCorr` re-proved sound. **The chain count could not move either way**: sieve (a) passes 2 (`104`, `108`), both of them aggregate-free, and coverage is multiplicative |
| **what pays FIRST, measured on the same run** | the **tagged-union READ side** — `switch (m.marke)`, `m.last.F`, `T x = m.last.F;` — which is what actually holds `120`, `121` and `34`, the three exporting programs that fail (d) on something other than `expr:neg`. All three carry the aggregate rows too, so the read side is necessary and the aggregate side is not sufficient; but the read side is the binding one, and `gcorr_onTag` is already PROVED and merely uninhabitable (`ValCorr` has no case for a tagged union) |
| **what would close it** | `CTy`/`CVal` gain an aggregate arm, the memory of `CSpeicher.lean` stores it (or `RecLay` + `CX.fld` carry it as the `nf` field stores and loads it really is — the machinery exists), `CFormen*`'s return and bind lemmas gain their arm, `korrOk` gains one arm per destination with a planted defect per arm, and the four `KNOWN_UNCOVERED` rows dated 2026-09-15 in `pruefe-cformen.py` move to state (i). **And the warrant is then a re-measured sweep, not this row** |

## O17 — Per-core writes are admitted by the checker and unmodeled in Lean (known since lane 245, 2026-09-17; NARROWED 2026-09-26, Opus agent B: the write half is covered, the read half is O25; NARROWED again 2026-09-26, Opus lane O25: the read half's memory side is proved, its contract side is O25)

**Narrowed again (Opus lane O25, 2026-09-26, SATZKARTE §52).** The fold -- a pool writing the
atomic accumulator, another start reading it -- is refused by the goal's checker at `fuss` and
ACCEPTED by `AkzeptiertA`, the checker with the atomic exemption (`faltung_abgelehnt`,
`faltung_akzeptiertA`, `Speichermodell/AtomarZeuge.lean`). On every program `AkzeptiertA` accepts,
machine W reads the plain carriers sequentially consistently and answers the atomic reads per W
(`schwach_ist_gA`), and the language-carried legs hold at every machine W reaches: trace
invariant, lock exclusivity, no deadlock, no wait cycle, time, race freedom of plain carriers
(`w_sprache_akzeptiertA`). What stays open is the CONTRACT side (the user's proof against every
value the fold may read: the rely of O25) and, as before, the exporter (`LG001` for `accumulates`)
and "each thread its own cell" (a core per thread, O19). The "lost update" of a real
`accumulates` update (load, then store) is exactly what `zaehler_verloren`
(`Speichermodell/Zaehler.lean`) shows W admits; the emitter's cells are relaxed atomics with
separate load and store, so a lost update is a behaviour of the C too -- the user's merge
discipline at quiescent points, as the emitter's comment says, not a theorem.

**Narrowed (Opus agent B, 2026-09-26, SATZKARTE §50).** The emitter lowers `accumulates X per cpu N`
to `static _Atomic T X_zellen[N]` with relaxed loads and stores, so in the model a per-core
accumulator IS a relaxed atomic global, and the weak machine W (`Speichermodell/`) says what the
cells do: writes from any number of threads take distinct timestamps of one modification order
(`Frisch`), and a read never goes back behind the reader's view (`schrittW_kohaerent`, read
coherence; write-write coherence is not stated as a theorem). The N cells are read as ONE
location, so "the write half is covered" means a pool that only WRITES the accumulator -- no
real `accumulates` update, which loads its cell first (review 2026-09-26).
Under that reading the Rust pool rule with its per-core disjunct IS the Lean one
(`poolSicherRust_iff`: "per-core" becomes "atomic" in `PoolSicher`), and a pool whose instances
all WRITE one relaxed atomic is accepted by the checker Bool (`proKern_schreiben_akzeptiert`) and
covered by `gabbro_ziel` including the weak-memory leg `schwach`. What stays open is the READ half,
and it is not per-core specific: every `accumulates` update loads its own cell before it stores,
and the fold reads every cell -- a read of a carrier other threads write. The Lean footprint
component refuses that (`proKern_lesen_abgelehnt`), the Rust `N300`/`N301`/`N304` exempt it ("one
cell per core -- nothing shared"). That read is OFFEN O25 (a rely for unguarded atomic reads);
modelling "each thread its own cell" would additionally need a core per thread in G (pinning,
O19). The exporter still refuses `accumulates` (`LG001`), so no per-core unit reaches (a) either
way. The record below is kept as written.


`fusswache2.rs::per_core` exempts `accumulates … per cpu` carriers
("one surface name denotes N distinct carriers", same rationale as
`H013`, `N300`/`N301`); lane 245's narrowed `N304` admits them in pools
too. The Lean `PoolSicher` covers guarded-or-atomic only and states the
gap openly (`PoolSym.lean`: "the model has no notion for it").

| | |
|---|---|
| **why this is not a soundness gap in the goal** | the exporter refuses `accumulates` items outright (`lean_g.rs` LG-table: generates none), so per-core programs never reach premise (a) — same standing as every checked-but-unexported program. Unguarded sharing still refuses (`N304`, gift `1097`). Memory safety holds regardless: the cells are `_Atomic`, so the worst case is lost updates (user-logic merge discipline at quiescent points, per the emitter's own comment), never a data race. |
| **what stays open** | the locality notion itself (per-thread disjointness under migration without pinning) and, on the checker side, whether `|| core` should narrow the way 208 narrowed vacuous rules. No lane is tasked with it yet: wave B of `TODO.md` §-1 (lanes 227–235, 252) has no such row, although this entry and `TODO.md` §4 said so until 2026-09-21 (review G13). The choice stays: model per-core or restrict the exemption. |
| **what would close it** | a `PoolSicher` disjunct with a disjointness proof over thread identity (or the pinning the runtime does not do today), plus the exporter covering `accumulates` so the bridge `einzelnPoolB ↔ EinzelnPool` ranges over it. |

## O18 — A busy start that runs twice is admitted by the Rust checker and covered by no theorem (known since lane 245, 2026-09-17; recorded 2026-09-21, reviews G06/G13) — CLOSED 2026-09-22 by fix lane F10

**Closed.** `Spec.lean` was changed as a reviewed diff (header "WHAT CHANGED ON 2026-09-22"):
`AkzeptiertSpec.einzeln` is `EinzelnPool` (a routine declared twice, `Mehrfach`, is pool-safe),
`Getrennt` pairs start occurrences, and `Laufzeit.einmal` lets a routine declared twice run on
several threads. `gabbro_ziel` is re-proved with the same statement text and the standard three
axioms; the only proof changes are `getrenntK_of`/`schreibGetrenntK_of`
(`Zielsatz/Akzeptiert.lean`). Nothing is weakened: both premise changes are relaxations, and on
distinct starts the Bool is the old one (`akzeptiert_nodup_gleich`, `akzeptiertSpecVor_neu`,
`pruefer_vor_neu`, `laufzeit_vor_neu`, `Zielsatz/PoolSym.lean`). Witnesses: `pool_ziel_zeuge`
(two instances of a lock-guarded writer, accepted, both stepped, `Ziel`) and `pool_abgelehnt`
(an unguarded writer twice, refused by the pool component alone), `Zielsatz/PoolZeuge.lean`;
SATZKARTE §47. Rust: `N304` decides the same condition on the exported fragment, the idle
refusal `N315` is retired (gift 976 removed), and the exporter's `LG001` for repeated starts is
lifted (`beispiele/157-worker-pool.gab` exports and agrees, `pruefe-akzeptiert-diff.py`). What
stays open is O17 (per-core). The record below is kept as written.


Lane 245 narrowed `N304`: `concurrent { arbeiter, arbeiter }` passes when `arbeiter` is
pool-safe (every carrier it writes is guarded, atomic or per-core), and `N315` refuses only an
*idle* duplicate (`fusswache2.rs`). The goal theorem does not follow:

- the Lean checker Bool still demands `einzelnB ws` (`ws.Nodup`, `Zielsatz/Akzeptiert.lean`), so
  `gabbro_ziel` says nothing about such a program;
- `Spec.lean`'s NOT-CLAIMED list names it ("one thread per busy start ... outside (d)");
- `PoolSym.lean` proves a separation lemma and a lock-exclusivity bridge, not `RennfreiBis`,
  deadlock freedom or the lock-invariant legs over a start multiset.

| | |
|---|---|
| **why it is recorded and not refused** | Simon's threading MUST (`TODO.md` §0); the pool rule reads race-free informally (every written carrier needs its lock, H007), but that is an argument, not a theorem. O17 is the per-core half of the same gap |
| **known side effects** | **fixed in fix lane F4 (2026-09-22):** the generated driver (`bau.rs` `treiberregel`, lane 246) de-duplicated `concurrent` names, so an accepted pool started ONE thread (review G06 F5) -- it now starts one thread per occurrence and the pin compares multisets (`tests/treiber.rs` `pool_zweimal_deklariert_laeuft_zweifach`: built, compiled, run on two threads); `lean_g.rs` `check_starts` had no refusal for a repeated start, and a pool unit DID export (measured: `starts := [⟨g_arbeiter, .nil⟩, ⟨g_arbeiter, .nil⟩]`, G06 F3) -- it now refuses by name (`LG001`), so no pool unit is exported as if the goal covered it. The Rust acceptance itself is unchanged (not gated): that is this item |
| **what would close it** | the `einzeln` → `EinzelnPool` swap in `Akzeptiert` with `RennfreiBis`, `KeinWarteZyklus` and the invariant legs proved over start multisets and a `Spec.lean` diff for (d), reviewed as such (Simon, 2026-09-21: this route; fix lane F10). The exporter's `LG001` for repeated starts goes with it |

## O19 — Handlers and cores are not in the unit: the preemption leg carries them itself (recorded 2026-09-21, reviews G02/G12/G13; NARROWED 2026-09-22, fix lane F11)

An `entry … vector … via idt` dispatch root travels into the model as an ordinary start
(`lean_g.rs` `check_starts`; `Spec.lean`: "`entry`/`boot` dispatch roots"). Since lane 255 the
exporter carries `masks irqs` as `D.maskiert`, but nothing in `Zielsatz/` or `Akzeptiert` reads
it (its only uses there are `fun _ => false` fixtures). In the model the handler is an
independent thread, so "no deadlock / `KeinWarteZyklus`" holds even when the handler, on the
core it interrupted, spins on a lock that core's thread holds unmasked.

| | |
|---|---|
| **who guards it today** | the Rust checker alone (`H102`, `kontexte.rs`); the emitter lowers no `cli`/`sti` (`beispiele/59` says so in its header) |
| **why it matters** | `beispiele/59` exports since lane 255, and its exported deadlock freedom reads like interrupt-deadlock freedom; it is not. a model of `gift/460` (refused by `H102`) would differ from `Korpus59.lean` only in `kMaskiert`, and would get the same `Akzeptiert = true` and the same `korpus59_ziel` (review G02 F1) |
| **what would close it** | either a NOT-CLAIMED line in the `Spec.lean` header (dispatch roots are modelled as independent starts; same-core preemption and `D.maskiert` are not read by `Ziel`; `H102` is the only guard), or a `MaskenOrdnung` leg carried into `Laufzeit`. Both are `Spec.lean` diffs for Simon |

**What fix lane F11 did (2026-09-22), and what is left.** Simon decided for real coverage, so
`Ziel` gained the leg `keinKernHalt` (`KernHaltG`, Spec.lean; proved in
`Zielsatz/Masken.lean`, witnessed in `Zielsatz/MaskenZeuge.lean`, SATZKARTE §48): on a run
that a core schedule admits — a handler enters only where no thread of its core holds a masked
lock, and runs to completion before that thread continues — a handler never stands at a lock a
thread of its core holds. `D.maskiert` is read by the goal theorem since then, and the
`gift/460` shape is refused by the discipline Bool `maskenDisziplinB`, which is `H102`.

WHAT IS LEFT, and why it is a lane of its own:

* `Einheit` does not say WHICH declared start is a handler (the exporter drops `via idt`) and
  G has no cores, so `kern`, `H`, the call graphs and the masking discipline are HYPOTHESES of
  the leg, not components of (a) or fields of (d). Closing that needs a field in `Einheit`, a
  core in the machine, and `lean_g.rs` carrying the dispatch fact.
* The C realises no masking: the emitter writes no `cli`/`sti`, so the translation-validation
  chain has nothing to relate the model's `KernPlan` to. Named in `Spec.lean`'s NOT CLAIMED.
* The leg constrains the handler's FIRST entry; re-entry of the same handler thread and
  handler-on-handler preemption stay outside (in G a handler thread runs once).
* Rust's `H102` skips locks the unit does not declare, and fires only on `via idt`
  (`beispiele/57`'s IPI is silent) — both already named in `kontexte.rs`.

## O20 — Arena generations and the commit ceiling assume one thread of control and roots entered once (recorded 2026-09-21, review G08, fix lane F2)

Fix lane F2 made both arena facts whole-program: `N211` applies a callee's (transitive)
`reset`s at every call and `start`, holds parameter indices to the entry generation and
refuses untracked carriers where the arena is reset anywhere; `N426` holds every `grow`
against the upper bound of the whole run's commit. Two assumptions remain, and neither is
checked:

| | |
|---|---|---|
| **generations along one thread** | a `reset` of `A` in a routine that runs CONCURRENTLY with the holder of an index into `A` (another root of a `concurrent` set, a `child` path, an interrupt handler) is not applied to that index. Memory safety does not depend on it (the index stays below `committed`); the residue is a logical dangling reference |
| **roots entered once per load** | the commit total sums call-graph roots once (a `concurrent` body once per naming, an `entry` dispatch target without bound). A routine entered again by code the unit does not see (a separately linked caller, NOT CLAIMED in `Spec.lean`) can still reach the runtime's past-ceiling stop (`abort`, `laufzeit/arena_dyn.c`) |
| **the emitted counters are plain words (lane 259, emitter arm)** | a dynamic arena lowers `used`/`committed` to ordinary `uint32_t` fields and `alloc`/`grow` to unsynchronised read-modify-writes -- two threads allocating (or growing) on one arena race in C, and no rule demands a lock or an atomic there. Memory safety does not depend on it (a raced check-then-use still names a slot below `committed`: the check passed on a smaller `used`, and `grow` only ever raises the ceiling side); the residue is logical -- duplicate indices, a lost cursor step, growth one thread never sees. No concurrency safety is claimed for the lowering, and none is built |
| **what would close it** | for the first: a `reset` in any routine that may run concurrently with a reader of `A` consumes every generation of `A` program-wide (cheap, strict), or arenas refused as shared carriers across threads; for the second: a Spec-level statement of the run model (declared starts, each once) naming the ceiling, reviewed as a `Spec.lean` diff; for the third: the same strict option (no arena shared across threads), or atomic counters with a model leg that carries them |

**Closed 2026-09-26 (lane 264, `arena_faden.rs`, gifts 1272-1280, `paesse.rs`
`arena_reset_*` / `arena_zaehler_*` / `arena_commit_*`).** The entry's strict
options were taken, all three from the checker side, no emitter change (the
plain words stay; `MARKE_EMIT` unmoved):

| | |
|---|---|
| **generations across threads: `N521`** | the refusal option, not generation consumption: a `reset` of `A` in a routine that may run concurrently with a use of `A` (another `concurrent` member -- a routine named twice against itself -- an `entry`/`boot` target, a `start` root, a `child` region; each closed over calls, indirect calls as the whole pool) is refused with no lock exemption. Consumption was rejected because a lock serializes the counter but cannot revive a consumed generation -- the admitted shape would still hand the holder a stale slot. `child` regions always double with `N457` (its guard disjunct is vacuous for arenas, measured: `sperrdaten` resolves no arena `protects`); `start` roots fall here alone (`N462` resolves no arena `writes` -- its carriers are tables -- so a sharing start root beside a member was nobody's refusal). |
| **roots entered more than once: counted, no code** | the hole does not reproduce on this tree: a `concurrent` body counts once per naming, an `entry` target without bound, and a started root once per execution of its statement (sequentially repeated, loop-multiplied, unbounded where the loop is) on top of the share the starter's bound already carries -- pinned by gifts 1279 (pool commits twice), 1280 (a looped `start` multiplies) and the `arena_commit_*` twins (repeated starts, the single execution clean). No `arena.rs` change; the sentence (`arena.wachsen_commit`) names the executions now. |
| **the emitted counters: `N522`** | the refusal option: `alloc` against `alloc`, `alloc` against `grow`, `grow` against `grow` across two concurrently running routines (members, pool self-pairs, `entry`/`boot` targets, `start` roots; `child` regions stay `N457`'s) without one lock protecting the arena held at every counter site is refused. Held counts as `H007` counts it (`locks` block, `effects` line, signature; never `shared`); the `protects` map is read module-resolved beside `sperrdaten`, which neither rule is weakened by. Atomics were rejected: an atomic cursor still loses the check-then-act past the committed prefix, a concurrent `reset` beside it stays `N521`, and the weak-memory leg over atomics is another lane's (Opus O25b). |
| **what stays open** | an `entry` target against plain pre-thread boot code (handlers pair with threads only); the `effects`-line exemption shared with `H007` (a declared-but-never-taken line exempts here exactly where `H007` stays silent); `H007` still owns arena READS while counter statements are this pass's; every region `N521` doubles with `N457` (above). |


## O21 — The `child` thread exists in the checker, not in the model, and its code between gate call and region is unchecked for the child (recorded 2026-09-21, review G11, fix lane F3)

Fix lane F3 made the `child` path a thread for the Rust checker: `N456` (no child under a
held context), `N457` (every carrier the region or its callees touch that anyone writes is
guarded, atomic or per-core), held-set walkers reset at `child`, `N450` one dominating gate
call per region, and an exhaustive spill read set. What stays open:

| | |
|---|---|
| **the child in the model, not in the goal** | fix lane F9: `CloneHandoff.lean` has the child as a thread (a dormant slot spawned by a live parent, then stepping by machine G's rules; every clone run is a G run). `GabbroZiel` still has no child: a child reaches `Ziel` only through `klon_ziel`, when the unit lists the child entry as a declared start and is accepted. Not modelled: the child's arguments and entry world at the SPAWN (they are fixed at the start), and repeated spawns of one gate (one slot, one spawn). `N456` has its model side (`klon_kind_haelt_nichts`: a child with no signature lock holds nothing at the spawn and never blocks); `N457` has a stated correspondence only (the child judged like a start), no proof that N457 implies Lean acceptance. `N456`/`N457` stay fail-safe (a carrier written only before the gate call still counts as written, a child that is the only writer still falls) |
| **the jump assumption** | the checker judges the REGION only; the statements between the gate call and the region are checked as parent code. Sound only if the lowering enters the child by jump at the region. Written into PLAN-SYSCALL, the `klon.uebergabe` sentence and `C185`'s message, pinned by `tests/klon_faden.rs`. Lane 260 landed it for the narrow triple (gate+`if v == 0`-guard+sole region, top-level): the gate call is an inline `syscall` jumping straight to the region label in the child, the in-between code runs parent-side only, and no new checker rule was owed (the gap is vacuous by construction). The stub correspondence lemma for the jump lowering is still open (see below); the C-form census books the region label as `stmt:label-kind` (known-uncovered) |
| **other flow facts** | held sets are reset or empty at a `child` (`N456`); other facts walkers carry down through `crate::unterbloecke` (M1 value ranges of guarded globals, phases, pairing state) were not re-audited for the child. Arena counters are moot: `N457` refuses a child touching an unguarded arena anyone writes, which also closes the `child` half of O20's first row |
| **what would close it** | spawn-time arguments and entry world in the clone machine, unboundedly many children per gate, the exporter emitting `child` units with the child entry as a start (and a proof that `N457` gives Lean acceptance), and the stub correspondence lemma for the jump lowering |

**Narrowed 2026-09-26 (Opus agent A, SATZKARTE §49).** The child is now IN THE GOAL at the MODEL level (a region given
as a function root in `gestartet`; no `child` program exports yet, see the table below):
`GabbroZiel` runs over the thread machine (FadenMaschine.lean), whose `kind` step spawns a
dormant slot of a run-time root (`Einheit.gestartet`) while the parent goes on; every leg of
`ZielF` holds on every such run (`gabbro_ziel`, witnesses `kw2_lauf`, `spawn_kind_ziel`), a
spawned thread enters holding nothing (`schlafendFrei`), and F9's clone machine is a special
case (`klon_als_faden`). Unboundedly many children per gate are covered: a root in `gestartet`
stands twice in `ws`, is judged as a pool routine, and may run on any number of slots. The model
half of `N456`/`N457` is now a Lean Bool fact (`wurzelnB`, `einzelnPoolB` over the doubled root;
`akzeptiertSpec_gestartet`, refusal `kind_unter_sperre_abgelehnt`). What stays open:

| | |
|---|---|
| **spawn-time arguments and entry world** | a slot's arguments are the unit's, fixed at the start machine, and its frame's ghost entry world is the start world (named assumption (d) in Spec.lean). A region reading its handed values (the stack argument, the gate answer) has per-spawn arguments -- not covered |
| **no export** | a `child` needs a stack gate, a foreign body the exporter does not build (`Ax := Empty`); no `child` program reaches Lean, so `N457` => Lean acceptance is stated, not measured |
| **the jump assumption** | unchanged (above): the lowering must enter the child by jump at the region with an empty held set; lane 260's `clone` lowering and translation validation own it |

## O22 — The hosted `start { … };` is checked, not modelled and not lowered (recorded 2026-09-22, review G12, fix lane F4)

Fix lane F4 gave the statement checker rules: the roots are call-graph edges (their effects
meet the starter's, `E008`), the statement costs the sum of the roots' declared costs plus two
per root, and `N458` (root shape), `N459` (duplicate root), `N460` (one owner per thread: no
`concurrent` member, `entry` root or `boot` dispatch is started by the statement), `N461` (no
`start` under `locks`/`observes`/`breaking`/`requires Held`) and `N462` (a started root is
pool-safe) refuse. What stays open:

| | |
|---|---|
| **no model** | `Akzeptiert`/`Ziel` know only `E.starts` from the declaration. A started root is in no declared pair; `N462` is the fail-safe substitute (the pool-safe shape `N457` gives a child), a checker rule with no Lean counterpart |
| **no lowering, no export** | the emitter lowers the statement since lane 260 (one raw-clone spawn per root on unit-owned stacks via `laufzeit/faden.c`, joined before the starter proceeds; `beispiele/159` emitted and run); the exporter still refuses it (`LG004`, the model lane's); no `start` program reaches Lean |
| **strictness** | `N461` refuses any held context (not only a lock some root takes); `N462` refuses a root that is the only writer of an unguarded carrier; the cost bill is the sum (sound on one core), not the maximum |
| **liveness** | a root that never returns keeps its starter waiting forever; progress over statement-level starts is not decided |
| **what would close it** | a statement-level spawn/join rule in machine G with the race component quantifying over started roots, then the driver-side lowering (one create per root, join before the next statement) |

**Model closed 2026-09-26 (Opus agent A, SATZKARTE §49).** The rows "no model" and the export
half of "no lowering, no export" are closed: the goal theorem runs over the thread machine, whose
`start` step spawns the roots (only where the starter holds no lock -- `N461` as the step's side
condition) and whose `join` step lets the starter go on only once every root has finished; the
roots are `Einheit.gestartet`, judged by the Lean Bool as pool routines (`N458`'s lock half is
`wurzelnB`, `N462`'s model half is `einzelnPoolB` -- `N462` bounds touched carriers,
`einzelnPoolB` written ones); join waits are in the deadlock and wait-cycle legs
(`keine_verklemmungF`, `kein_warteZyklusF`) and named in progress (`JoinWartet`). The exporter
carries the roots (`gE.gestartet`, `check_gestartet`), and `pruefe-akzeptiert-diff.py` compares
the verdicts (`messung/proben/faden-start-pool.gab`). What stays open: the LOWERING (lane 260),
the strictness row above, and liveness (a root that never finishes keeps its starter waiting: a
named stop, not a claim). A root's `requires` is the user's duty at the declared initial memory,
not at the spawn world (named assumption (d)).

## O23 — A gate's argument preconditions are named, not modelled in the goal: the NUL path and the frame length (recorded 2026-09-22, reviews G04/G10, fix lane F5)

Fix lane F5 repaired example 149's `open` gate (the register map is now Linux x86_64
`open(path, flags, mode)`; measured on the emitted C) and gave the fd gates their own named
assumptions and probes (`linux_open_contract`/`sonde_open`, `linux_read_contract`/`sonde_read`).
The frame length is now DECIDED: a `syscall` byte buffer carries `requires x <= lenof(p)`
(`N464`), and every call decides it (`N463`). What stays open:

| | |
|---|---|
| **the NUL-terminated path is a named CALLER assumption, not a checked fact** | `beispiele/149` states it as `spec fn path_nul_terminated(path, pathlen)`, the gate `requires` it, and `gabbro obligations` counts it as a `V` obligation at every call. The checker does not decide it (no rule reads a byte's value), so a program that does not discharge it by its own logic calls `open` with a frame the kernel may read past |
| **the goal's premise (c) quantifies over every argument** | `AxVertragO` (`AxiomVertrag.lean`) has no argument precondition. `FremdRuf.lean` §9 proves the split (`AxVertragOP` + `AufruferPflicht`) and a bridge back to `HardwareAnnahmen` for a re-dressed oracle that agrees with the machine's on every well-formed call; `Spec.lean` is unchanged, and run-level coincidence under the caller obligation is not proved. No exporter produces a gate precondition (149/150 do not export: `LG001`/`LG002`) |
| **`N464` holds `syscall` buffers only** | an `extern fn` taking a byte pointer and a length (`beispiele/64`'s `write`) is not held to the clause; `N463` decides the clause wherever it is written, but nothing demands it there |
| **`lenof` of a pointer is decided only where an array decays** | along a forwarding chain it is the caller's own promise, carried by the same clause; a pointer out of a field or a computation cannot answer (refused, fail-closed) |
| **what would close it** | an `AxPre` field in the declaration exported from each gate's `requires`, the caller obligation in `NutzerPflicht`, and the run-coincidence theorem that lets premise (c) drop to well-formed calls |

> **STATUS 2026-09-26 (lane 262): narrowed on all four rows, closed on none.**
> `N506` holds `extern fn` byte buffers with a length parameter to the same
> `requires x <= lenof(p)` clause `N464` demands at `syscall` gates
> (`beispiele/64` tightened, no other accepted program falls). `N507` decides
> the NUL obligation where the program builds the buffer -- a proved
> `buf[L-1] = 0` store, an untouched zeroed buffer, or forwarding under the
> caller's own clause; unseen pointers keep the named `V`. Example 96's write
> gate says `reads buf` (the `pure` fiction fixed, callers carry
> `reads WINDOW`); gifts 1067/1068 name the read assumption. In Lean,
> `FremdRuf.lean` §10 lifts the bridge from one call to call sequences at the
> oracle layer (`mitVorbedingung_folge_gleich`); machine-level runs through
> `bindAxiom`, the `AxPre` export and the fixture widening stay open (CUTS).
> What remains of each row: the NUL for unseen pointers (still `V`-only); the
> run coincidence above the oracle layer; `lenof` of a pointer decided only
> where an array decays.

## O24 — Bounded strings are checked, not represented: NUL, the upper limit on `max`, aggregates (recorded 2026-09-22, review G12, fix lane F6)

Fix lane F6 made the checker agree with the Lean value model
(`ZeichenfolgeGebunden.lean`): an index is proven against the length by a flow fact
(`N454`), a string stands only in parameters, results and `let`s (`N465`), and the name
table is scoped. Lane 261 (2026-09-26) closed the representation, the limit and the
literals; what stays open is narrower:

| | |
|---|---|
| **representation: CLOSED** | `gabbro_string_N`: one `uint32_t` length word plus `max` bytes, no NUL terminator (`emit.rs` `ketten_abschnitt`); `lenof` is `.len`, the index `.data[k]`, copies plain or widening helpers, `+` a concat helper at the summed max, comparisons two generic byte helpers. `ZeichenfolgeC.lean` states the operation correspondence over the live prefix |
| **upper limit on `max`: CLOSED** | `1 ..= 65535` (`N486`, `zeichenfolge.schranke`); zero has no object form, more no stack frame |
| **literals: CLOSED** | `"hi"` parses (`ExprArt::Kette`, UTF-8 bytes, length is the byte count), the checker holds the count against the slot exactly, the slot writes a compound literal at its own max |
| **no strings in aggregates or constants** | still refused by `N465` (a deliberate cut, not a model): fields, table slots, `const`/`static`, arrays, variants, pointers, fn pointers, `syscall` heads. The layout COULD carry them now; length facts still cannot reach them |
| **max-bound over-approximation** | still open: `+` and copies compare maxes; `bconcat_max_summe`/`bkopie_max` prove this sound, not complete -- a copy whose actual length would fit is refused |
| **no Char bridge** | still open: the layout carries bytes, `BString` carries characters; `ZeichenfolgeC.lean` states the gap beside its lemmas, and no `CForm` plugs into the correspondence framework |
| **what would close the rest** | flow facts for aggregate positions (a bigger checker), exact-length copies (a bigger analysis), a verified UTF-8 bridge plus a `CForm` hook (a bigger model) |

## O25 — Programs that RELY on an unguarded atomic read across threads are refused by the Lean checker, and the goal says nothing about W's non-SC outcomes (recorded 2026-09-26, Opus agent B; NARROWED 2026-09-26, Opus lane O25: the memory half and the language-carried legs are proved, the contract legs are open)

**Narrowed (Opus lane O25, 2026-09-26, SATZKARTE §52; `messung/OPUS-O25-ATOMICS.md`).** Proved,
standalone (no Spec diff, `GabbroZiel` still runs `Akzeptiert`):

| | |
|---|---|
| **the memory half** | with the footprint property exempting ATOMIC carriers only (`FussSA`, Bool `fussWAB`, checker `AkzeptiertA`; every program `Akzeptiert` accepts is accepted, `akzeptiertA_of_akzeptiert`), every W step is a step of machine GA -- G on a memory that agrees with G's at every NON-atomic carrier, the atomic reads answered per W (`schwach_ist_gA`, `ga_aus_w`). Plain carriers stay sequentially consistent; atomics are coherent (`schrittW_kohaerent`) and release/acquire hands views on (`hb_uebergabe`: after an acquire read of `t`'s release message, every read of `u` at any other carrier is at or above `t`'s view before the release) |
| **the language-carried legs** | on a program `AkzeptiertA` accepts, at every machine W reaches: `SpurInv`, lock exclusivity, no global deadlock, no wait cycle, `ZeitAb`; race freedom for every non-atomic carrier on every W run (`w_sprache_akzeptiertA`) |
| **witnesses** | the flag (configuration 1: refused by `Akzeptiert`, accepted by `AkzeptiertA`; W's stale read `w_nicht_sc` happens there and is a GA step, `n1_nicht_sc_aber_ga`; `SchwachSC` is false there, `n1_schwachSC_falsch`); the per-core fold (`faltung_akzeptiertA`); the refusal of a plain payload read with no synchronisation (`nutzlast_ohne_erwerb_abgelehnt`); the relaxed `fetch_add` counter is 2 on an atomic-RMW view machine (`zaehler_zwei`) |

**What stays open -- and why no Spec diff was made:**

| | |
|---|---|
| **the contract legs** | `vertrag`, `sperrInv`, `invRueck`, `invGrund`, `startEnde`, `keinStartGrund`, `keinLogikHalt`, `fortschritt` come from the replay of the user's sequential proof (`execEndH`, `KoerperGutS`) into G (`ziel_ort_mehrfaden_ende` and around, the `ZielOrt*`/`Sperre*` family, about 30 000 lines). The replay keeps the sequential world equal to the machine's on the STABLE carriers; a racing atomic is not stable, and a GA step reads a value the sequential world does not have. Needed: `execEndH` answers a read of a shared atomic with ANY value of its type (a havoc at the read, next to the one `Umwelt` makes at a lock take), `KoerperGutS` over it, and every residue lemma of the replay carrying it. Until then a `GabbroZiel` over `AkzeptiertA` would lose the contract legs, so the goal keeps `Akzeptiert` |
| **the leg `schwach` in GA form** | on `AkzeptiertA` programs `SchwachSC` is false (`n1_schwachSC_falsch`); the Spec diff would replace it by "every W step is a GA step with plain carriers SC" (`schwach_ist_gA`), reviewed as a diff of `Spec.lean` together with the rely |
| **RMW atomicity in W** | W's step lets an `exchange` read one message and write at any fresh timestamp, so a `fetch_add` counter can lose an update in W (`zaehler_verloren`) although RC11 forbids it; the fix is the adjacency of `ZSchritt` (write at the read message's timestamp + 1) in `SchrittW` for a step that reads and writes one atomic -- a change of the machine Spec imports (a smaller W: every claim over W stays, `w_aus_g` must be re-checked) |
| **the payload hand-off to a PLAIN carrier** | the view transfer is proved (`hb_uebergabe`); a footprint rule admitting a plain payload read that follows an `awaits` of its atomic (and a producer that writes it only before the `publishes`) is not, so `publishes { p }` with plain `p` read across threads stays refused, as in P3 |
| **the exporter** | refuses every `atomic` item (`LG001`), so no racing-atomic unit reaches Lean; the Rust footprint legs never counted atomics (on this component Rust decides `fussWAB`, measured on `messung/proben/o25-flagge-atomar.gab`) |

Since 2026-09-26 the goal theorem is proved over the weak machine W (`Speichermodell/`,
SATZKARTE §50): the leg `schwach` of `Ziel` says that on an accepted program W takes only G's
steps, for every assignment of memory orders, and `gabbro_ziel_schwach` gives every leg at every
machine W reaches. That is the DRF theorem, and it holds BECAUSE the footprint component `fuss`
demands that every carrier a thread's graph reads is thread-local or lock-guarded -- `atomic` or
not. So:

| | |
|---|---|
| **what is not covered** | a program in which one start WRITES an atomic (a flag, a counter, a per-core cell) and another start READS it without a lock: message passing through `publishes`/`awaits`, a spin on a flag, a statistics counter read by a monitor thread. `fuss` refuses it (`fuss_n1_abgelehnt`); the Rust checker accepts it (the atomic is exempt from `H013`/`N300`/`N301`); the exporter refuses every `atomic` item (`LG001`). W's non-SC outcomes (`mp_rlx_erlaubt`, `sb_erlaubt`, `w_nicht_sc`) occur only on such programs, so no accepted program shows them and no theorem here speaks about them |
| **why it is not a soundness gap** | the Lean Bool is STRICTER than the Rust checker here: a program it refuses reaches no premise (a) of `GabbroZiel`. What is missing is coverage, not correctness |
| **what would close it** | a RELY for atomic reads in the user's sequential semantics: `execEndH` (SperreSem.lean) answers a read of a shared unguarded atomic with an ARBITRARY value of its type (a havoc at the read, as `Umwelt` does at lock moves), `fuss` exempts atomic carriers from locality, and the replay (`ziel_ort_mehrfaden_ende` and its family) carries the havoc. The user's proof then covers every value W can return -- relaxed and non-SC included -- and `schwach` is no longer needed for those carriers; coherence (`schrittW_kohaerent`) and release/acquire (`schrittW_erwerb`) are already facts of W for every program. Payload hand-off (`publishes { p }`, P3) needs more: the payload read is covered only through the acquire's view, i.e. a rely conditioned on `awaits` |
| **who guards it today** | the Rust checker alone (atomics exempt from the race rules), the emitter's explicit orders (lane 152), and `V001`-`V005` for payload pairing |

## O26 — An own lock primitive (`N323`) is not checked for memory orders, and the weak-memory leg assumes every lock primitive is acquire/release (recorded 2026-09-26, Spec-diff verdict of Opus agent B, F2; CLOSED for own primitives 2026-09-26, Opus lane O25: `N481`-`N483`; foreign primitives stay assumed)

**Closed for own primitives (Opus lane O25, 2026-09-26, SATZKARTE §52).**
`namen.rs::sperrprimitiv_ordnung`, sentence `namen.sperrprimitiv_ordnung`, over the ORDERED
atomics (declared `acquire`, `release` or `seq`, lowered acquire / release / acq_rel):
`N481` refuses a take (`L_nimm`, `L_nimm_geteilt`) that reads atomics but no ordered one, `N482`
a give that writes atomics but no ordered one, `N483` a bodied take and give of one lock that
release and acquire on different ordered atomics (no synchronises-with edge). Poison probes
`beispiele/gift/1201` (a relaxed test-and-set spinlock: `N481` and `N482`), `1202`, `1203`;
positive: snippet tests `geordneter_spinlock_besteht` and `ticket_sperre_besteht` (the runtime's
ticket lock shape of `laufzeit/sperre.gab` beside `lock TOR`). Corpus diff: only the three gifts.
Measured the same day: `N042` refuses the C name of EVERY own or foreign `L_nimm`/`L_gib` beside
`lock L`, so no accepted program has a non-driver lock primitive today; these rules are the order
half of the contract for the day that name opens. What stays: foreign primitives (`extern fn`,
`asm`) are assumed; that the acquiring read is the one that SEES the release (the spin on the
right word) is `N323`'s shape, not a flow fact; the lowering of the orders is assumption (2).
`Spec.lean`'s assumption (3) says so (a comment-only header correction). The record below is
kept as written.

The DRF argument of the leg `schwach` (SATZKARTE §50) transfers to the C only if every
`<L>_nimm` is an acquire and every `<L>_gib` a release. `Spec.lean` names this as assumption (3)
of the reading, for EVERY lock primitive:

| | |
|---|---|
| **driver-defined locks** | `pthread_mutex_lock`/`_unlock` in the generated driver (`treiber.rs`): acquire/release by POSIX. Holds |
| **own primitives** | a bodied `<L>_nimm`/`<L>_gib` over a declared atomic, `N323` (`namen.rs:147`, `LockGiltAn`). `N323` checks atomicity, that the body reads an atomic, and hold time -- NOT the memory orders. A spinlock with relaxed loads and stores passes `N323` and does not synchronise like a mutex in C11. **Assumed, not checked** |
| **foreign primitives** | `extern fn` / `asm` (trust base, `N042`). **Assumed** |
| **what would close it** | `N323` demands `acquire` (or `acq_rel`/`seq`) on the atomic access that takes the lock and `release` (or `acq_rel`/`seq`) on the one that gives it, with a poison probe (a relaxed spinlock refused) and a positive probe (the runtime's ticket lock, `beispiele`); foreign primitives stay a named assumption |
| **who guards it today** | nothing mechanical; the header of `Spec.lean` names it |

## O27 — 176 accepted corpus programs have no Lean judgement: the exporter refuses them (recorded 2026-09-26, Opus agent C)

A green `lake build` covers a program only through its certificate
(`grammatik/Grammatik/Zertifikat/`, SATZKARTE §50). Every accepted program the exporter refuses
stands, by name and first refusal, in `Zertifikat/REGISTER.txt`, which `Spec.lean` cites as NOT
CLAIMED; the cargo test `zertifikate` keeps the register complete.

| | |
|---|---|
| **measured** | 199 accepted (129 corpus + 70 gift clean sides), 23 CERTIFIED, 176 UNCERTIFIED; of the 129 corpus programs 18 certified |
| **by first code** | `LG001` 116, `LG002` 36, `LG004` 13, `LG005` 6, `LG003` 3, `LG006` 2 |
| **why it is not one fix** | 114 of the 176 meet two or more refusal shapes (measured with a throwaway continue-on-refusal build); lifting `extern fn` alone gained 0 programs |
| **model decisions it needs** | an `Endblock` form for a tail `let` of a call and for `return` under `locks` (110, 125); records, wrapping integers, named assumptions outside `forever`/`retires`, devices, atomics (Opus B), pointers into records |
| **what would close it** | per-shape lanes, each measured by the register's CERTIFIED count |

## O28 — Linking is proved in the model and checked at the source level; the Rust race residue closed by Opus agent F, the rest stays open (recorded 2026-09-26, Opus agents E and F)

`GabbroZielVerbund` (`Zielsatz/Spec.lean`, proved as `gabbro_ziel_verbund`, SATZKARTE §54)
covers a program linked from two units over ONE link declaration, each accepted alone, under
the SAME hardware assumptions; `gabbro link` (`N501`-`N505`) checks the heads against the
bodies. Report: `messung/OPUS-E-LINKEN.md`.

| | |
|---|---|
| **review** | the Spec diff (a second statement, purely additive) has had no independent review round yet |
| **Rust vs Lean, the race legs** | **CLOSED by Opus agent F (2026-09-26, `messung/OPUS-F-VERBUND-RENNEN.md`).** Review E F1 (a read behind an imported head, raced by another thread of the importer, linked green) is closed twice: an imported head's declared READS join the importer's footprint (`fusswache2.rs`; probe 1246 now falls in `gabbro check --with` with the one-file `N291` + `N301`), and `gabbro link` checks the LINKED program whole (`verbund::verbinde_alle`: the units composed, each body from its owner, every start of every unit; the race deciders of `lok`/`renn`/`einzeln` run over the linked call graphs = the composed hulls under `KeinRueckruf`). Threads on both sides are judged, not refused (probe 1247 falls with `N291` + `N301`, twin `faeden-beide-*` links). What remains is the one-unit caveat: the Rust checker is not the Lean Bool |
| **contracts as text** | **Trees since Opus F:** `requires`/`ensures`/`effects`/signatures compared as normal-form trees (positions and redundant parentheses dropped, conjuncts order-free). Still no semantic equivalence and no refinement: an equivalent contract written as a different tree, and a weaker-but-sound import, are refused (Lean has ONE contract per function, `Verbindbar`) |
| **units and the build** | **Since Opus F** `gabbro build` runs the link over every manifest of two or more units (a unit may be several files) and `gabbro build a.gab b.gab` runs it over one-file units (nothing compiled); a module split over two units is refused (`N516`). Open: no certificate for a linked program (the exporter exports one `Einheit`) |
| **the C link step** | symbol resolution, calling convention, layout -- the linked C refining the linked G program is translation validation's (TODO §2, "The linking theorem") |
| **not claimed at all** | different hardware assumptions, callbacks through an import (`KeinRueckruf`), dynamic loading, ABI-level linking of foreign C |


---

## O29 — Dynamic unbounded data structures and probabilistic statements: planned for later, out of scope now (Simon, 2026-09-26)

Two whole classes of statement are **not open work for the current waves** and **not claimed**:
they are planned for "some day", after the current scope (the goal theorem's named gaps, the
Caprock rewrite, full translation validation).

| | |
|---|---|
| **dynamic unbounded data structures** | lists, trees, graphs and maps whose size is not bounded by a declaration (heap allocation without a declared ceiling, recursive types, pointer structures that grow at run time). Today's language covers bounded tables, arenas with a declared `max` (`grow`, reset-only free) and bounded strings; nothing beyond a declared bound is modelled, checked or claimed. |
| **probabilistic statements** | claims about distributions, expected values, failure probabilities or randomised algorithms (e.g. "the hash collides with probability ≤ p", "the retry succeeds with probability 1"). The goal theorem is a statement about EVERY run; no measure over runs exists in the model. |
| **status** | planned for later; no lane is tasked; no code, gift or example number is reserved. |
| **where it is named** | here, and in AGENTS.md §2/§3 ("OUT of scope for now"). The `Spec.lean` header does not list them yet; when the next reviewed Spec diff touches the NOT CLAIMED list, both lines belong there. |
