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
| **the question for the owner** | is «B14» a fourth demand, or a fourth *kind* of demand? |
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

## O7 — `N030` compares opaque types at a PARAMETER and not at a FIELD

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
| **what would close it** | `N030` reading the declared type of a field access, not only of a parameter — the same move `R013` made for pointer rights, one position further |
| **what it is NOT** | `S2`. The language states this correctly; a pass does not read it. Same family as `R008`/`R013` in `messung/PASSREGISTER.md` |
| **measured at** | `messung/FUENFTE-MARKE.md` §3, `messung/proben/probe-opak-am-feld.gab` |

---

## O8 — A `tagged type` value has no constructor

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

