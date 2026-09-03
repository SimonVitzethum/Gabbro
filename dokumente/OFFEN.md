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

## O3 — The manifest does not carry the obligation text

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
| **what would close it** | `AUFTRAG-GABBROV.md` §4 — version field first, all readers on both formats, then the format |
| **material already present** | `gabbro pflichten --lean` carries the text as a datum (`post_duty_2 : Expr`) |
