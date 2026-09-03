# The named exceptions to `E2` — obligations that cannot end decided

**`E2` of `AUFTRAG-GABBROV.md` §1 is the decision share: how many of the obligations GabbroV
treats end as *passed* or *refuted* instead of *undecided*.** Its claim is *all of them, except
the structurally undecidable — and those stand here by name.*

> **By name, and not as a percentage.** A percentage lets the exception list grow silently with
> every obligation that turns out to be hard. A list has to be added to, and an addition is a
> diff.

---

## The bar for getting on this list

**Structural, not difficult.** The reason has to be a property of the semantics or of the
statement, not of the solver or of the day. *"The solver does not get through"* is
**undecided** — a per-run outcome — and not an exception.

The test is the one `AUFTRAG-GABBROV.md` §1 states: *no fragment and no solver changes it.*
If a better solver, a wider fragment or more time could move the row, it does not belong here.

**And the two failure directions are not the same.** An exception says *"this can never end
decided"*. It does **not** say the obligation is met, that it is unimportant, or that it has
been discharged. Every row here is an obligation that stays **open** in the manifest — the
state it was already in — and GabbroV writes it back that way.

---

## The list

| # | obligation | reason — and why it is structural | since |
|---|---|---|---|
| 1 | **L24** — `caller` and `reply_owner` are written in **one** step | The statement is *"no third state exists in which one is written and the other is not"*. It quantifies over a state **between** the pre and the post. `programmlogik/Gabbro/Body.lean`'s `exec` is **big-step**: it maps a state and a statement list to an `Outcome`, and there is no intermediate state to name, let alone to quantify over. | 2026-09-03 |
| 2 | **L34** — the invariant does **not** hold between the two assignments | The same object, from the opposite side: L24 needs to say no intermediate state exists, L34 needs to say one does and what fails in it. **Same missing means, opposite directions.** | 2026-09-03 |
| 3 | **L50** — `Flush`: the flush completed **before** the reply | An ordering between two effects of one big step. A predicate over a pre/post pair cannot separate two effects that the semantics collapses into one transition. | 2026-09-03 |
| 4 | **L52** — `Stop`: the reply still goes out **before** the service ends | Same as L50. *Both would type-check as `flush ∧ reply` — which reads right, is strictly weaker, and would carry the obligation's name while saying less than it.* | 2026-09-03 |

**Four rows, one cause.** They are not four separate gaps; they are one missing means seen
four times.

---

## Why the cause is not in the specification fragment — and why that matters here

The obvious reading is *"§7's Lean fragment is too narrow"*, and it is wrong in a way that
would point the repair at the one place where it cannot be made.

A specification fragment is a language of predicates over the objects **the shared semantics
provides**. `exec` provides a start state and an end state. A new construct in §7 would have
nothing to range over: it would be a formula with no denotation, or — the failure §7 itself
names as the commonest way such tools go unsound — a formula with a **wrong** one.

**The corpus already draws the line in the right place.** L24's pre/post half is not missing:
it is `L23`, its own row, and it stands as a `Prop`. *What is left of L24 once L23 is
subtracted is exactly the residue no predicate over a state pair can hold.*

So the cause sits one level below the specification language, in the operational semantics —
and `exec`'s big-step character is on `AUFTRAG-GABBROV.md` §9's stop-list **because the
Isabelle proofs rest on it**. Only a small-step or trace semantics could close it, and that is
a different and much larger decision than widening a fragment.

---

## And this is the class where GabbroV was supposed to be worth most

*This is the sharp end of the entry, and it should not be softened by being counted.*

`GABBROV.md` §3 picks out one site as the place GabbroV would create value beyond convenience:
§8.3.1 records that `D013` checks only that the invariant `I` **exists**, and expressly not
that the block restores it — *"a `breaking` on the wrong-but-existing invariant still passes."*

**The statement that site needs is L34**, and L34 is row 2 of this list.

> So the four rows are not four leftovers at the edge of a good result. **They are the centre
> of the case for building GabbroV at all**, and today they are the part of it that the shared
> semantics cannot express. *A list of exceptions whose members happen to be the most valuable
> rows is a finding, not an appendix.*

---

## The guardian

```
./instrumente/pruefe-ausnahmen.py
```

It holds two things at once, because either alone can be satisfied by accident:

1. **The count against a booked mark.** Raising it means editing the guardian, which is a
   diff. `AUFTRAG-GABBROV.md` §9 puts *any* growth beyond these four rows on the stop-list, so
   the mark is where that stop is mechanised.
2. **Every row's name against `HISTORIE.md`.** A row whose obligation is not written up there
   falls, so an exception cannot be added by editing a table alone — the reason has to be
   recorded where the folder keeps its corrections.

*An empty list is a **refusal**, not a pass:* over zero rows both checks hold trivially, and
the greenest run this guardian could produce would be the one where it looked at nothing.
