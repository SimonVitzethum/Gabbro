# GabbroV — the run against `dokumente/AUFTRAG-GABBROV.md`

*Started 2026-09-03 from tree `af48491`. This file is the running report the mandate asks
for at every gate. It is written as the run proceeds and committed with each finding, not
at the end. Every count below names the command that produced it.*

**Machine note.** The mandate's §10 puts computation on `ki-pc-fisch-101` in an own
directory; this lane uses `gabbro-ag`. Both transfers, in the prescribed order. Local runs
carry a `free -g` beside them.

---

## 0. The four answers, before anything was touched

The mandate opens with four questions and the instruction *"if your understanding differs,
say so and wait"*. The four answers stand below. **One reading does differ, and it is an
arithmetic one in §2.2 — it is reported in §0.5 rather than acted on.**

### 0.1 Why the rebooking belongs in `zaehle-pflichten.py` and not in the table of `PFLICHTEN.md`

Because the table is the **datum** and the counter is the **definition of the population**,
and only one of the two can hold a reason.

`zaehle-pflichten.py --spalten` derives `66` by reading the third column of every anchored
row of `PFLICHTEN.md`. `pruefe-zahlen.py` then holds six numbers in `PFLICHTEN.md`'s two
summary tables against that command (`instrumente/pruefe-zahlen.py`:670–711). So the two
sides are already wired: **a letter changed in the table moves the counter with it, and
every guard stays green.** The rebooking would leave no trace but two characters in a
239-row table, and no reader could tell a rebooking from a typo. Worse, the tool's own
docstring says what the column is: *"the class `K`/`L` is a JUDGEMENT a human wrote into
the third column — this tool counts it, it does not make it."* Editing the column is making
a new human judgement with the evidence nowhere.

In the counter the same change is a **named rule with a search path**: three rows are
excluded because their names stand as `assume` in the fragment source and `SYNTAX.md`:1074
says a `progress` clause *is* an assumption. That rule can be spoken-probed in both
directions (R14 — an invented `progress` row must move the number, an invented ordinary row
must not), it can print both numbers from one run, and `pruefe-zahlen.py` can then hold the
document against a number whose cause is readable.

And that is the 2026-08-20 lesson used in the direction it points. Three numbers then stood
over one thing and the one **with** the search path was the wrong one — the remedy is not to
distrust search paths but to make sure the search path carries the *meaning* of the
population, so there is exactly one place where "what counts as an `L`" is defined.

### 0.2 Why "four rows about ordering are not sayable" is **not** a gap of the Lean fragment

Because a fragment is a language of predicates over the objects the **shared semantics**
hands it, and the object those four rows need does not exist there.

`programmlogik/Gabbro/Body.lean`'s `exec` is big-step: it maps a state and a statement list
to an `Outcome`. It yields a start state and an end state and **nothing between them**. All
four rows are about the space between: L24 says no third state exists in which one of two
places is written and the other is not; L34 says one does exist and names what fails in it;
L50 and L52 say one effect precedes another. A new means in §7 would have nothing to range
over — it would be a formula without a denotation, or, which is worse and is the failure §7
names as the commonest, a formula with a *wrong* denotation: `flush ∧ reply` type-checks,
reads right and is strictly weaker than the obligation whose name it would carry.

The corpus itself already draws the line in the right place. The pre/post half of L24 is not
missing — it is `L23`, its own row, and it stands as a `Prop`. *What is left of L24 once L23
is subtracted is exactly the residue no predicate over a state pair can hold.*

So the gap sits one level below the specification language, in the operational semantics —
and `exec`'s big-step character is on §9's stop-list precisely because the Isabelle proofs
rest on it. **Widening the fragment cannot close it; only a small-step or trace semantics
could, and that is a different and much larger decision.** Calling it a fragment gap would
point the repair at the one place where it cannot be made.

### 0.3 Why `aushaengen :: ensures #1` violates §15's own sentence

§15 promises *"Nothing is silently lost"* and says the ratchet **runs over names**. Its own
example lines carry the obligation as text:

```
obligation revoke.functional  "ensures !exists k in descendants of s: k.used"  offen
```

What the binary emits carries a function name, a clause kind and an **ordinal**. The text is
not in the product; recovering it means reading the source and counting conjuncts — which is
exactly what `GABBROV.md` §2 promises the tool need not do.

**And the failure is silent in the strict sense, which is measurable.** `ensures #1` of
`aushaengen` is `c.slots[s].elter == None` (`beispiele/01-tabelle.gab`:91). Exchange the
first and third conjunct in the source — a reordering no rule forbids and no reviewer would
flag — and the obligation named `ensures #1` becomes `c.slots[s].naechstes == None`:

```
./target/debug/gabbro pflichten beispiele/01-tabelle.gab   > m-orig.txt
# same file, ensures conjuncts 1 and 3 exchanged
./target/debug/gabbro pflichten <swapped>                  > m-swap.txt
diff m-orig.txt m-swap.txt
# 1c1  -- the header line, i.e. the FILE NAME, and nothing else
```

**The two manifests are byte-identical apart from the path in their header.** Three
obligations were permuted and the register did not move. So the name the ratchet runs over
does not identify the obligation it names: the same line stands for a different statement
before and after, and nothing reports it. *That is not "the text is missing"; it is "the
identity is positional and the position is free to move".*

### 0.4 Why a red row in the correspondence table is a failure and a yellow one is not — and how both differ from unsatisfiability

**Red is *Lean can say it, Gabbro cannot*.** Then a specification asserts something no Gabbro
program is able to claim. The obligation it creates cannot be discharged by any program in
the language — not because the program is wrong but because the sentence has no counterpart
on the other side. The gap does not get closed, it gets *moved one level up*, and it looks
like progress while it moves. It is a defect we introduce ourselves, and we can remove it
ourselves — take the fragment construct back, or build the Gabbro side first. A defect that
is ours and removable is a failure, not a state.

**Yellow is *Gabbro can say it, Lean cannot*.** Then a program states something the
specification is silent about. The obligation ends **undecided**, and undecided is one of the
three honest outcomes: it writes the obligation back as `open`, the state it was already in.
Nothing false is claimed, soundness is untouched, and the row is recorded by name. §4 says
undecided may occur often; yellow is that sentence in table form.

**And neither is unsatisfiability.** Red/yellow is the *channel* question — can it be
**said**. Unsatisfiability is the *content* question — an expressible requirement that no
state can **meet**. Both are failures and both are real, but they are found by different
instruments: red by a static table held against a table, before any specification is written;
unsatisfiability by a solver call per obligation, in §6. Merging them hides both — a table
comparison can never find a satisfiable-looking `requires` that no state fulfils, and a
solver can never find a construct that cannot be written down at all.

### 0.5 The one reading that differs: §2.2's `56 of 64` and the third `progress` row

*Reported, not acted on. §2.2 is another lane's section; this note is for whoever settles it.*

§2.2 states two things in consecutive sentences:

> *"**Three** `progress` clauses are already `assume` in the source and are booked a second
> time as a logic obligation. The result is therefore **56 of 64**."*

**Those two sentences cannot both be executed.** The three rows are `L42`, `L46` and `L66`,
identified by anchor:

```
./instrumente/zaehle-pflichten.py --spalten          # 66 L rows, the population
grep -n 'progress' dokumente/PFLICHTEN.md            # 3 hits: :237 (L42), :260 (L46), :383 (L66)
```

`L42` and `L46` are among the ten that do not stand as a `Prop`; **`L66` is among the 56 that
do.** So:

| if the counter excludes | denominator | sayable | not sayable |
|---|---:|---:|---:|
| all **three** `progress` rows | **63** | **55** | 8 |
| only `L42` and `L46` | **64** | **56** | 8 |

`56 of 64` is the second row, i.e. **two** rows moved, not three. The first sentence of §2.2
describes three.

**Both readings have an argument, and they are different arguments**, which is why this is a
decision and not an arithmetic slip to be patched:

* *Three.* The double booking is structural and uniform — all three names stand as `assume`
  in the fragment source and are therefore already in the assumption manifest.
  `SYNTAX.md`:1074 makes `progress` an assumption by construction. The rule has one search
  path and no case distinction.
* *Two.* `GABBROV.md` §5 and `messung/GABBROV-V1.md` §6 both argue that `L66` differs in the
  **referent** of its named predicate — `token_verbraucht` is about the program, the other
  two about the world — and `PFLICHTEN.md` draws that line in L66's own row
  (*"the ALGORITHM's progress measure, not the machine's finiteness"*). On that reading `L66`
  is a genuine obligation that happens also to be declared as an assumption, and only the two
  world-facing rows leave the column.

*Note that the second reading concedes a residue: if `L66` stays in the `L` column it is
still booked twice, and that double booking is then a known and unaddressed one.*

**This lane picks neither.** Two sides moved one number for different causes once already
this week and the merge could not tell them apart; the rule that came out of it is
re-measure, never pick. The measurement is above; the choice is a classification judgement
and belongs to whoever owns §2.2.
