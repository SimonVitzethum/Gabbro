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

> **ANSWERED, and by neither of the two rows above — see §1.2.** The lane that owned §2.2
> re-measured and found that **the `L` column does not move at all**: `PFLICHTEN.md`'s third
> column asks *machine or subject*, and a device, a client and a token are subjects.
> `239 = 173 K + 66 L` stands. What moves is a different population — **GabbroV's**: 63, of
> which 8 not sayable and 55 sayable. *Both readings above shared one wrong premise, that the
> `L` column was the object of the question.* **The dilemma was real and the answer was
> outside it**, which is the argument for reporting rather than picking better than any
> argument I made for it.

---

## 1. §2 — the books, and Gate 1

*§2.2 and §6 were delivered by a parallel lane and merged as `97f5b21`. This lane verified
them against the mandate's own wording rather than starting over; §1.2 says where the
document is sharper than that lane's mandate was, and what was built as a result.*

### 1.1 §2.1 — `G1` had no threshold, and none was supplied

`G1`'s condition is *"a **noteworthy** part of the 66 L obligations is not sayable in the
fragment"*. **No count clears a gate with no number, and none trips it.** The sentence
~~*"`G1` does not fire"*~~ stood in four places; all four are struck through now, and none is
deleted -- **including this one**, which the guardian caught: a document that quotes a
withdrawn sentence in order to withdraw it still carries it, and `WG1` does not read intent:

```
dokumente/GABBROV.md      head, §10, §11
messung/GABBROV-V1.md     the answer up front -- this lane's own report, corrected by it
TODO.md                   the parenthesis in the 179 -> 181 note
```

**The repair that was refused is the entry.** Supplying the threshold now would supply one
chosen while `56 of 66` is on the table — `R2`, a rule pulled to fit a result. What takes over
are `E1` and `E2` of §1, and their force is not that they are stricter but that they were
written down **before** the runs they judge. `dokumente/HISTORIE.md` carries it.

**And the class is wider than the one row.** `G5` sits in the same table and cannot fire
either: *"the assumption set has no model"* is a question about formulas, and the eight
assumptions of the ten fragments are German prose sentences. **Two of five falsifiers cannot
be evaluated, and both looked evaluable from the outside** — `R11` one level up from where
this folder usually books it. Recorded as `O2` in the new `dokumente/OFFEN.md`.

**Mechanised, not only written.** `pruefe-widerruf.py` gained `WG1`, and it is the first entry
in that register whose revoked sentence was **not** refuted by a measurement — every earlier
one was overtaken by a build or a count. This one was withdrawn because nothing can confirm or
refute it. *A sentence that cannot be checked is worse placed in a report than a wrong one: a
wrong one has a next reader who can catch it.* The pattern is pinned to `G1` rather than to the
phrase, because the tree carries four legitimate `does not fire` sentences about other
subjects — a guardian that catches a true sentence teaches its next reader to disable it.

### 1.2 §2.2 — verified, and then the one thing the document asks for that was missing

The merged lane's argument is **right and better witnessed than the document's**: the document
argues from `SYNTAX.md`:1074 (prose), while `schleifen.rs`:221 raises `S003` when a `progress`
name resolves to no declared assumption and `S004` when it is unfalsifiable — *so a legal
`progress` name is a declared assumption by construction.* Its correction of `GABBROV.md` §5
also stands: the **emitted** manifest never double-booked; `gabbro pflichten` emits no
obligation from any `progress` clause.

**And its re-measurement of the counts is right where my §0.5 could only report a conflict.**
The `L` column does not move — `PFLICHTEN.md`'s third column asks *machine or subject*, and the
device, the client and the token are subjects. **239 = 173 K + 66 L stands.** What moves is
GabbroV's own population. *Neither of the two readings in §0.5 was the right one, and the
reason is that both assumed the `L` column was the object.*

**What was still missing is the half of §2.2 this lane was told wins if they differ:** *the
change belongs in `zaehle-pflichten.py`, not in the table.* The lane put the rebooking in
`PFLICHTEN.md`'s fourth column — correctly, as prose about three rows — and then reached `63`
by **subtracting `3` from `66` in prose, in four cells across two documents.**

> That is the 2026-08-20 shape exactly: several numbers over one thing, and the derivation
> living nowhere.

```
./instrumente/zaehle-pflichten.py --gabbrov
```

Built 2026-09-03. It derives the denominator from **two sides that have to meet**:

| side | what it reads |
|---|---|
| source | the real `progress <name>` clauses of `messung/fragmente/F*.gab` — the executable fragments, not the frozen prose of `FRAGMENTE.md`, whose anchors are from revision `708beed` and no longer point where they say |
| table | the `L` rows of `PFLICHTEN.md` whose fourth column names one of those names |

**It refuses rather than subtracting when the two disagree.** A `progress` clause with no
rebooked row means a row was missed; a rebooked row with no clause means a name was invented.
Three speech tests, all two-directional: every `progress` name is a declared `assume` (which
`S003` should guarantee and the mode asserts anyway); an invented clause with no table row is
*reported*, not absorbed; removing one rebooking raises the population 63 → 64 **and names the
row that went missing**.

```
== GabbroV's obligation population -- the two sides, and they have to meet ==
  `L` rows in `PFLICHTEN.md`                     66
  of these discharged by the assumption layer     3
  GabbroV obligation population                  63
```

`pruefe-zahlen.py` now holds all four cells against that command: **83 of 83 entries
recomputed, exit 0.**

*The mode prints its own limit: the three leave GabbroV's population because they are not
obligations, **not** because they are settled. A falsifier is a promise that someone could
refute an assumption, not a record that anyone has.*

### 1.3 §2.3 — the big step is its own entry, and it is not a leftover

`dokumente/AUSNAHMEN.md` is new and carries `L24`, `L34`, `L50`, `L52` as its first four rows
with name, reason and date. `dokumente/OFFEN.md` is new and carries the same finding as `O1`.
`dokumente/HISTORIE.md` carries it as a dated correction.

**One missing means seen four times, not four gaps.** L24 needs to say no state exists between
the pre and the post; L34 needs to say one does and what fails in it; L50 and L52 order two
effects of one big step. `Body.lean`'s `exec` hands out a start state and an end state.

**And the sharpening the mandate asks for is the part that must not be softened by counting.**
`GABBROV.md` §3 picks out one site as the place GabbroV would earn its keep beyond convenience
— §8.3.1's finding that `D013` checks only that the invariant `I` *exists*, expressly not that
the block restores it, so *"a `breaking` on the wrong-but-existing invariant still passes."*
**The statement that site needs is `L34`, and `L34` is row 2 of the exception list.**

> *An exception list whose members are the most valuable rows is a finding, not an appendix.*

### 1.4 The guardian over the exception list

```
./instrumente/pruefe-ausnahmen.py        # 4 rows, exit 0
```

`E2` without it is a declaration of intent, and the mandate says so. It holds **two** things,
because either alone is satisfiable by accident:

1. **The count against a booked mark (4).** Raising it means editing the guardian, which is a
   diff. §9 puts every addition beyond the four big-step rows on the stop-list; the mark is
   where that stop is mechanised.
2. **Every row's obligation name against `HISTORIE.md`.** A row whose reason is not written up
   there falls **at the same row count** — so an exception cannot be created by editing a
   table alone.

Four speech tests, and the third is the one that matters: **the empty list is a refusal, not a
pass.** Over zero rows both checks hold and the run is the greenest it could ever be — `W17`,
a positive verdict about nothing. The fourth is the control, without which the other three
would also pass over a guardian that always says no.

*What it does not do is judge whether a reason is really structural. That sentence is in the
fourth column and no script decides it.*

### 1.5 The merge hazard fired again, on this lane, and was caught

The coordinator's warning was not hypothetical. This lane added `messung/GABBROV-AUFTRAG.md`
and moved `pruefe-widerruf.py`'s file count 184 → 185; the other lane added
`messung/GABBROV-V2.md` and moved it 184 → 185. **Git saw two identical `185`s and merged them
without a conflict. The merged tree measured 186.**

Re-measured after the merge and set to 186, then to 188 when `AUSNAHMEN.md` and `OFFEN.md`
joined. *Three times in two days now, and the shape is always the same: a merge that would
have to ADD has no text conflict.*

### 1.6 The other numbers this work moved, all re-measured rather than reasoned

Adding one guardian and one counter mode moves five guarded figures. Each was found by
`pruefe-zahlen.py` / `pruefe-todo.py` going red, not by being anticipated:

| figure | | |
|---|---|---|
| exit sites behind the first (`RUECKLAUFWERTE.md`) | 304 → 309 → **312** | the five refusals of `--gabbrov`, then the new guardian's |
| guardians that can abort mid-run | 52 of 55 → **53 of 58** | |
| instruments carrying all five requirements (`README.md`) | 57 → **58** | |
| guardians (`README.md`) | 29 → **30** | |
| figures with a command (`TODO.md`, two cells) | 79 → **83** | |
| files the revocation guardian reads (`TODO.md`) | 184 → **188** | 12 → **13** revocations |

**One of them was a real finding about my own work.** `pruefe-waechter.py` refused
`pruefe-ausnahmen.py` at first: its `return 1` was a *partial measurement that looks like a
whole one* — output before it, nothing after, and a return code reading as *finding* rather
than *cut short*. Repaired by wrapping `main` in `abschnitt.fahre`, the tree's shared form,
rather than by booking an exemption. *A new guardian that does not itself satisfy the
guardian-of-guardians is the cheapest possible instance of the class it was built to catch.*

### Gate 1 — met

| | |
|---|---|
| `pruefe-zahlen.py` green | **yes** — 83 of 83, exit 0 |
| new denominator out of the command | **yes** — `zaehle-pflichten.py --gabbrov`, 63, three speech tests |
| `AUSNAHMEN.md` with guardian | **yes** — 4 rows, `pruefe-ausnahmen.py`, four speech tests |
| entries written | **yes** — `HISTORIE.md` ×2, `OFFEN.md` (O1–O3), `AUSNAHMEN.md` ×4 |

*Also green after the work: `pruefe-todo.py`, `pruefe-widerruf.py`, `pruefe-englisch.py`,
`pruefe-waechter.py`.*

---

## 2. §3 — the day's experiment

**This section is written in two commits on purpose.** The draw below was recorded and
committed **before** any of the five rows was looked at; the results follow in the next
commit. §3 says the five are drawn *before looking*, and *"if one of them fits suspiciously
well, that is a reason NOT to take it"* — a rule that can only be honoured if the drawing and
the judging are separated in the record, not merely in intention.

### 2.1 The draw

Population: the sayable rows of `programmlogik/gabbrov/V1.lean` — the 66 minus the ten that
carry `notSayable`, minus `L66`, which left for the assumption layer on 2026-09-03.
**55 rows.**

```
seed  b15ef79        the commit this lane produced at Gate 1
order sha256(seed + ":" + row), ascending
```

The seed is the Gate 1 commit. It existed before any row's difficulty was inspected, and it
cannot be tuned afterwards without the draw visibly changing.

```
population 55   not sayable 10   L66 rebooked
two-state in the population: 19
table identity              : L04 L05 L09 L15 L16

hash order, first five      : L01 L40 L39 L23 L62
  constraint table identity   NOT met -- L05 replaces L62
  constraint two-state        already met

THE FIVE: L01  L05  L23  L39  L40
  L01  domain
  L05  table identity, two-state, domain
  L23  single state
  L39  two-state
  L40  two-state
```

**§3 asks for two properties in the sample, and only one had to be forced.** Three of the
blind five are two-state relations already; none was from the table-identity class, so `L05`
— the first member of that class in the same hash order — **replaces the last blind pick**
rather than being added. *The correction is one element and it is visible; the draw stays a
draw.*

| | |
|---|---|
| `L01` | `cdt_wohlgeformt`'s sibling half — a predicate over a table domain, one state |
| `L05` | table identity **and** two-state: a `cdtWf` preservation over a bounded reachability |
| `L23` | `caller` and `reply_owner` are set together or not at all — one state, and the pre/post half of `L24`, which is row 1 of `AUSNAHMEN.md` |
| `L39` | two-state |
| `L40` | two-state, and `PFLICHTEN.md` marks it with a gap of its own («B26», no placeholder for the pre-state) |

*Recorded here before the rows were read. What they say, whether a solver touches them, and
what that means for the scope of the whole project is the next commit.*

### 2.2 What was actually run

Hand work, as §3 asks — no tool, no scaffold. For each of the five: the Lean `Prop` from
`programmlogik/gabbrov/V1.lean`, the body or the declaration from the fragment source, and a
**verification condition written by hand in SMT-LIB** and put to Z3.

```
/opt/verus/z3 --version          # Z3 version 4.16.0
free -g                          # 31 total, 19 available -- a solver call is not a build
(set-option :timeout 60000)      # in every file
```

The files are in the tree, one per row, with the encoding decision written into each:
`messung/gabbrov/L01.smt2`, `L01b`, `L01c`, `L05` (generated by `erzeuge-L05.py`), `L05c`,
`L23.smt2`, `L39.smt2`, `L40.smt2`.

**The verification condition is `premises ∧ body → obligation`, negated.** So `unsat` is
*passed*, `sat` is *refuted with a counterexample*, `unknown` is *undecided* — the three
outcomes of `GABBROV.md` §4, read straight off the solver.

**And the premise rule is the whole experiment:** a premise is available only if the fragment
**declares** it. M1's range facts are assumed (plumbing, `GABBROV.md` §9 point 4); a table
invariant is assumed if the `table` block states it. Nothing else. *That is what a checker
reading the manifest would have.*

> **This encoding is my judgement, and it is on the trust list by name.** §9 points 5 and 6
> are *"meaning of the obligation texts"* and *"translation fragment → SMT"*. The `.smt2`
> files are in the tree so that the judgement can be read and disagreed with, rather than
> only the verdict.

### 2.3 The five results

| row | Z3 | best of 3 | verdict |
|---|---|---:|---|
| **L01** — a root has no predecessor | **sat** | 0.021 s | **refuted**, with a counterexample |
| **L05** — the CDT stays well-formed | **sat** / **unknown** | 0.03 s … timeout | **refuted where it answers**, undecided where it does not |
| **L23** — `caller` and `reply_owner` are set together | **unsat** | 0.019 s | **passed** |
| **L39** — `drvok` | **unsat** | 0.017 s | **passed** |
| **L40** — a reset applies from every state | **sat** | 0.016 s | **refuted** |

**Two passed, three refuted, none undecided at the bounds the corpus actually uses.**

### 2.4 The three refutations are three DIFFERENT defects, and not one of them is Z3

This is the finding, and it is not the one §3's question anticipated.

**L01 — the missing premise is one Gabbro's `pred` cannot state.** The counterexample: slot `s`
has a `next_sibling` `n`; `n` has no parent; `s` does. `unlink` writes `prev[n] := prev[s]`,
and `n` is now a root with a predecessor. What excludes that configuration is the **mutual**
sibling chain — `slots[s.next].prev == s` — which is `L02`, and `F01.gab`:181-183 says in its
own comment why it is not declared: **«B14», the resolution of an `option index into` inside a
predicate.**

```
L01                      sat    0.021 s     the declared premises only
L01b  + L02 («B14»)      unsat  0.019 s     proved
L01c  + cdt_wohlgeformt  sat    0.021 s     still refuted -- see below
```

`L01c` exists because run 1's model gave a slot its own parent, and a reader may call that
nonsense and the refutation an artefact. So run 3 adds `cdt_wohlgeformt`, which the fragment
*does* declare and which forbids the cycle. **It is still `sat`.** *The premise that repairs
`L01` is exactly the one premise the language cannot express, and no other.*

> **So for this row GabbroV is neither a prover nor a pre-sorter.** The solver decided in
> 21 ms, twice, in both directions. What stands between *refuted* and *passed* is a
> production in `pred`.

**L40 — the transition the obligation talks about cannot be written.** «B26» is already
recorded in the row. Measured rather than believed: given the four transitions `F04.gab`
declares, is there a pre-state with a declared step to 0? **`sat` in 16 ms**, and the witness
is `#x00` — *no declared transition reaches 0 from anywhere*, the initial state included.
`ack` goes `0 → ACK` and nothing goes back. The gap is not "the reset is unverified"; it is
"the table has no reset at all, and the four rows that are there cannot be completed".

**L05 — the fragment is wrong, and the solver said so before the reachability ever became the
problem.** `unlink` declares `maintains cdt_wohlgeformt` and sets `parent[s] := None`. Unless
`s` is `WURZEL`, slot `s` then reaches nothing.

```
L05, bound 4              sat    counterexample s = 1, and 1 ≠ WURZEL
L05, + s = WURZEL         unsat  0.02 s
```

The only premise that repairs it contradicts what `unlink` is for. That points at the
invariant, so:

```
L05c  cdt_wohlgeformt  ∧  one detached slot        unsat   0.02 s
```

**`cdt_wohlgeformt` forbids a free slot.** It quantifies over `slots of c` — the whole table,
not the used slots — and a slot outside the tree has `parent == None` and is not `WURZEL`.
`release_slot` (`F01.gab`:233) leaves exactly such a slot behind. *So no removal path in F1
can restore the invariant it maintains, and the invariant cannot hold over any table with a
free slot — which is every table before it is full.*

> That is a defect in the corpus, found in 20 ms, by a question nobody had asked. It is also
> the answer to *"where would GabbroV create value?"* that `GABBROV.md` §3 was looking for,
> arriving from an unexpected direction: **not by proving hard obligations, but by refusing
> ones that were never true.**

### 2.5 And the one place the solver really is the wall — DEMAND 3

`L05`'s reachability is `reachesIn`, bounded by the table's own `count`. Here the bound
becomes a number, and the number is the measurement:

| bound | file | Z3 | time |
|---:|---:|---|---:|
| 2 · 4 · 8 · 12 · 16 | 1.6–11 KB | sat | ≤ 0.4 s |
| 17 | 12.6 KB | sat | 6.6 s |
| 18 · 19 | 14–15 KB | sat | ≤ 0.4 s |
| **20** | 16.5 KB | **unknown** | 60 s (×3) |
| 21 | 17.9 KB | sat | 0.34 s |
| **22** | 19.4 KB | **unknown** | 60 s (×2) |
| 24 · 32 · 48 | 23–81 KB | sat | ≤ 0.3 s |
| **64** | 140 KB | **unknown** | 60 s |

**The failure is not monotone in the bound, and that is the finding rather than the wall.**
20 and 22 time out while 21, 24, 32 and 48 answer in under a third of a second — reproduced,
twice each, on an idle machine. *A solver that answers at 21 and not at 20 gives you no bound
to plan with.* A tool built on "unroll to the table's count" would not degrade gracefully; it
would be fast, fast, fast, and then silent, with no property of the input predicting which.

**And the bound the corpus asks for is not 20.**

```
messung/fragmente/F01.gab:56    const NSLOTS : u32 = 80256;
beispiele/01-tabelle.gab:10     const NSLOTS : u32 =  4096;
```

**Four orders of magnitude between where the solver stops and where the obligation lives** —
and five of the 63 rows hang on this one means (`L04`, `L05`, `L09`, `L15`, `L16`), the demand
`GABBROV.md` §7 does *not* record. *`V1.lean`'s note says the bound "is what makes the helper
total and the unrolling finite, and it is the whole reason the row reads DEMAND and not NOT."
Finite is right. It is not the same as tractable.*

### 2.6 The answer to the question §3 says decides the project's scope

> *"Does GabbroV become a checker or a pre-sorter?"*

**On this sample: neither, and the sample says why the question has a third answer.**

A pre-sorter is what you get when the solver is the bottleneck — it clears the easy rows and
says *undecided* on the hard ones, leaving the state of the world unchanged. **Z3 was not the
bottleneck on four of the five.** It answered in 16–21 ms, and it answered in *both*
directions on demand: add the missing premise to `L01` and it flips to `unsat` in 19 ms.

What decided the outcomes was, in order:

| | rows | what actually decided it |
|---|---|---|
| **the premise supply** | L01 | a `pred` production that does not exist («B14») |
| **the corpus being wrong** | L05 | an invariant that cannot hold and a body that does not maintain it |
| **the construct not existing** | L40 | «B26» — the transition table cannot be completed |
| **nothing at all** | L23, L39 | proved on the first try |
| **the solver** | L05's reachability only | and non-monotonically, which is worse than a wall |

> **So the honest headline is that a GabbroV built today would spend its first months as a
> defect finder, not as a prover.** Three of five drawn-blind rows are refuted, and every
> refutation is a real thing wrong with the tree — two language gaps that were already
> recorded as gaps, and one invariant that nobody had noticed cannot hold.

**What this does NOT settle, and it is the part that decides the build:** *whether the 55 stay
this cheap once the obligations that have no proof today are reached.* The five were drawn
blind from all 55, which is the right way to sample — but three of them turned out to be
refutable, and a refutation is a much easier question than a proof. **`unsat` is the expensive
answer, and only two of the five produced one.** A sample of two is not a rate.

*And a second limit, named rather than left out:* every encoding here is mine. `GABBROV.md` §9
puts *"meaning of the obligation texts"* and *"translation fragment → SMT"* on the trust list
as points 5 and 6, and this run is exactly those two points exercised by hand. **A wrong
encoding produces a confident answer**, which is the shape of `G4`, the falsifier the document
says does not show up by itself. The `.smt2` files are in the tree for that reason.

---

## Gate 2 — reached, and this is where the mandate says to stop

| §3 asks for | |
|---|---|
| five obligations from the sayable set | **L01 L05 L23 L39 L40** |
| drawn before looking, and recorded | seed `b15ef79`, committed in `3a5172c` **before** any row was read |
| mixed, not the easiest | 3 two-state, 1 with table identity, 1 carrying a recorded gap of its own |
| specification in Lean | `programmlogik/gabbrov/V1.lean`, unchanged |
| does a solver even touch them | **eight solver runs, each with its output** |
| five results, each with solver output | §2.3–§2.5 |

**Reporting and stopping here**, as §9 and §3 both require. The number that decides how much
building is justified is above, and the decision is not an agent's.

*Three questions this lane would ask before §4 starts, in the order they would change the
plan:*

1. **`L05`'s defect is a corpus repair, and repairing it changes an obligation's meaning.**
   `cdt_wohlgeformt` needs `forall s in used slots of c`, or the invariant needs a different
   home. That is the same shape as the `L44`/`L53` tautology finding the other lane left open:
   *rewording an obligation decides what the fragment meant.* Not touched.
2. **`L01` says the aggregation demand in §7 has a sibling that is not on the list.** «B14» —
   resolving an `option index into` inside a `pred` — is not among the three demands
   `messung/GABBROV-V1.md` records, and it is the difference between *refuted* and *passed*
   on a real row. **Should it be a fourth demand?**
3. **DEMAND 3 may not be buildable in the shape V1 assumes.** *"Bounded, so translatable"* is
   true and insufficient at 80 256. If the five reachability rows need an axiomatised
   transitive closure instead of an unrolling, that is a different piece of work from the
   other two demands, and §7 does not yet distinguish them.
