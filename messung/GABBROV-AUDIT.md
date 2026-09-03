# GabbroV — the audit of Gate 2, of design C, and of the manifest

*Started 2026-09-03 from tree `393d866`. This file is the report, written as the run
proceeds and committed with each finding. Every count names the command that produced it.
This lane BUILDS nothing except where it says so at the site.*

**Machine note.** `free -g` beside every local run. Solver directory on the server would be
`gabbro-vm`, but see §0 — the solver is not there.

---

## 0. Two premises of the mandate, measured before anything was used

**`z3` is on THIS workstation and is NOT on `ki-pc-fisch-101`.** The mandate states the
opposite and it is the wrong way round.

```
which z3                        # no z3 in $PATH
/opt/verus/z3 --version         # Z3 version 4.16.0 - 64 bit
ssh ki-pc-fisch-101 'which z3; ls /opt/verus/z3'
                                # z3: command not found
                                # ls: cannot access '/opt/verus/z3': No such file or directory
```

So every solver call in this report is local, and that is not a breach of `CLAUDE.md`: a
`check-sat` on a 2–140 KB file is not a build. `free -g` at the start of the run reported
**31 GB total, 19 available**. The one call class that could have grown — the 60 s
reachability timeouts of §2.5 — was re-run with the memory watched.

*Reported rather than worked around, because a lane that quietly runs locally against an
instruction to run remotely leaves no record of which of the two was wrong.*

**The worktree was three commits behind `master` at start** (`01d69b2`), and none of the
five files the mandate names existed in it. `git merge --ff-only master` before the first
measurement, as `CLAUDE.md` requires. *A lane that measures a tree without the subject in it
gets a clean, meaningless zero.*

---

## 1. Question 1 — what is actually wrong with GabbroV?

**The answer is the third of the three readings the mandate offers, and it is the good one:
the corpus is wrong, three times over.** Two of the three refutations were re-derived by a
hand that had not seen the first encoding, and both came back with the same verdict and a
sharper reason.

### 1.1 How the second encodings were kept independent, and where that discipline leaked

*The mandate asks for "a second encoding, written without looking at the first". I had
already read `messung/gabbrov/L01.smt2`, `L40.smt2` and `L05c.smt2` before that sentence
became actionable, so **my own second encoding could not have been blind.*** Rather than
write one and call it independent, the second encodings were given to three separate agents
that carry none of this conversation, each with:

* an explicit prohibition on `messung/gabbrov/`, every `*.smt2` in the tree, and the four
  GabbroV documents;
* a packet of SOURCE only — the fragment excerpt, `Body.lean`'s model, `V1.lean`'s helpers
  and the row's own `Prop`, copied into a scratch directory;
* the verdict convention (`unsat` = passed, `sat` = refuted, `unknown` = undecided) and the
  premise rule, but **no hint of what the first encoding found**.

Two of the three disclosed, unprompted, that the shared scratch directory listed files from
their siblings, and that they had opened none of them. *A disclosure nobody asked for is the
only evidence of isolation worth having.*

**The leak that remains, named:** the packets were assembled by me, and I chose what went
into them. A row's premise supply is exactly what the experiment is about, so the choice of
excerpt is itself an encoding decision. What the three did NOT get from me is any modelling
decision — representation, theory, bound, control — and that is where all three diverged.

### 1.2 `L40` — refuted twice, and the second encoding proves the stronger claim

| | first encoding (`messung/gabbrov/L40.smt2`) | second encoding (independent) |
|---|---|---|
| representation | `(_ BitVec 8)`, `schritt` as a 4-clause disjunction | `(_ BitVec 8)`, `step` as a 4-clause disjunction, **skolemised witness** |
| verdict | **sat**, 0.016 s | **sat**, 0.014 s |
| witness | `#x00` | `#x00` — DEVICE_STATUS = 0, the initial state |
| control | none | **`L39` = `unsat`, 0.015 s** |
| stronger claim | asserted in prose | **measured: `unsat`, 0.014 s** |

The two agree on the verdict and on the witness. **What the second encoding adds is the part
the first only asserted.** The first says in prose *"no declared transition reaches 0 from
anywhere"*; the second put that to the solver as its own file — `∃p q. step(p,q) ∧ q = 0` —
and got **`unsat` in 0.014 s**. The claim is now measured.

It also brought two instruments the first did not have, and both matter:

* **A control.** `L39` through the same encoding comes back `unsat` while `L40` comes back
  `sat`. Without it, a `sat` on `L40` is compatible with an encoding that says `sat` to
  everything. *`GABBROV.md` §11 calls `G4` the falsifier that does not show up by itself; a
  control is the cheapest thing that makes it show up.*
* **A named vacuity hazard in its own encoding.** `L40`'s antecedent is
  `DEVICE_STATUS = .int v`. If that place could hold `.absent`, the antecedent would be
  unsatisfiable and `L40` would pass **vacuously** — a `passed` that means nothing. The second
  encoder wrote the totality assumption down as an assumption rather than letting it sit
  inside the model. *That is `V2.lean`'s subject appearing inside a `V1` row, and neither
  document connects them.*
* **A liveness probe on the step relation**: all four declared pairs `sat`, an invented fifth
  `unsat`. A typo that dropped a clause would have handed `L40` a free refutation.

**Verdict: the refutation holds, and it is stronger than reported.** «B26» is not "the reset
is unverified" and not even "one state has no reset" — the four declared transitions are a
strictly ascending chain `0 → 1 → 3 → 11 → 15` with no edge back to `0` at all.

### 1.3 `L05` — refuted twice, and the second encoding measured the repair

The second encoding shares almost nothing with the first: `Value` as a four-constructor SMT
datatype rather than a two-form `Opt`; `World` as `(Array Place Value)` with array
extensionality carrying the frame; the body threaded through **seven** worlds `w0..w6` rather
than collapsed into one nest of `ite`s; `N` pinned to 4 to make the decisive files
quantifier-free.

| | first | second |
|---|---|---|
| `L05` verdict | **sat** | **sat**, 0.13 s |
| `cdt_wohlgeformt` ∧ one detached slot | **unsat**, 0.02 s (bound 6, N symbolic) | **unsat**, 0.03 s at N = 4 **and `unsat`, 0.01 s at symbolic N** |
| encoding-soundness control | none | **`s = WURZEL` → `unsat`, 0.10 s** |
| repair candidate | named in prose as an open question | **measured, and it FAILS** |

**The central finding is confirmed by two disjoint encodings:** `cdt_wohlgeformt` quantifies
over `slots of c` — the whole table — and `reachesIn` falls to its `| _ => false` arm the
moment it meets an absent parent on a non-root slot. One free slot anywhere falsifies the
invariant outright. `release_slot` sets `used = false` and never clears `parent`; `unlink`
clears `parent` and never clears `used`. **The invariant cannot hold over any table that is
not completely full and completely linked.**

**And the second encoding settled the question the first left open.** Gate 2's closing note
proposes the repair — *"`cdt_wohlgeformt` needs `forall s in used slots of c`"* — as an open
item. Measured:

* the `used`-guarded invariant IS satisfiable (`sat`, 0.07 s) — so the repair is livable;
* **but `L05` is STILL refuted under it** (`sat`, 0.14 s). `unlink` *requires* `used` and does
  not clear it, so it leaves a slot marked used with a cleared parent. ***`used` is not the
  right guard.***

The second encoder also found the sharpest form of the defect, and it needs no body at all:

> `unlink`'s `ensures c.slots[s].parent == None` **contradicts its own
> `maintains cdt_wohlgeformt`** for every `s != WURZEL`. The two clauses stand four lines
> apart in one signature.

*A defect visible in the signature was found by a solver and by nobody reading the file for
three weeks.* That is the best available answer to `GABBROV.md` §3's question about where
GabbroV would earn its keep.

### 1.4 `L01` — refuted twice, and the second encoding SPLITS the missing premise in two

This is the row where the two hands diverge most, and the second one is right.

| | first (`messung/gabbrov/L01*.smt2`) | second (independent) |
|---|---|---|
| `cdt_wohlgeformt` in the base | no — added in a third run (`L01c`) | **yes, in the base**, encoded as a rank function |
| degeneracies forbidden | none | **all** — no self-pointers, `t != s`, no post-state self-loop |
| base verdict | **sat**, 0.021 s | **sat**, 0.022 s |
| «B14» as a premise | one premise, flips to `unsat` (`L01b`) | **two directions, measured separately** |
| encoding-soundness control | none | **goal asserted POSITIVELY is also `sat`** |

**The verdicts agree. The reason does not, and the second is finer.**

*The first encoding treats «B14» as one thing.* The second put each direction to the solver
on its own:

| candidate premise | verdict | is it «B14»? |
|---|---|---|
| forward mutuality `slots[u].next == Some(n) => slots[n].prev == Some(u)` | **`unsat`**, 0.018 s | yes |
| **backward** mutuality `slots[u].prev == Some(p) => slots[p].next == Some(u)` | **`sat`** (ground at N=3, 0.021 s) | yes |
| siblings share a parent `slots[u].next == Some(n) => slots[n].parent == slots[u].parent` | **`unsat`**, 0.019 s | yes |

**Only ONE direction of the mutual sibling chain is load-bearing**, and a third, different
«B14» statement repairs the row by a shorter route. *The first encoding's `L01b` says "the
premise that repairs `L01` is exactly the one premise the language cannot express, and no
other". The second says: there are at least two such premises, they are not the same
statement, and one half of the one the first named does not repair it.* The conclusion
survives — every repair is «B14» — but the sentence "and no other" does not.

**And the second counterexample is better than the first.** The first encoding's model gave a
slot its own parent, which is why `L01c` exists at all. The second forbade every degeneracy
*and* carried `cdt_wohlgeformt` from the start, and is still `sat` at N = 3:

> Slot 0 is `WURZEL`. Slot 1 is being unlinked, with `prev = Some(2)` and `next = Some(0)`.
> The body's line `c.slots[n].prev_sibling = c.slots[s].prev_sibling` writes `Some(2)` into
> **slot 0's** `prev_sibling`. **The root has acquired a predecessor** — at a slot `unlink`
> never meant to touch as a root.

*A counterexample that survives `cdt_wohlgeformt` and every non-degeneracy constraint is a
different quality of evidence from one a reader can dismiss as nonsense.*

**One more thing this run produced without being asked for it, and it corroborates §2.3.**
Two of its files came back `unknown` at the 60 s cap — the quantified forms (c) and (e) — and
it settled them by **grounding at N = 3**, where they answer in 0.021 s. *A hand that had
never heard of the reachability wall hit it, diagnosed it as the quantified encoding, and
worked around it the same way.*

### 1.5 So which of the three readings is it?

**The corpus.** Not the obligations, not the specifications, not the encoding:

* **not the encoding** — two rows were re-derived by hands that had not seen the first, in
  representations that share no design decision, and both landed on the same verdict. Both
  second encodings carry a **control that comes back with the opposite answer**, which the
  first encodings did not have. An encoding that says `sat` to everything is ruled out by
  measurement rather than by care.
* **not the specifications** — `L40`'s and `L05`'s Lean `Prop`s were read straight out of
  `V1.lean` by both hands. The disagreement is not about what the obligation says.
* **the corpus** — «B26» is a transition table with no edge to `0`; `cdt_wohlgeformt` is an
  invariant no non-full table satisfies. Both are defects in `messung/fragmente/`, and both
  were found in under 30 ms.

**Said plainly, as the mandate asks: this is a good outcome.** A tool whose purpose is to
find exactly this found three of five drawn blind, and two independent hands confirm two of
them. *The Gate 2 number is not void; it is better witnessed than when it was reported.*

