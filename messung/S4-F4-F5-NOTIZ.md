# S4 seam findings F4 and F5 — design note

Status: design note, not a measurement. Nothing in this file was verified by
running anything; the commands that would verify it are listed in section 4
and were deliberately not run.

Context: the S4 seam compares two checkers routine by routine — `gabbro-check`
in Rust against the `schluss` / `pruefe` model in `programmlogik/Gabbro/`
(PLAN-SICHERHEIT.md, section 4). The F3 scope gap (index-into parameters
carrying `.int` where the model needs `intIn`) is already closed on this lane
(commit 648e049). What remains open are F4 (range formulas the checker
computes and the model drops) and F5 (branch refinement the checker performs
and the model lacks). Seam figures below are quoted from the plan status of
2026-09-10 (189 routines, 119 witnessed, 53 both-accept, 66 rust-only,
0 lean-only), not re-measured here.

## 1. F4 — range formulas in typen.rs versus arith returning .int

### 1.1 Shared preliminaries in the checker

All five functions live in `crates/gabbro-check/src/typen.rs` and share three
rules. First, `gemeinsame_form`: operands of different width or signedness
give an unknown range, unless one side is a literal, which adopts the other
side's form (the U10 rule). Second, `ergebnis`: the overflow flag is set
exactly when the computed interval leaves the machine width. Third, an empty
interval on either side yields unknown — from an empty range anything
follows, so it may carry nothing (this also covers the `5 .. 0` denominator,
which `enthaelt_null` treats as containing zero).

### 1.2 The five formulas

| case | checker function | result interval |
|---|---|---|
| division, dividend nonneg and denominator positive | teile | low = a.min / b.max, high = a.max / b.min |
| division, signed | teile | min and max over the four corners a.min/b.min, a.min/b.max, a.max/b.min, a.max/b.max |
| division, denominator empty or holding zero, or either side empty | teile | unknown, still accepted, no overflow flag |
| remainder, dividend nonneg and denominator positive | rest | 0 to min(b.max - 1, a.max) |
| remainder, signed | rest | neg bound to bound, with bound = max(abs(b.min), abs(b.max)) - 1 |
| remainder, same guards as division | rest | unknown, still accepted |
| bitwise and, both operands nonneg | bitweise Und | 0 to min(a.max, b.max) |
| bitwise or/xor, both operands nonneg | bitweise Oder/Xor | 0 to mask(max(a.max, b.max)), where mask is the smallest value of the form 2^k - 1 covering the input |
| any bitwise operation with a negative operand | bitweise | the full machine interval |
| shift left, amount within width | schiebe_links | min and max over a.min<<b.min, a.min<<b.max, a.max<<b.min, a.max<<b.max |
| shift left, amount negative or reaching width | schiebe_links | the full machine interval plus the overflow flag |
| shift right, value and amount nonneg, amount within width | schiebe_rechts | a.min>>b.max to a.max>>b.min |
| shift right, negative value or amount out of range | schiebe_rechts | the full machine interval, with the overflow flag exactly when the amount reaches the width |

### 1.3 What the model computes instead

`arith` in `programmlogik/Gabbro/Sicherheit/Ausdruck.lean` carries intervals
for addition, subtraction, and four-corner multiplication, then stops. For
division and remainder over two ranged shapes it returns `.int` when the
denominator excludes zero and refuses otherwise (M102). For the bit
operations and both shifts it returns `.int` when both lower bounds are
nonneg and refuses otherwise (M137/M104). With a rangeless number on either
side, addition and friends still give `.int` while division, remainder, bits,
and shifts refuse. So the model proves absence of stuckness (S4) and drops
every bound from the table above (Fund 5 in `Sicherheit.lean`).

### 1.4 Closing options

Option A: lift the five formulas into `arith`, returning `intIn` instead of
`.int`, one operator family at a time, each with decide examples mirroring
the `typen.rs` probes. Division goes first — it shares the M102 guard the
model already has. This requires pinning the corner semantics the checker
already assumes: truncating division including the min-int divided by minus
one overflow (flagged by the width check), remainder sign following the
dividend, shift-out-of-range flagging, and the mask function. Benefit: F4
disappears and the both-accept count rises. Cost: the work itself, plus a
second implementation of the same arithmetic that the seam must then keep in
agreement.

Option B: keep `.int` and record F4 as accepted imprecision with the M104
boundary named. Cost: a permanent rust-only wedge on every division-heavy
routine, and a finding count that can never fall on this axis.

Recommendation: option A, formula by formula, division first. The guard
structure already matches, so each step is small and each step is measured
by the seam count moving.

## 2. F5 — branch-refinement design (refine and join)

### 2.1 What the checker does

`fakten_aus` (`crates/gabbro-check/src/m1.rs`) refines the environment on
entry to each branch. Place against constant narrows the interval facts (V1,
`bereichsfakt`); place against place records a relation fact (V2,
`Beziehung`); float comparisons narrow float intervals. A conjunction gives
both facts in the then-branch; a disjunction gives both negated facts in the
else-branch. Negation needs a total order — the precondition is documented
at the function, NaN possibility blocks negation, and volatile places are
excluded (B33) because a second read may see a different value.

Scope discipline: each branch is checked under a clone, writes kill facts
(`geschriebenes_toeten`), and branch facts never escape to the outer scope.
The single exception is an if without else whose one branch always exits
(return, leave, diverging call): what follows it is exactly the negated
condition, so the outer scope is refined with it.

In short: refine equals condition facts into the branch scope; join equals
discard the branch scope and keep the outer scope minus killed writes, plus
negated-condition refinement after always-exiting branches.

### 2.2 What the model does

The `.ite` case (`programmlogik/Gabbro/Sicherheit/Anweisung.lean`) checks the
condition as boolean and both branches under the same environment, then
returns the outer environment. No refinement happens, so there is nothing to
join. The F5 gap — 11 instances plus probes — is the set of routines whose
checker acceptance rests on narrowing the model cannot replay.

### 2.3 Design

Carry a fact layer beside the environment: a mapping from names to
intervals, refined on branch entry from comparison conditions over integer
shapes (mirroring the comparison-to-interval mapping and its negation),
identity for non-comparison conditions and for float conditions. Each branch
is checked under its refined layer, so refined bounds can discharge index
and denominator checks inside the branch.

Join stays trivial: return the outer environment and discard the fact layer,
exactly mirroring the checker's cloned scopes. Bindings made inside a branch
must not escape — this holds today because `.ite` returns the outer
environment, and the design keeps it that way.

Refinement of the outer scope after an always-exiting branch depends on F1
(`endetMitAusgang` lacks arrow-never): without a divergence notion in the
model there is no sound trigger for keeping else-facts past the join.
Record F1 as the dependency, do not work around it.

Open points for the implementing lane: relation facts (V2, place against
place) need an encoding on the model side; volatile has no model
counterpart yet; loop interplay (U2, `SchleifenOK`) needs the fact layer
registered the same way the environment is.

### 2.4 Decide examples to add with the implementation

One example per comparison operator in both polarities showing the specified
refinement; the conjunction and disjunction polarity rules; float comparison
refining nothing; branch bindings not escaping the join; negated-condition
refinement after always-exiting branches, marked blocked on F1.

## 3. Verification commands (listed, not run)

None of these were run while writing this note. The implementing lane runs
them on the compute host under its own server directory, not locally:

- the checker suite with fail-fast disabled, from a clean tree
- the Lean build over `programmlogik/`
- the seam witness run: the ignored seam corpus emission driven by its
  source and output directory variables, then one Lean elaboration per
  witness file under a timeout
- `zaehle-pflichten.py` in hanging mode for the finding count
- the S5 guardian from PLAN-SICHERHEIT.md once it exists: zero sorry over
  the Sicherheit files, axiom output free of sorryAx, speech tests present,
  finding-count ratchet intact

## 4. Relation to the other findings

F1 is a dependency of the F5 join rule and stays open. F3 is closed on this
lane. F4 and F5 are designed here and stay open until implemented. F6, F7,
F8, F9, and F10 are unchanged by this note.
