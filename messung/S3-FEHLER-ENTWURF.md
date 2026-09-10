# S3 error draft: from silent stuck to named faults

Status: draft. No code changed. Question from `dokumente/PLAN-SICHERHEIT.md` section on
S3: two silent classes (an index outside its range, a store outside its declared
width) currently reach a value or a bare `stuck` in the model, and the safety
theorem therefore says nothing distinguishing about them.

## 1. Current shape

`programmlogik/Gabbro/Body.lean` today:

- `eval : State -> Expr -> Option Value`, with `none` meaning stuck.
- `inductive Outcome` with `running`, `returned`, `exited`, `left`, `stuck`.
- The `.place` arm of `eval` reads `s.world (.slot c k f)` for any integer `k`
  with no check against `0 ..< count c`; an out-of-range index reaches a value.
- A zero denominator and a negative bit operand return `none` (stuck), so the
  model stops but does not name the reason.
- `exec_sicher` has the shape `exec = stuck -> Logik`: stuck implies own logic.

Finding stated in the plan: add an outcome the semantics reaches when an index
leaves its range or a store leaves its declared width, so that `exec_sicher`
becomes stuck-or-fault implies own logic, and the index class becomes a theorem
instead of a checker property.

## 2. Design A: fault enumeration on `Outcome` (primary)

Add a fault class enumeration beside the existing outcomes:

```lean
inductive Fehlerklasse where
  | index
  | ueberlauf
  | nenner
  | gestalt
```

and one more `Outcome` arm:

```lean
  | fehler (k : Fehlerklasse)
```

Semantics changes, per site:

- `eval` keeps its type; the range check lives where the carrier is known.
  The `.place` arm (and the `.assign` path through `store`) compares `k`
  against the table count and yields `fehler .index` outside
  `0 ..< count c`. Width stores yield `fehler .ueberlauf` outside the declared
  width. The zero-denominator arms yield `fehler .nenner` instead of `none`.
  Shape mismatches that are stuck today yield `fehler .gestalt`.
- `evalAll`, `step`, and `exec` propagate a fault unchanged: a fault is
  neither merged into `stuck` nor recoverable by a later statement.
- `finalState` maps `fehler` to `none`, as it does for `stuck`; only `stuck`
  has no post state today, and a fault has none either.
- `exec_sicher` becomes `(exec = .stuck \/ exists k, exec = .fehler k) ->
  Logik`, with the existing proof cases kept and one propagation lemma per
  combinator (`evalAll`, `step` sequence, loop iteration).

Fault table (checker column names the pass that carries the class today):

| class | site today | new outcome | checker keeps |
|---|---|---|---|
| index out of range | `.place` read, `.assign` store | fehler index | M103 refuses statically; model names the dynamic remainder |
| store outside width | narrowing store | fehler ueberlauf | M104 for the four proved operators; open for the rest |
| zero denominator | `.div` and `.rem` | fehler nenner | M102, already proved on the checker side |
| wrong shape | match arms, option arms | fehler gestalt | D005, M123 and the N passes |

## 3. Design B: second evaluator `evalF` (cheap alternative)

If `Body.lean` may not move (see section 7), keep `eval`, `step`, and `exec`
untouched and add a second evaluator beside `eval` that carries the fault:

```lean
def evalF (s : State) : Expr -> Except Fehlerklasse Value
```

with exactly one theorem:

```lean
theorem evalF_agrees : evalF s e = .ok v -> eval s e = some v
```

Consequences of this shape:

- The falsifier of section 6 becomes statable without touching any induction:
  `evalF` reports `.error .index` where `eval` reaches a value.
- The safety theorem stays `stuck -> Logik`; the fault story is a separate
  lemma, not part of `exec_sicher`.
- Cost: two evaluators over the same expression language that must be kept in
  step by hand; every new `Expr` arm needs both, and the agreement proof is
  the only thing holding them together.

Prefer design A when the coordination of section 7 is available; prefer design
B as a measurement scaffold before that, or if the shared file is frozen.

## 4. Consequences of Finding 1 and Finding 2

Finding 1 (fault outcome): the index class moves from a checker property to a
model theorem. `M103` and `schluss_sicher` stay where they are and keep
refusing statically bad indices; what changes is that the dynamic remainder is
no longer silent. A program the checker accepts but that indexes outside at
run time reaches `fehler .index` instead of an unconstrained value, so the
safety sentence covers it by name.

Finding 2 (`Shape.opt` range): the option shape needs a range, either a fixed
one on `Shape.opt` or a bounded form `Shape.optIn lo hi`. Without it, the
boundary between `absent` and `present` cannot be checked at the fault site,
and the `gestalt` arm would rest on a convention rather than a declaration.
This is a precondition of design A for option-typed slots, and of design B for
the `evalF` arms over `.someOf` and `.onOption`.

Untouched: `passlogik` Fund 1 (V2 replace versus intersect) and Fund 2 (E008
compares the kind, not the effect) concern the checker passes, not the model
outcomes, and neither design changes their statements.

## 5. Gift falsifier specification

The plan names the falsifier: `beispiele/gift/` files that index outside must
reach `fehler .index` under `exec`, where today they reach a value. Draft
acceptance shape:

- Each named file evaluates under `exec` to `.fehler .index` (design A) or to
  `.error .index` under `evalF` (design B). A file that reaches any value, or
  bare `stuck`, fails the falsifier.
- Minimal pair: `beispiele/gift/33-index-ueber-tabellenrand.gab` (index type
  `0 .. 127` against `count 64`, expects `M103`) and
  `beispiele/gift/647-an-index-into-an-empty-table.gab` (`count 0` indexed
  with `0`). Both are checker refusals today; the falsifier asks the model to
  reach the fault for the same shapes.
- The falsifier is per file and non-aborting: every named file is evaluated
  and reported, so one passing file never hides another failing one.
- Until the fault arm exists, the recorded outcome is the negative one: the
  files reach a value. That negative record is the baseline the build must
  flip, not a passing test.

## 6. O1 big-step coordination note

`dokumente/OFFEN.md` O1 records that `exec` is big-step and that the Isabelle
proofs rest on exactly that shape. Adding an `Outcome` arm touches every
induction over `step` and `exec` (sequence, loop iteration, coverage cases),
so design A must land as one coordinated change: the `Body.lean` edit and the
proof updates move together, and no lane edits the induction principle alone.

What is NOT proposed: a small-step or trace semantics. O1 names that as the
thing that would close the four listed obligations, and the stop-list keeps it
out. The fault arm stays inside the big-step shape: it names how a descent
ends, alongside `stuck`, without introducing an intermediate state.

Design B exists for exactly this constraint: while coordination is pending,
`evalF` measures the fault classes without moving the shared induction.

## 7. Open points and non-goals

- The enumeration above ends open (`gestalt` covers shape; further classes are
  added by need, not by anticipation).
- The `ueberlauf` row inherits the plan's Finding 5 split: four operators are
  carried, the rest are open, and the fault arm must not claim more.
- Frame, effect, rank, alias, race, termination, phase, and refinement rows of
  the plan's table are outside this draft; the fault arm changes none of
  their statements.
- No checker rule is removed or weakened here; the checker keeps refusing
  statically, the model names the dynamic remainder.
