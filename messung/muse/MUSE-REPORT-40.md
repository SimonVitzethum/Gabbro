# MUSE-REPORT-40: Sequential Hoare rules over execBlock (lane 40)

## What I did

New file `grammatik/Grammatik/HoareRegeln.lean` (~1540 lines), wired via
`import Grammatik.HoareRegeln` at the end of `grammatik/Grammatik.lean`.
No existing file was modified except that one import line; no existing
definition or theorem was touched. `./lean-bau` is green
(`Build completed successfully (34 jobs)`, `== 0 error line(s)`).

## Design

- `HTripel O passes R b Pre Post` / `STTripel ... s ...`: partial correctness
  over the actual sequential semantics. For every world `σ` and environment `ρ`
  with `Pre σ ρ`, if `execBlock O passes R b σ ρ` (resp. `execStmt`) ends
  normally (`.ok σ' ρ'`), then `Post σ' ρ'`. Pre/post are predicates over the
  actual world AND environment; nothing is quantified over environments.
- `StmtOhneRuf` / `BlockOhneRuf` / `EndOhneRuf` / `ArmsOhneRuf` /
  `GrundArmsOhneRuf`: call-freedom predicates over the `Block`/`Stmt`
  constructors. `call`/`callInd` statements and
  `bindCall`/`bindCallInd`/`bindCallElse` block spines are excluded (no such
  constructors); nested blocks (branches, lock bodies, loops, breaking) must
  preserve the property. Oracle/hardware leaves (`axiomCall`, registers,
  transitions, publish/awaits) stay allowed: they are not calls.

## Theorems (all green, axioms `[propext, Classical.choice, Quot.sound]`, no sorry)

- `hoare_skip`, `hoare_assignVar` (backward/substitution),
  `hoare_assignVar_fwd` (forward), `hoare_seq`, `hoare_ite`,
  `hoare_konsequenz`, `hoare_konsequenz_stmt` — proved directly over
  `execStmt`/`execBlock` equations.
- `stmtOhneRuf_Runabhaengig`, `blockOhneRuf_Runabhaengig`,
  `endOhneRuf_Runabhaengig`, `armsOhneRuf_Runabhaengig` — on call-free code the
  executor never consults the call-meaning parameter `R`.
- `traverseKey` / `retryKey` / `foreverKey` — standalone R-independence of the
  loop executors (`traverseLauf`/`retryLauf`/`foreverLauf`), taking block
  equality as a hypothesis; proved by induction on the index list / counter.
- `grundArmsOhneRuf_RunabhaengigAux` / `grundArmsOhneRuf_Runabhaengig_end` —
  R-independence for `execGrund`, by `Nat.rec` on the arm index.
- `armsOhneRuf_RunabhaengigAux` — one-arm peeler for `execArms`.
- `hoare_Runabhaengig` — triples over call-free blocks hold for every `R`.

## Key technical findings (for the next lane)

1. A `mutual` tactic block over the four derivations does NOT pass Lean's
   termination checker (`fail to show termination`), even with binders before
   the colon, eta-expanded self-calls, or `termination_by` hints. Bisection
   showed the check is non-monotone under `sorry`-stubbing, so stub-bisection
   results are unreliable; the robust fix is to avoid `mutual` entirely.
2. The working shape: prove the four equations by direct application of the
   generated mutual recursor (`StmtOhneRuf.rec` / `BlockOhneRuf.rec` / ...),
   with motives `fun x _ => ∀ σ ρ, Eq-at-x` so every induction hypothesis is
   already universally quantified over world/environment. Each of the four
   theorems repeats all 48 minor premises (25+13+6+2+2); the file was generated
   by script (`.tmp/emit2.py`, kept outside the repo tree in scratch).
3. Two recursor-specific pitfalls, both fixed in the final file:
   - Minor-premise case binders bring FRESH indices; bodies must not reference
     outer theorem indices (`σ.lese Λ` → `σ.lese _`, and `split`/`next` instead
     of `cases`/`by_cases` naming world-read discriminants).
   - Recursor IH binders follow CONSTRUCTOR proof-argument order, not the order
     of a hand-written hyps list: for `regLiesElse`/`narrow`/`pruefung`/
     `gleitNarrow` the order is `(he hr)`, not `(hr he)` (found via `#check`
     on the recursor; symptom was swapped `ihr`/`ihe` types).
4. `onGrund` needs no general call meaning: the recursor's `motive_5` IH
   (`iha`) proves the grund arm directly; the standalone `grund_*` lemmas are
   kept for the direct `execGrund` statement.

## Last `./lean-bau` result line

`Build completed successfully (34 jobs).` with `== 0 error line(s) in the
COMPLETE output`. `./lean-probe grammatik/Grammatik/HoareRegeln.lean` reports
`== 0 error(s)`.

## What remains open

- No while-rule and no frame rule: both need loop invariants / frames over
  shared carriers, i.e. the interference fragment — out of scope for this lane.
- Loop R-independence covers the executors only; Hoare-style loop rules with
  user invariants are future work on top of these triples.
- The generated-file workflow (`.tmp/emit2.py`) is scratch-only; anyone
  editing a minor premise should re-check with `./lean-probe` immediately.

## Task assessment

Nothing in the task statement looks wrong. The five required rules (skip,
assignment, sequence, if-then-else, consequence) are all proved over the real
semantics with pre/post over actual world AND environment, plus the
call-freedom predicate and R-independence. The result is not weaker than asked.
