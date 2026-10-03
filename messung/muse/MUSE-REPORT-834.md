# MUSE-REPORT-834: Composition closing — budget-resumption closing

## What was done

Closed the source-budget-exhaustion to target-work-spent interface with an
explicit ghost source-budget correspondence, by composing already-accepted
modules only. New file `grammatik/Grammatik/X86/ComposeBudgetResum.lean`
(+ import line in `grammatik/Grammatik.lean`); no other file touched.

Producer/consumer interface closed: source budget exhaustion
(`Budget.runOps` over-budget head via `BudgetExecution.stoppReihenfolge`)
to target work spent (`CostSummary.expandBound`/`targetWork` via
`BudgetExecution.Deckung` and `budgetAusfuehrung_transfer`), with the
ghost (`GhostBudget`: ghost tracks the source budget exactly) and
resumption (larger source budget preserves coverage, from the accepted
expansion formula `expandBound_keinVerlust`).

## Exact new names

- `def GhostBudget (s : CostSummary) (ghost src : Nat) (xs : List Decodiert) : Prop`
- `theorem expandBound_mono`
- `theorem deckung_resum`
- `theorem ComposeBudgetResum_verbindung`
- `theorem ComposeBudgetResum_verbindung_zeuge` (jointly inhabited,
  non-degenerate: table-writing program, reached run slot `0 -> 5`,
  memory-changing target run register/byte `0 -> 42`, both transfer
  bounds at `src = 1` and resumed `src' = 2`, both planted refusals:
  over-budget `fremdOp 3` names the source budget breach, refused `ret`
  head refuses the target aggregation)

No interpreter, executor, decoder or cost model duplicated; accepted
`lauf`/`laufKosten`/`targetWork`/`runOps` equations reused untouched.
No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files touched.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeBudgetResum.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (whole project): `Build completed successfully (509 jobs).`
- Axioms of new theorems: `GhostBudget` none; `expandBound_mono`,
  `deckung_resum`, `ComposeBudgetResum_verbindung` on
  `[propext, Quot.sound]`; `ComposeBudgetResum_verbindung_zeuge` on
  `[propext, Classical.choice, Quot.sound]` (via the reused reached-run
  witness). All within the standard goal axioms.
- `gabbro_ziel` family still exactly
  `[propext, Classical.choice, Quot.sound]` (lean-probe of
  `Zielsatz/BeweisAtomar.lean`, 0 errors).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise of
  every new theorem is used by its proof.

## What remains open (explicit CUTS in the file)

- Exhaustion TIMING stays OPEN (scheduling/IR lanes): when the target
  stops relative to source exhaustion, interleavings, waiting delays.
  The transfer bounds admitted finite prefixes only.
- Lowering correspondence stays carried data (`Deckung`): which source
  step lowers to which target segment comes from the lowering/IR
  producer (`DerivedWorkBound.deckung_fragment` derives it for the
  covered fragment; the generic IR is absent).
- No hardware cycle claim (named per-form bounds only, `ret` refused),
  no constant-time or CAS-progress/fairness promise.

## Task assessment

Nothing in the task appears wrong. The target statement was provable as
stated without added premises or weakened conclusion; the existing
`budgetAusfuehrung_transfer` already composed work to time, so this
lane adds exactly the ghost correspondence, the resumption leg and the
joint stopping order on top, with exhaustion timing left as the named
OPEN cut.
