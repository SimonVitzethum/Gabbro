# MUSE-REPORT-347: Organisation plan C3 — CostSummary

Lane 347, reviewed direction, reviewer lane 385. Branch `muse/347`.

## What was done

New file `grammatik/Grammatik/X86/CostSummary.lean` (371 lines) plus one
additive import at the end of `grammatik/Grammatik.lean`. Nothing else
touched: no source checker, Spec, goal, Typen, Rust, emitter, docs, or
friend-reserved paths.

Cost-summary SCHEMA per FLOAT-ZEIT §8.1 (all names provisional schemas,
generic over every source text):

- `StepClass` (11 source step classes: leaf, branch, lockOp, callOp,
  traverse, retryTry, foreverPass, floatOp, fenceOp, spillOp,
  casAttempt) and `alleKlassen` enumeration.
- `targetWork : List Befehl → Nat` skeleton (`length`): retired target
  instructions per segment. Spill/fence forms are not in the pilot
  `Befehl`; their counts live in the summary, never hidden here.
- `CostSummary`: per-class maxima `expand : StepClass → Option Nat`,
  actually-used `spillCount`/`fenceCount`, per-site `retryBound :
  Option Nat` (`none` = unbounded), waiting `exclusions`.
- `kostenSummeOk : CostSummary → Bool`: validator/profile admission.
- `alleMax` / `expandBound : CostSummary → Nat → Option Nat`: the
  summary bounds lowered MACHINE work via the validated expansion over
  the source budget (`src * max + spill + fence`), `none` while any
  class is unbounded. Never a source-budget stop claim.
- `klassenKosten`: declared-op reading of a class maximum, tying the
  schema to `Budget.totalCost` (one declared `Op` per expanded
  instruction, P1 style).
- `budgetSimulationOffen`: OPEN obligation schema (machine work to
  `passes`-budget exhaustion), STATED, never derived by re-summing.

## Proved (no `sorry`/`admit`/`axiom`/`native_decide`; every premise used)

- `totalCost_replicate_one`, `klassenKosten_total` (Budget tie),
  `targetWork_add` (segment additivity).
- Refusals, all with used premises: `kostenSummeOk_verweigert_unbegrenzt`
  (unbounded retry behind a constant bound refused),
  `kostenSummeOk_verweigert_ohneQuelle` (exclusion without source
  correspondence refused), `kostenSummeOk_verweigert_spin` (CAS-spin
  exclusion refused unconditionally).
- `alleMaxAux_gilt`, `alleMax_gilt`, `expandBound_gilt` (bound exists
  over any `src`, in particular a `kostenTiefF` value),
  `expandBound_keinVerlust` (spill/fence added in full).
- Concrete leaf facts: `blattSummary_ok`, `blattSummary_beschraenkt`,
  `blattExpansion_zaehlt` (= 3), `blattExpansion_imRahmen`,
  `blattKosten_drei`, `blattSummary_schranke` (`expandBound _ 1 = some 5`).
- `kostenExpansion_zeuge`: JOINT witness on `eP`/`eD` — reached run,
  start slot 0, `eSetze` writes `konto` (`rfl`), entry world slot 5,
  log membership, `ReqAmEintritt`, admitted summary, counted
  3-instruction leaf expansion inside its class maximum, and a work
  bound over `kostenTiefF eP … 0 1 eSetze`. Non-degenerate:
  table-writing program, memory-changing run.

Axioms: every theorem depends only on subsets of `propext`,
`Classical.choice`, `Quot.sound` (witness inherits the fixture
footprint); `#print axioms` lines are in the file.

## Checks

- `./lean-probe grammatik/Grammatik/X86/CostSummary.lean`: 0 errors.
- `./lean-bau`: green, 386 jobs, build completed successfully.
- `gabbro_ziel` axiom probe (`BeweisAtomar.lean`): still exactly
  `[propext, Classical.choice, Quot.sound]`.

## What remains OPEN (CUTS in file)

Refinement relation instance (decoder/bridge lanes), per-form maxima
proofs (backend-declared, Bool-checked), per-site exclusion proofs
(positive correspondence), `budget_simulation` derivation, cycle bounds
(DEFERRED), no duplicated `Befehl` evaluator, no checker change.

## Reading corrections applied

- Refusal Bool is admission, not a hardware fault (docstrings).
- CAS retry unbounded: no constant, no exclusion, attempt bound required.
- No re-summing: `expandBound_gilt` concludes a work bound only; the
  admission premise was REMOVED from it after the linter flagged it
  unused — existence needs boundedness alone, admission gates USE
  (stated honestly in the docstring, reviewer please note).
- One genuine finding: none — plan symbols resolved against source
  (`Op.cost`/`totalCost` in `Budget.lean`, `kostenTiefF` in `KostenG`,
  14-form `Befehl` in `X86.Typen`, `ziel_ort_einfaden_zeuge` fixture);
  no invented source behaviour.
