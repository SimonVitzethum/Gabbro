# MUSE-REPORT-385: Independent exact-candidate C3 review of 347 CostSummary

Lane 385, reviewer of author lane 347. Clone `/home/simon/Dokumente/gabbro-muse/a385`,
branch `muse/385` verified. Own only this report; candidate staged privately
(owned module + additive import), probed, built, then fully restored before this commit.

## Candidate

Author short HEAD from build evidence: `41306b43` (full 40-char hash not present in
this isolated clone; `muse/347` branch not fetched here). Reviewed exact snapshot
`.tmp/review/author-347`: `grammatik/Grammatik/X86/CostSummary.lean` (371 lines),
one additive import at end of `grammatik/Grammatik.lean`, `MUSE-REPORT-347.md`.
PATCH touches nothing else: no checker, Spec, goal, Typen, Rust, emitter, docs,
or friend-reserved `OptimizationRules`/`OptimizationWitnesses`.

## What was checked

- Read the full candidate file against actual sources in this clone: `Budget.lean`
  (`Op.cost`, `totalCost`), `KostenG` (`kostenTiefF`), `X86.Typen` (14-form `Befehl`,
  `Register` with `.rax`/`.rcx`/`.rdi`, `Wort := BitVec 64`), fixture
  `ZielOrtEinfadenZeuge` (`ziel_ort_einfaden_zeuge`, 4-step reached run with write).
  All plan symbols resolve; no invented source behaviour found.
- Forbidden-tactic scan (word-boundary grep for `sorry`/`admit`/`native_decide`/
  `unsafe`, leading `axiom`): zero hits (`admit` substring hits are the English
  word "admitted").
- Premise-use audit of every theorem: all premises used in proofs. No `Prop`-typed
  premise. No conclusion restating a premise. No quantified-away contract: the
  witness carries `ReqAmEintritt eP ePruefe w0 rho` at actual entry values.
- `targetWork` is `List.length`, documented as skeleton, never called a semantics.
  No duplicated `Befehl` evaluator in the file. No source admission tightened.
- Staged privately and executed: `./lean-probe .../CostSummary.lean` -> 0 errors;
  `./lean-bau` -> green, 387 jobs (386 author-side + 1 for this base's extra module);
  `BeweisAtomar.lean` probe -> `gabbro_ziel` still exactly
  `[propext, Classical.choice, Quot.sound]`. Candidate axioms all standard subsets.
  Tree restored afterwards (`git status` clean, import tail verified).

## Findings

No material defect. Specifically confirmed:

- Three refusals proved with used premises: unbounded retry behind a constant
  bound (`kostenSummeOk_verweigert_unbegrenzt`), exclusion without source
  correspondence (`_ohneQuelle`), CAS-spin exclusion unconditional (`_spin`).
- `budgetSimulationOffen` is STATED as a `Prop`-valued schema over admitted
  summaries, inhabited by no theorem, never derived by re-summing. Honest OPEN.
- `expandBound_gilt` concludes a work-bound existence only; the author documents
  that the admission premise was removed after the unused-variable linter flagged
  it (existence needs boundedness alone, admission gates use). Correct scoping,
  plainly stated, not a hidden weakening.
- Joint witness `kostenExpansion_zeuge` reuses the proved `ziel_ort_einfaden_zeuge`
  fixture: table-writing program (`eSetze` writes `konto`, `rfl`), memory-changing
  reached run (slot 0 -> 5), counted 3-instruction leaf expansion inside its class
  maximum, bound over the real `kostenTiefF` value. Non-degenerate.
- `blattExpansion` is a stipulated instruction triple, not a backend lowering;
  the file and CUTS say exactly this (backend-declared maxima, exhibition not
  lowering). Claim stays within its bound. Cycle bounds deferred, no timing claim.

## Verdict scope

ACCEPT covers only the precise bounded delivered obligations: the ESSENTIAL
cost-summary schema, its validator Bool with three proved refusals, the Budget
tie, segment additivity, the counted leaf expansion with honest spill/fence
counts, and the OPEN-stated (not derived) simulation obligation. Not a full
compiler, validator, lowering, or hardware correspondence claim.

CANDIDATE: 347 41306b43
VERDICT: ACCEPT
