# MUSE-REPORT-1175: Finite and infinite execution soundness of the pipeline

Clone: `/home/simon/Dokumente/gabbro-muse/a1175`, branch `muse/1175` (verified).
Owned files only: `grammatik/Grammatik/X86/PipelineInfinite.lean` (new),
`grammatik/Grammatik.lean` (one appended import line), this report.
No existing file was otherwise touched; `OptimizationRules.lean` /
`OptimizationWitnesses.lean` untouched; no second IR, no second source
interpreter, no per-program rule. Rust out of scope (none touched).

## What was built

New file `grammatik/Grammatik/X86/PipelineInfinite.lean` (~660 lines),
reusing accepted definitions unchanged (`senkBlock_korrektC`,
`senkBlock_ausgang`, `validate_sound`, `Entspricht`, `CodeAt`,
`WorldRep`, `LayoutSep`, `EnvRepr`, `ByteRahmen`, `laufBytes_rahmen`,
`codeAt_lauf`, `laufBytes_add`, `execStmt_ite`,
`execBlock_cons_stmtOk/Grund`, `constInt?_sound`, all `pw*` witness data).

Definitions (new):
- `BudgetAusgang` (`fertig` / `stopp`): outcome of a budgeted byte run.
- `laufBudget : Nat → Zustand → BudgetAusgang`: the target-side budget
  semantics (at most `n` byte steps; `stopp` on a defined stop).

Theorems (new), each with `#print axioms` (all standard: machine-level
ones `[propext, Quot.sound]`, the rest `[propext, Classical.choice,
Quot.sound]`):
- `laufBytes_praefix_erfolg`: every prefix of a successful run succeeds.
- `laufBytes_verweigert_plus`: a refused run stays refused under fuel.
- `laufBudget_fertig`: `fertig k s'` iff `k = n` and the plain run succeeds.
- `laufBudget_stopp`: `stopp k s'` gives `k ≤ n`, a successful `k`-prefix
  and a transition-less prefix state.
- `laufBudget_stopp_stabil` (refusal theorem): a stop is sticky under more
  fuel; the runner refuses to step past a stop.
- `laufBudget_fertig_von` (converse, for the positive probes).
- `praefix_sicher` (SAFETY OF EVERY PREFIX): a validated block reaches its
  `Entspricht` end state, and every prefix succeeds with code region and
  memory frame intact. Mid-run states deliberately get no source meaning.
- `erste_stop_ordnung` (BUDGET-STOP ORDERING): a stop at step `k` satisfies
  `n ≤ k`; at `k = n` it is the corresponding end state. Before `n` the run
  always continues.
- `budget_unabhaengig`: a lowered block runs the same at every budget
  `passes` (induction mirroring `senkBlock_ausgang`; the fragment has no
  loops/calls, so `passes` is threaded but never consumed).

Witnesses (joint, on non-degenerate `pwSrc`: two slots written, source run
changes memory 7 -> 35 and 9 -> 6):
- `praefix_sicher_zeuge`, `erste_stop_ordnung_zeuge`,
  `budget_unabhaengig_zeuge`.
- Helper `laufBytes12_stop`: the computed 12-step run ends at the code end
  (rip 4178) with no transition (via a decidable 13-step observation plus
  `laufBytes_add`, since `ByteAusgang` equality itself is not decidable).

Probes:
- `gift_stopp_ist_stopp`: tampered memory (`pwMemFalsch`) stops the
  budgeted runner at step zero.
- `gift_fertig_laueft`: the honest 5-step prefix runs clean.
- `gift_budget_kein_stopp_im_code`: the honest 12-step run finishes its
  budget and ends at the code end (no early stop on accepted programs).

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineInfinite.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `exit 0`, `Build completed successfully (608 jobs)`.
  (One first attempt failed with `failed to create thread` (exit 134) while
  building `PipelineInfinite.olean`: transient resource contention, not a
  proof failure; immediate retry was green.)
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.
- Every premise of every new theorem is used by its proof.
- Commits on `muse/1175`: `c455b05c` (skeleton), `28296b5d` (budget
  runner), `dd732b4c` (prefix + ordering), `117096e7` (budget
  independence), `5df87940` (witnesses/probes/CUTS). This report is the
  remaining commit.

## What remains open (see CUTS in the file)

Termination of the target run beyond what `senkBlock_korrektC` gives per
validated program; infinite traces past the corresponding end; behaviour
past the end (needs the image stop premise of `PipelineImage`, cited but
not re-proved — stops with `k > n` are unclaimed at pipeline level);
per-step source correspondence (no source small-step exists by design);
progress/fairness (sequential single-core model); all inherited
`Pipeline.lean` fragment limits (pilot ISA, integer slots, no loops/calls,
no TSO, no time).

## Where the result is weaker than the task text, stated plainly

1. The task asks for "a correctness theorem in the style of
   `pipeline_correct_entry` (source `execBlock` result related to the
   byte-level run on the loaded image)". I did NOT add another loaded-image
   closing theorem: that would need `imageOk`/`weltOk` premises whose joint
   witness (`valX86` over a full `Bild`) is not buildable from the
   `PipelineWitnesses` data, so its `_zeuge` would fail the inhabitation
   rule. Instead the new validator is the target-side budgeted runner
   (`laufBudget`) over the pipeline-level runs, with correctness
   (`fertig`/`stopp` correspondence, prefix safety, first-stop ordering)
   and refusal (`stopp` stability, no stop before the corresponding end)
   theorems, plus the source-side budget theorem. The loaded-image
   composition is left to `PipelineImage`'s closing theorems, which this
   file reuses but does not duplicate.
2. "Every finite prefix corresponds to a source prefix or a budget stop":
   prefixes strictly inside the run are proved SAFE (success + code +
   frame), not source-corresponding — a half-executed assignment chunk has
   no `execBlock` meaning, and inventing one would be a second interpreter
   (forbidden by decision 594). Correspondence holds at the end
   (`Entspricht`); budget stops provably do not exist on either side for
   accepted programs (`budget_unabhaengig` + `pipeline_ausgang`).

## Findings for the coordinator

- `by_contra` does not resolve anywhere in `grammatik/` (zero uses in the
  whole X86 tree; `subst`/`cases`/`by_cases`/`omega` are fine). Proofs here
  use the `by_cases` pattern instead. If a lane needs classical
  contradiction, it must go through `by_cases`/`Decidable.em`, not
  `by_contra`.
- `obtain`/`cases` patterns: a cleared (`-`) existential whose variable
  appears in a later conjunct's type breaks the later bindings (met with
  `code`/`ht` from `senkBlock_ite_inv`). Name every existential that
  later types mention; mirror `senkBlock_ausgang`'s exact pattern.
- The `decreasing_by` of `budget_unabhaengig` needs the full
  `Block.cons/pruefung/Stmt.ite.sizeOf_spec` simp set (the
  `unusedSimpArgs` linter warning on `Stmt.ite.sizeOf_spec` is misleading:
  removing it breaks the `t`/`e` goals).

Co-Authored-By: muse-agent-1175 <muse-agent-1175@noreply.invalid>
