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

## Response to review lane 1176 (REPAIR, apparatus-directed)

MUSE-REPORT-1176 records verdict REPAIR explicitly addressed to the review
apparatus, not to these proofs: no author file was observable from that
lane (candidate absent from its worktree, no working shell), so it contains
no finding for or against any theorem above. There is therefore no theorem
defect to repair, and none was manufactured: the Lean files are unchanged
by this update (report-only change).

Author-side verification performed for this response (all in this clone):
- HEAD is exactly the pinned candidate `eddf71c3` on `muse/1175`, tree
  clean; the 1176 snapshot values (author, HEAD, base `062b979a`, the same
  three files) match this clone exactly.
- Diff against base `062b979a`: exactly the three owned files, 787
  insertions, 0 deletions; `Grammatik.lean` change is the single appended
  import line (verified by diff).
- Banned tokens: grep for `sorry|admit|native_decide|sorryAx|unsafe|^axiom`
  over `PipelineInfinite.lean` finds nothing.
- Premise use: every premise of every new theorem is consumed by its proof
  (checked by reading each proof; no `intro _` / `have _ :=` anywhere,
  verified by grep); no conclusion restates a premise; `ρ` is always the
  concrete environment at actual values, never quantified away.
- Witnesses are joint and non-degenerate (`pwSrc` writes two slots; source
  runs change memory 7 -> 35 / 9 -> 6; target runs are computed, including
  the 12-step run to the code end).
- No silicon facts are stated anywhere in the new file (no encodings, no
  extension/flag claims); the machine is reused unchanged.
- Fresh `./lean-probe grammatik/Grammatik/X86/PipelineInfinite.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (axioms as listed above).
- Fresh `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (608 jobs)`.

Suggested dispatch fix (unchanged from 1176): hand the reviewer the pinned
HEAD with candidate access in the same step instead of scheduling the review
while the author lane is still working.

## Response to second review round (lane 1176 on snapshot 5d9d800a)

The updated MUSE-REPORT-1176 (candidate `5d9d800a`) repeats the verdict
REPAIR with the same scope note: addressed to the review apparatus, still
no finding for or against any theorem, candidate still unobservable from
that lane, still no shell there. Again there is no theorem defect to
repair, so again no Lean change was made and no guarantee weakened
(report-only update).

Author-side verification repeated against the new snapshot:
- HEAD is exactly `5d9d800a38843cb83de734fe78f3f8f850191009` on
  `muse/1175`, tree clean; snapshot values (author, HEAD, base,
  file list) match this clone.
- Diff against base: exactly the three owned files, insertions only.
- Fresh `./lean-probe grammatik/Grammatik/X86/PipelineInfinite.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- Fresh `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (608 jobs)`.

The 1176 checklist (banned tokens, axioms, premise use, witness quality,
CUTS honesty, silicon facts) was executed author-side in the previous
round with clean results (see section above); the Lean files are byte
identical since, so those results carry over unchanged.

Co-Authored-By: muse-agent-1175 <muse-agent-1175@noreply.invalid>
