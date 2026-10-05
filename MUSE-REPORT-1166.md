# MUSE-REPORT-1166: Exact review of candidate 1165 (pipeline source-budget to target work/time transfer)

## VERDICT: ACCEPT

CANDIDATE: lane 1165, HEAD `b0aef4880dd96fba84c165f392d983133a538c0c`
("Lane 1165: pipeline source-budget to target work/time transfer"),
base `062b979a`, snapshot clean, exactly 3 files.

## What was reviewed

The coordinator-supplied exact snapshot in `.tmp/review/author-1165/`
(`SNAPSHOT.json`, `PATCH.diff` — full 1053-line diff read end to end,
`MUSE-REPORT-1165.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, and the
pinned file copy `grammatik/Grammatik/X86/PipelineWork.lean`, cross-checked
against the diff). Files in the candidate:

- `grammatik/Grammatik/X86/PipelineWork.lean` — NEW, 952 lines.
- `grammatik/Grammatik.lean` — one appended line
  `import Grammatik.X86.PipelineWork`, nothing else.
- `MUSE-REPORT-1165.md` — NEW, author report.

## Gate checks (all pass)

1. **No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.** Full-text grep
   over the snapshot file and the diff: zero code occurrences. The only
   matches are prose ("admitted pipeline summary" = the family's own
   validator-Bool admission vocabulary, `kostenSummeOk`) and rule quotations.
2. **`#print axioms` standard.** Captured build output shows every theorem
   depending only on subsets of `propext, Classical.choice, Quot.sound`
   (`pipeSummary_ok`/`pipeSummary_max` on no axioms at all).
3. **Existing files untouched except one import line.** Diff file list is
   exactly the 3 owned files; the `Grammatik.lean` hunk appends one import.
   No checker/Spec/goal/emitter/friend-reserved file touched.
4. **Every premise used.** Traced all 12 main theorems: `hT` feeds the cast
   rewrite, `hflach` feeds agreement+classification, `hsrc` feeds the
   `omega` bound, ghost/stop premises are all forwarded to
   `ComposeBudgetResum_verbindung`, cost premises to the transfer theorem.
   No `intro _`, no `have _ :=`, no `forall rho`/`forall v` contract
   quantification, no new semantics (only reused `execBlock`/`laufBytes`).
5. **Family evaluator lifted, not copied.** Reused untouched:
   `senkStmt`/`senkWertT`/`senkWert`/`senkFrag_laenge`/`senkWert_als_tief`,
   `validate`/`validate_sound`/`pipeline_correct`, `arbeit_decodiert`,
   `budgetAusfuehrung_transfer`, `ComposeBudgetResum_verbindung`,
   `kein_freier_versuch`, and the `PipelineWitnesses` program/data. New
   definitions are only the `pipeSummary` `CostSummary` value (the
   deliverable) and the `PipePaket` Prop bundle. No second interpreter, no
   second cost model, no SSA IR. (`open ...OptimizationRules` is an unused
   import only; the reserved files are not edited.)
6. **Planted refusals really refuse.** Four poison probes, all by
   computation (`decide`/`rfl`): `gift_pipe_knapp` (bound 2 vs 5-instruction
   chunk), `gift_pipe_mul` (`2*3` has no lowering), `gift_pipe_tief`
   (depth-two addition, empty scratch), `gift_pipe_retry` (retry bound
   removed refuses admission). Four matching refusal theorems close the
   shapes generically.
7. **Witness non-degenerate, joint everywhere.** `PipePaket`/`pipePaket_hold`:
   contract writes the table, source run moves slots 7→35 and 9→6 through
   real `execBlock` (memory-changing), fetched-byte run observably changes
   memory. A `_zeuge` exists for every syntax-premise theorem (12 of 12),
   each instantiating ALL premises jointly on this package. Two cores N/A:
   no concurrency claim is made (CUTS excludes TSO/W-GX).
8. **Silicon.** No silicon claim exists to check: `tt` counts NAMED per-form
   bounds from the selected profile, and CUTS explicitly disclaims silicon
   latencies, constant-time, CAS progress and fairness. No
   hardware-correspondence or W/GX claim. Honest.
9. **CUTS honest, claim = proof.** CUTS lists: fragment-only single shallow
   assignments (deeper trees/checks/loops/calls/floats/pointers/aggregates/
   globals refused, never guessed), no block-size induction, exhaustion
   timing with scheduling lanes, entry/image beyond `CodeAt` open, no
   TSO/concurrency. The proved statements match exactly these bounds.

## Build evidence

Author-clone captured runs, in order: `./lean-probe` 0 errors on the final
file; final `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
output`, `Build completed successfully (608 jobs)`. The committed `.lean`
is exactly what built green (evidence shows no unstaged changes between the
green build and commit `b0aef488`). One intermediate full-build run failed
with `lean::exception: failed to create thread` (job 606/608) and passed on
retry — documented by the author as resource exhaustion, consistent with the
known apparatus issue; the standalone probe was green throughout.

Own check (lane 1166 tree = master + this report only, no Lean changes):
`./lean-bau` last result line: `Build completed successfully (610 jobs).`
(610 vs the author's 608: master moved forward by two jobs since; my tree
adds no Lean code, so this confirms the base the candidate merges into is
green.)

## Method note

Shell execution was temporarily permission-denied in this review
environment; it was restored before finishing. The ACCEPT rests on the
complete exact diff plus the pinned-HEAD build evidence, confirmed by my
own green `./lean-bau` on the reviewer tree (see above); the serial merge
gate re-runs the build and the sorry-scan anyway. Report committed below.

## New definitions/theorems by lane 1166

None (report-only review lane; owns only `MUSE-REPORT-1166.md`).

## What remains open

Nothing for 1165. Follow-up scope stays where the candidate's CUTS puts it:
block-size induction, scheduling-side exhaustion timing, entry/image
admission beyond `CodeAt`, TSO/concurrency bridge, silicon latency fidelity.

## Task notes

Nothing in either task statement was wrong. The pinned-HEAD snapshot
procedure worked: exact candidate, complete evidence, reviewable offline.

Co-Authored-By: muse-agent-1166 <muse-agent-1166@noreply.invalid>
