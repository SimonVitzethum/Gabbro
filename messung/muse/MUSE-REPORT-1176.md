# MUSE-REPORT-1176: Exact review of lane 1175 (PipelineInfinite)

CANDIDATE: 1175 d018126b4e5a0253f1810e75eaba4a80eeb8ed47
VERDICT: ACCEPT

This report supersedes all previous lane-1176 rounds on older snapshots. Those
rounds recorded non-acceptance addressed to the review apparatus because no
candidate content was observable; per the corrected delivery (candidate as
files under `.tmp/review/author-1175/`) a full substantive review was now
performed, and no concrete defect in the candidate was found.

## Reviewed material

- `.tmp/review/SNAPSHOT.json`: author 1175, HEAD
  d018126b4e5a0253f1810e75eaba4a80eeb8ed47, base
  062b979a6271b7b3044ab06be3f3cde411a0d4f1, files MUSE-REPORT-1175.md,
  grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineInfinite.lean.
- `.tmp/review/author-1175/PATCH.diff`: the exact base...head diff (new
  661-line `PipelineInfinite.lean`; `Grammatik.lean` delta is exactly one
  appended `import Grammatik.X86.PipelineInfinite` line; report text).
- Delivered file copies of the same three files; delivered `.lean` is 661
  lines with head/tail identical to the PATCH text.
- `OWNER-TASK.md` (author task) and `BUILD-EVIDENCE.json` (author probe/build
  log, including intermediate red states and the final green runs).
- Packaging note (apparatus, not a candidate defect): the delivered report
  copy and the PATCH-embedded report end at the 5d9d800a response section;
  per BUILD-EVIDENCE the pinned d018126b commit is report-only
  (`git add MUSE-REPORT-1175.md`), and the `.lean` file is unchanged since
  5df87940. The proof content reviewed here is therefore identical to the
  pinned HEAD's proof content.

## Checklist results (all clean)

- Banned constructs: grep over the delivered `.lean` for
  sorry/admit/native_decide/sorryAx/unsafe/split_ifs/by_contra/`intro _`/
  `have _ :=`/leading-`axiom` finds nothing (hits elsewhere in the delivery
  are prose in the reports/task and one intermediate author build log, all
  superseded by the final green runs).
- Axioms: file ends with `#print axioms` for all 16 new theorems/lemmas;
  author evidence lists only standard axioms (`propext`, `Quot.sound`, and
  `Classical.choice` where family witness lemmas are used). No `axiom`
  declaration in the file. Proofs use only `simp`/`rw`/`omega`/`decide`/
  `cases`/`obtain`/`by_cases`/`rfl`/`exact`/`refine`/`subst`/`rcases`.
- Existing files untouched except the single import line (PATCH-verified);
  `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched; no second
  IR, no second source interpreter, no per-program rule.
- Accepted evaluator lifted, not copied: the only new semantics are
  `BudgetAusgang`/`laufBudget` (file lines 45-58) over the accepted
  `byteschritt`/`laufBytes`/`ByteAusgang` (`Byteschritt.lean`); correspondence
  goes through accepted `senkBlock_korrektC`, `validate_sound`, `Entspricht`,
  `CodeAt`, `WorldRep`, `LayoutSep`, `EnvRepr`, `ByteRahmen`,
  `laufBytes_rahmen`, `codeAt_lauf`, `execStmt_ite`,
  `execBlock_cons_stmtOk/Grund`, `constInt?_sound`, `optimise_sound` and the
  `pw*` witness data. Every cross-file name was resolved in this clone with a
  matching signature and compatible use (spot-verified call shapes: the
  `senkBlock_korrektC` application with `[] []` contexts, the
  `validate_sound` 6-pattern, `codeAt_lauf`/`laufBytes_rahmen` applications,
  the `sizeOf_spec` simp set mirroring `Pipeline.lean`, the
  `execBlock_cons_*` rewrites).
- Every premise used: each proof read; all hypotheses consumed, no discarded
  premises; `ρ`/`σ` stay concrete environments at actual values, and the
  generic theorems quantify exactly as the family theorems they build on.
  No conclusion restates a premise; no unsupported desired-correctness
  premise; no weakened guarantee.
- Refusals are genuine: `laufBudget_stopp_stabil` (file lines 171-199) proves
  a stop is sticky under more fuel; `erste_stop_ordnung` (264-303) proves no
  stop before the corresponding end. Probes compute: `gift_stopp_ist_stopp`
  (tampered `pwMemFalsch` stops the budgeted runner at step zero),
  `gift_fertig_laueft` (honest 5-step prefix runs clean),
  `gift_budget_kein_stopp_im_code` (honest 12-step run finishes at rip 4178).
- Witnesses joint and non-degenerate: `praefix_sicher_zeuge`,
  `erste_stop_ordnung_zeuge`, `budget_unabhaengig_zeuge` (file lines 455-558)
  instantiate all premises jointly on `pwSrc` (two slots written; source run
  changes memory 7 -> 35 and 9 -> 6; target 12-step computed run to the code
  end with a real stop, via `laufBytes12_stop`). Machine-level lemmas quantify
  only over `Nat`/`Zustand`, so no further companions are owed.
- Silicon: the file states no hardware facts (no encodings, extension or flag
  claims); the machine is reused unchanged. Single-core sequential model, no
  concurrency or weak-memory claim.
- CUTS honest and narrow (file lines 600-642): safety proved; termination,
  past-the-end stops (`k > n`), per-step source correspondence,
  progress/fairness, and all inherited fragment limits explicitly not claimed.
  The author's plainly-stated deviations from the task text (no second
  loaded-image closing theorem for lack of a witnessable `Bild`; prefixes
  proved safe rather than source-corresponding by design decision 594) are
  sound scope decisions, not hidden weakenings.

## Theorem inventory (delivered file lines)

`BudgetAusgang` 45-48; `laufBudget` 50-58; `laufBytes_praefix_erfolg` 67-85;
`laufBytes_verweigert_plus` 88-104; `laufBudget_fertig` 112-138;
`laufBudget_stopp` 141-167; `laufBudget_stopp_stabil` 171-199;
`laufBudget_fertig_von` 203-219; `praefix_sicher` 235-258;
`erste_stop_ordnung` 264-303; `budget_unabhaengig` 313-442 (with
`termination_by`/`decreasing_by`); three `_zeuge` companions plus
`laufBytes12_stop` helper 455-558; three `gift_*` probes 560-598; CUTS
600-642; `#print axioms` 644-659.

## Residual (apparatus, openly stated)

No independent `./lean-probe`/`./lean-bau` run from this lane: the `bash`
tool rejects every call in this session, so the instructed local copy into
`grammatik/` could not be made (a copy without the ability to probe or
remove it would only pollute the tree, so none was made). The green build
evidence is author-supplied (`./lean-probe`: 0 errors, exit 0;
`./lean-bau`: exit 0, 608 jobs, at the pinned HEAD), corroborated here by
complete static verification: full file read, banned-token grep, and
signature-level compatibility of every cross-file reference against this
clone. Recommended: the merge gate re-runs probe/build on the exact
candidate before integration.

## Last `./lean-bau` result line

Not run from this lane (no shell). Author evidence at pinned HEAD: `== exit
0; 0 error line(s) in the COMPLETE output`, `Build completed successfully
(608 jobs)`.

## New definitions/theorems by this lane

None. Report-only review lane owning only MUSE-REPORT-1176.md; no Lean file
added or modified.
