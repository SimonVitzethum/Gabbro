# MUSE-REPORT-1130: Exact re-review of candidate 1129 (Scalar FP32/FP64 and MXCSR)

CANDIDATE: 1129 f105c9366997fc7e20ec09616f0661a0cc6604d3

Lane 1130 (reviewer). Clone `/home/simon/Dokumente/gabbro-muse/a1130`, branch `muse/1130`: verified (`pwd`, `git branch --show-current`).

## What changed since the stale verdict

The previous verdict (REPAIR on reviewability only, commits `ed19117d`/`eddcdb14`)
reported that pinned commit `6032515d` was not reachable from this clone. The
coordinator has since repinned to `f105c936` (same Lean tree; the delta to
`6032515d` is report text only, "No Lean change" per author evidence) and
provided the exact snapshot in-clone at `.tmp/review/`: `SNAPSHOT.json`
(author 1129, head `f105c936…`, base `8744590d…`, files `MUSE-REPORT-1129.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwFpControl.lean`),
`PATCH.diff` (1490 lines), the candidate `grammatik/` file, `OWNER-TASK.md`,
`MUSE-REPORT-1129.md` and `BUILD-EVIDENCE.json`. This re-review runs the full
checklist against that exact material. No stale snapshot is approved.

## Checks performed (all against the pinned material)

- **Scope/ownership**: `PATCH.diff` touches exactly the three owned files:
  new `MUSE-REPORT-1129.md`, one appended line `import Grammatik.X86.HwFpControl`
  in `grammatik/Grammatik.lean` (hunk at end of imports), new 1317-line
  `grammatik/Grammatik/X86/HwFpControl.lean`. No existing theorem edited.
- **Forbidden tactics**: static scan of the candidate file for
  sorry/admit/axiom-declarations/native_decide/unsafe finds only English prose
  ("admitted"/"admits" in doc comments); no tactic use. Corroborated by the
  axiom prints (no `sorryAx`) and by independent elaboration below.
- **Independent elaboration (reviewer-measured)**: `./lean-probe` on the exact
  snapshot file in this clone: `== 0 error(s) in the COMPLETE output; exit 0`
  (one linter warning: unused binder `s'`, harmless). This also confirms the
  file still elaborates against this clone's newer master: every referenced
  accepted name (`stepExt_fp`, `s32Schritt_addssRR`, `mxcsrSchritt_ld_erfolg`,
  `issueListe_anderer_kern`, `fpHwEncodeArithRR`, `fpHwLen_rr`, …) resolves.
- **Axioms**: `#print axioms` block present for every main theorem; outputs
  (reviewer-observed) are only `propext`/`Quot.sound` subsets, matching the
  author's recorded lines. Standard.
- **Lift, not copy**: the file imports the four family modules plus
  `HardwareExecution` and `ConcurrentIntegerExecution`; family evaluators
  (`s32Schritt`, `fpSchritt`, `mxcsrSchritt`) appear only as applied equation
  premises and cited lemmas, never redefined. The earlier duplicate
  `issueListe_anderer_kern` is gone: exactly one occurrence, a use
  (line 785) fed by the accepted import — the repair from `857cce26` holds in
  the pinned tree.
- **Premises used**: spot-checked across all sections; every theorem premise
  feeds its proof (step equations drive `cases`/rewrites; `hmem` gates feed the
  `HwSchritt.reg` constructor; refusal hypotheses rewrite the step to `none`).
  No `Prop`-typed premise, no discarded premise, no conclusion restating a
  premise (the `∃ s'` in `fpCtrlSpüle_ist_hw` packages the embedding
  `FpCtrlSchritt → HwSchritt`, not a rename).
- **Refusals**: length/profile/LOCK/permission refusals conclude `False` from
  (step ∧ refusal condition) via the accepted family refusal lemmas; they
  elaborate, so the refusal chains genuinely close.
- **Witness** (`fpCtrl_zeuge`): non-degenerate — two-core reached run
  (core 0 fetches REX DIVSD `1.0/+0.0=+inf`, register ADDSS
  `1.0f32+2.0f32=3.0f32` with upper96 preserved, MXCSR reset install with
  admission); the four-drain changes actual shared memory (`0` becomes
  `0x40400000`, closed `decide` evaluation); owner-only forwarding proved
  (`0x40` owner vs `0x00` foreign, then foreign observes `0x40` post-drain);
  core-1 fetch refusal included. All premises jointly instantiated.
- **Silicon**: lengths used (DIVSD 5 = F2+REX.W+0F+opcode+ModRM, ADDSS 4,
  LDMXCSR m32 7) match the architecture; reset word `0x1F80`; LOCK-prefixed
  LDMXCSR `#UD`. All silicon facts live in the accepted families and are
  cited, never restated; the file and CUTS explicitly disclaim hardware
  correspondence beyond self-consistency and claim no W/GX bridge.
- **CUTS**: honest block present; open points (no `decodeExt` s32/MXCSR rows,
  no per-access W/GX simulation, no word atomicity beyond byte groups,
  inherited family cuts) match the code. Claim is not larger than the proof.
- **Build**: author evidence records full `./lean-bau` green (601 jobs) at the
  pinned Lean tree plus sorry-gate 0 violations. Reviewer ran `./lean-bau` on
  the own tree (candidate import not wired here): green, last line
  `Build completed successfully (604 jobs).` Full-candidate-tree rebuild was
  not reproduced in the reviewer clone (would require editing `grammatik/`
  beyond owned files); module-level green is reviewer-measured, project-level
  green is author-evidenced and consistent with it.

## Finding

VERDICT: ACCEPT

Candidate 1129 at the pinned HEAD is accepted: the family's accepted
evaluators are lifted unchanged onto the coherent machine with exact embedding
theorems, wf preservation, genuine refusals, and a non-degenerate two-core
witness; axioms standard; CUTS honest; no claim beyond the proof. The one
content defect in its history (duplicated `issueListe_anderer_kern`) was
repaired before pinning and verified absent. The previous reviewability REPAIR
is superseded by the provided exact snapshot, not overridden.

## Open

- Nothing pending on this review. `MUSE-REPORT-1130.md` is the only file owned
  and committed by this lane; no Lean code added, so no witness obligation applies.
