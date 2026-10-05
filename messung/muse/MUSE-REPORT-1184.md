# MUSE-REPORT-1184: Exact review of candidate 1183 (feature gating per step)

CANDIDATE: 1183 cd5eb23ee3a94da1b0e2fb0b47775b6f322381ac

## Task

Report-only independent exact review of CANDIDATE 1183. The LANE.md text
carries the placeholder `<full pinned HEAD>`; the clone-local review
snapshot (`.tmp/review/SNAPSHOT.json`, inside my own clone, no outside
access) pins the candidate exactly, and that pin is what I reviewed:

- author: 1183, HEAD `cd5eb23e3a94da1b0e2fb0b47775b6f322381ac`,
  base `0ddf527d050ae9edced5f26e90172293b059eaf2`, clean tree.
- Files (3): `MUSE-REPORT-1183.md` (new), `grammatik/Grammatik.lean`
  (one appended import line), `grammatik/Grammatik/X86/HwFeatureStep.lean`
  (new, 683 lines).
- Review source: `.tmp/review/author-1183/PATCH.diff` plus the snapshotted
  files. I read the candidate diff only; no other tree state was used.

## What was checked

1. **Forbidden tactics/axioms.** Grepped the new file for
   `sorry|admit|native_decide|axiom|unsafe`: only benign `admits`
   substrings inside doc comments (lines 68, 78, 101, 124, 465, 520,
   616-618). No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`.
   No `intro _` / `have _ :=` premise discards. PASS.
2. **Axioms.** Author BUILD-EVIDENCE shows every `#print axioms` line as
   `[propext, Quot.sound]`, except the decide-only
   `hwStepTor_ohne_silizium_zu` as `[propext]`. That is within the
   standard goal-axiom set (subset, no `Classical.choice` needed, no new
   axiom). The file ends with `#print axioms` for 27 names plus a CUTS
   block. PASS.
3. **Scope.** `PATCH.diff` has exactly three file diffs; the
   `Grammatik.lean` hunk appends only
   `import Grammatik.X86.HwFeatureStep`. No accepted definition edited
   (task: lift, never edit). PASS.
4. **Lift, not copy.** The only new definition is `stepExtTor`, which
   calls the accepted `stepExt`/`projFp`/`m.bereit` under the accepted
   whole-gate `hwTorOffen`; §3 agreement goes through the accepted
   `stepExt_fp`/`stepExt_vec`/`stepVector_profil_verweigert` lemmas and
   the accepted `adapterFeatureTor`/`HwTorSchritt`/`hwTor_verbindung`
   results. No model duplicated. PASS.
5. **Premises used.** Spot-checked every theorem: `hwStepTor_verbindung`
   forwards all 12 premises (`hoff`, `hstep`, `hmem`, `hwf`, `s1 s2 a
   val hrd hissue e hrest hbuf hflush`) into `hwTor_verbindung`;
   `hwStepTor_wf`, `hwStepTor_ok_iff`/`ud_iff`, the §3 lifts/inversions
   and the F2 ignorance equalities all use both sides / all hypotheses.
   No conclusion restates a premise; no `forall rho/v` contract
   quantification; no fake semantics. PASS.
6. **Planted refusals.** `hwStepTor_unbereit` (no OS vector state),
   `hwStepTor_ftz` (FTZ word), `hwStepTor_ohne_bit` (no observed bit),
   `hwStepTor_ohne_silizium` (absent silicon), plus
   `hwStepTor_halb_1` (half-gated core 1) — each is a proved
   `= .verweigert` equation via `stepExtTor_zu` and an accepted
   closed-gate lemma, not an assertion. The positive twins
   (`hwStepTor_wit_vec`, `hwStepTor_halb_0`) execute. PASS.
7. **Witness non-degenerate.** `hwStepTor_verbindung_zeuge` (18
   conjuncts) joins: step-level vector admission, wrapper `HwTorSchritt`
   leg, exact `HwSchritt.reg` embedding, TSO owner forwarding
   (`loadByte hwTorS1 0 = 42`) with foreign core observing 0
   (owner-only), drain into shared memory (`hwTorS2.mem = 42`) against
   initial byte 0 (memory 0 becomes 42), well-formedness, both fault
   silences, two-core half-gating at step AND wrapper level, unbereit
   refusal with `.ud` fault, scalar-FP admission with open gate. Two
   cores where the family touches memory; memory-changing step. PASS.
8. **Silicon.** No new hardware definition: encodings, bit positions,
   lengths, fault classes are all the accepted producers'. The one new
   machine value (`hwStepTorOhneSilizium`) flips an accepted silicon
   feature bit off. CUTS names clone-local Intel SDM provenance (as in
   MUSE-REPORT-660/1135), no AMD snapshot, no vendor-difference, timing
   or physical-silicon claim. PASS.
9. **CUTS / claim size.** CUTS lists exactly what is proved (§§1-5 plus
   closing) and explicitly NOT proved: register-plug discipline for
   memory-touching forms, no source/checker/emitter correspondence, no
   per-access target-to-W/GX simulation, no whole-word atomicity beyond
   reused TSO byte equations, no image/loader/entry/budget link. No
   hardware-correspondence or W/GX claim anywhere in file or report.
   The F4/silicon-absent and F3/observation findings match the task's
   requested FINDING deliverable. PASS.

## Build verification — BLOCKED, stated honestly

- I could not run an independent `./lean-bau`: all `bash` tool calls in
  this session are rejected by the permission classifier (two attempts,
  both denied before execution), so no queued wrapper could be started.
  This is an environment denial, not a candidate defect.
- Relied-on evidence instead: the author's `BUILD-EVIDENCE.json`
  (clone-local, committed with the candidate) records a `./lean-probe`
  `== 0 error(s)` final state and `./lean-bau`
  `Build completed successfully (618 jobs).`, plus a clean
  `git status` and commit `cd5eb23e`. The probe log also shows two
  mid-task red states honestly repaired before the final green, which
  reads as genuine development, not a doctored log.
- A merger should still run the standard `./lean-bau` gate before
  integration; nothing here substitutes for it.

## What remains open

- Serial `./lean-bau` (and the merge-gate sorry/axiom scan) must still be
  run by whoever integrates; my ACCEPT rests on exact-diff review plus
  the author's committed build evidence.
- Nothing in the candidate itself is left open beyond its own honest
  CUTS list.

## What is wrong in the task

- `LANE.md` line 25 gives the candidate as `1183 <full pinned HEAD>`
  without the hash; the actual pin came from `.tmp/review/SNAPSHOT.json`
  (`cd5eb23e…`). Suggest filling the hash into the lane line so the
  reviewer never has to resolve it indirectly.
- `LANE.md` line 23 says to read the diff in "the author clone", which
  contradicts HARD RULE 1 (touch nothing outside this directory). The
  clone-local `.tmp/review/author-1183/` snapshot resolves the conflict;
  the lane line should name the snapshot path instead.

VERDICT: ACCEPT

Candidate 1183 at pinned HEAD
`cd5eb23e3a94da1b0e2fb0b47775b6f322381ac` is accepted on exact review:
standard axioms only, no forbidden tactics, minimal scope (one new file
plus one import line), accepted evaluators lifted not copied, every
premise used, planted refusals proved as refusal equations, joint witness
non-degenerate (two cores, memory 0 becomes 42, owner-only forwarding),
silicon provenance clean, CUTS honest with no W/GX or
hardware-correspondence overclaim. Integration still owes the routine
serial `./lean-bau` gate, which this environment denied me.

No new definitions or theorems were added by lane 1184 (review-only lane;
owned file is this report alone).
