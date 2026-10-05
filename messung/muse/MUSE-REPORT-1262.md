# MUSE-REPORT-1262: Exact review of lane 1261 (Pipeline over TSO, store issue/drain path)

## Candidate

- Author lane 1261, reviewed from the in-clone snapshot
  `.tmp/review/author-1261/` (`SNAPSHOT.json`: HEAD
  `f89f0c1ad4a4bf70eefb25ce936b8487c2ff9c16`, base `515546d0`, clean).
- Diff scope: new `grammatik/Grammatik/X86/PipelineTsoStore.lean` (446 lines),
  one appended import line in `grammatik/Grammatik.lean`, plus
  `MUSE-REPORT-1261.md`. Nothing else touched.

## Checks performed (all in my own clone, read-only against the snapshot)

- Forbidden tokens: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
  candidate code. The only matches for the `admit` substring are the English
  word "admits" in doc comments; "axioms" appears only in `#print axioms`
  lines. The one `sorryAx` in `BUILD-EVIDENCE.json` belongs to a failed
  mid-work `rfl` attempt (2 errors, exit 1) that the author repaired and
  documented; the final run is clean.
- Independent re-elaboration: `./lean-probe
  .tmp/review/author-1261/grammatik/Grammatik/X86/PipelineTsoStore.lean`
  gives `== 0 error(s) in the COMPLETE output; exit 0` against my newer tree,
  so there is no base drift and no invented name. Every referenced lemma
  (`hwWortAusgabe_puffer`, `hwWortAusgabe_kein_speicher`, `issueListe_stern`,
  `issue_verweigert`, `issueListe_cons_none`, `flush_leer`,
  `stapelPop_unlesbar`, `setTso_ansicht`, `drainGleichWrite64`,
  `issueListe_haengt_an`/`_anderer_kern`/`_kein_speicher`/`_erhaelt_berechtigungen`,
  `grp_hgrp`, `grp_spur`, `grp_hend`, `grp_hempty`, `grp_hstoer`, `grp_hles`,
  `drainGrp_hwr`, all `drainWit_*`) resolves to an accepted in-tree theorem.
- Axioms (reproduced): every new theorem depends at most on
  `[propext, Quot.sound]`, a subset of the required triple. No `Classical.choice`.
- Existing files: only the single import append; `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` untouched.
- Premise use: every premise of every new theorem is used. The main theorem
  `pipeline_correct_tsoStore` builds the `WortGruppe` from `h_issue`
  (via `tsoStore_puffer`), `hleer0` and `h_fremd`, and feeds `hles`, `hspur`,
  `hend`, `hleer`, `hstoer`, `hwr` into the accepted `drainGleichWrite64`,
  whose signature I verified takes exactly those premises.
- Lift, not copy: `tsoStoreIssue` is a direct alias of the accepted
  `hwWortAusgabe`; the issue-path lemmas are thin lifts of accepted theorems.
  No machine, decoder row or instruction duplicated.
- Refusals: guard / empty-drain / dark-observation refusals each fire as a
  concrete `= none` theorem (`tsoStoreGiftWache`, `tsoStoreGiftLeer`,
  `tsoStoreGiftDunkel`) on witness machines. All typecheck.
- Witness: `pipeline_correct_tsoStore_zeuge` instantiates ALL main-theorem
  premises jointly on concrete machines. Non-degenerate: two cores
  (`drainWitKern`, owner-forwarding of 42 while the foreign core reads 0),
  and a shared-memory change 0 -> 42 observed from both cores after the drain.
- Silicon / scope: no new silicon fact is stated (eight-entry expansion is
  pinned by `rfl` against the accepted `wortEintraege`, not a new encoding
  claim). CUTS honestly leaves OPEN the `store64` fetch/decode/execute leg,
  the `Pipeline.senkStmt` relation, silicon correspondence and any W/GX
  simulation. No claim exceeds the proof.
- Author's task-critique verified: there is no `PipelineTso.lean` and no
  `pipeHw_reg_einbettung` anywhere in `grammatik/`, so no lift onto lane 1169
  could have been stated. Correctly recorded in CUTS instead of invented.

## Baseline build

- `./lean-bau` in my clone: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (658 jobs).`

## Nits (not verdict-changing)

- CUTS describes `grpWit_issue` as proved "by `rfl`"; the final proof goes
  through the propositional `grpWit_fold`. Stale wording, proof itself is fine.
- `grpWit_wf` uses `intro c f _`, discarding a hypothesis. This matches the
  accepted in-tree precedent `hwWf_aus_zugelassen` exactly, and the hypothesis
  is redundant on the full-silicon witness profiles. Not a violation in spirit.
- The source-`execBlock`/loaded-image half the CONTEXT paragraph sketches is
  not delivered; it is honestly cut, and the lane's core demand (eight byte
  issues, `HwSchritt` embedding, post-drain outcome, foreign core sees old
  value, two-core witness) is fully met.

## Machine-readable verdict

CANDIDATE: 1261 f89f0c1ad4a4bf70eefb25ce936b8487c2ff9c16
VERDICT: ACCEPT
