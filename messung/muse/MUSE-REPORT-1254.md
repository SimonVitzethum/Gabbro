# MUSE-REPORT-1254: Independent exact review of lane 1253 (TsoGxStart)

CANDIDATE: 1253 79ceb5ef5e26e9e5468d8f2cc1c40f05bbcca9c7

## Clone / branch verification
- Reviewer clone: `/home/simon/Dokumente/gabbro-muse/a1254`, branch `muse/1254`.
- Reviewed artifact: the pinned snapshot in `.tmp/review/author-1253/` at the hash above
  (base `515546d0e2430c0d416ede74e3add0166e88e2de`): `PATCH.diff` (227 lines),
  `MUSE-REPORT-1253.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, plus the new module file.
- Owned file only: this report. No Lean files created or modified by the reviewer.
- Procedural note: the first attempt at this review was recorded as blocked (lane text
  carried a `<full pinned HEAD>` placeholder and the author clone was not readable from
  here). The pinned snapshot has since been supplied inside this clone, so the full
  substantive review below replaces that blocked status entirely.

## Candidate content
- New file `grammatik/Grammatik/X86/TsoGxStart.lean` (141 lines) + exactly one appended
  import line in `grammatik/Grammatik.lean`. No other existing file touched.
- New names (all `Gabbro.Grammatik.X86`): `startAnker`, `startAnker_refl`,
  `startAnker_gleich`, `startCall_erreichbar`, `fragmentKopf_erreichbar`,
  `startBrueckenArten`, `startFragment_zeuge`.

## Checklist results
- Forbidden tokens: `rg` over the full patch for `sorry|admit|axiom |native_decide|unsafe|
  intro _|have _ :=` returns zero matches. Clean.
- `#print axioms` present for all 7 main theorems; build evidence reports standard
  dependencies only (`propext, Classical.choice, Quot.sound`; `startAnker_gleich` on
  `propext` alone, `startBrueckenArten` axiom-free). Standard.
- Existing files: only the one import line. The one-import rule holds.
- Premise use: no theorem takes an unused premise; no `Prop`-typed premise; nothing
  restates a premise as its conclusion; no contract quantification; no new semantics
  (no new machine, no new executor); no discarded premises. `startBrueckenArten` uses
  its `FragArt` premise directly through the accepted covering lemma.
- Lift-not-copy: every proof step reuses accepted lemmas unchanged — `w_rufEnde`
  (entry/call step), `w_blatt` with `execStmt_assignSlot` (fragment-head step),
  `fragArt_abgedeckt_oder_drain` (kind enumeration), `ziel_ort_einfaden_zeuge` plus an
  `rfl` write fact (joint witness). All four names resolve in this reviewer's master
  (`RufAdaequatRufG.lean`, `TsoRunInduction.lean`, `ZielOrtEinfadenZeuge.lean`). The only
  new definition, `startAnker`, is a concrete machine instance (`RufStartG eP eSp eInit`),
  not a copied model.
- Refusals: the candidate admits nothing new (no adapter, no step relation, no gate),
  so no new planted refusal is owed; the drain kind is referenced as refused-a-W-step by
  the accepted run induction, not re-proved. Nothing to fire.
- Witness non-degeneracy: `startFragment_zeuge` instantiates all premises jointly on the
  accepted program `eP` (`haupt` calls `setze`, which writes table `konto`): a reached
  machine from `RufStartG`, start world `konto[0] = 0`, `setze` writes `konto`
  (`schreibt = true` by `rfl`), logged `pruefe` entry world with `konto[0] = 5` —
  an observable memory change on a written table. The accepted
  `ziel_ort_einfaden_zeuge` was re-read here and has exactly the lifted shape.
  Single-threaded (`faeden 0`) is correct for this leg: it is the entry/call prefix,
  and the two-core forwarding shapes live in the already-accepted `TsoRunInduction`
  kinds, which this module consumes by reference only.
- Silicon: no silicon, encoding, fault-class or ordering claim is made. Nothing to check
  against the SDM extracts.
- CUTS honesty and claim size: the CUTS block (plus the author report) explicitly
  disclaims the cross-declaration refinement simulation, the per-access TSO-to-W/GX
  simulation, and the byte-level entry/call linkage. No hardware-correspondence and no
  W/GX bridge claim. The claim matches the proof.
- Weaker-than-task point, stated plainly by the author (rule 4 compliant): the owner
  task asked to reuse byte-level `PipelineEntry.lean`/`StackExecution.lean`, but
  `RufStartG` reachability is source-level (`RufSchrittG`), so the prefix reuses the
  source-level entry/call lemmas instead and records the byte-to-source entry connection
  as OPEN. Faking the byte linkage would have been worse; the honest OPEN is correct.
- Stale task-context claim (not a defect): the author states `TsoGxRefine.lean` does not
  exist on their base. On this reviewer's newer master it does exist (lane 1215 has
  since integrated; `Grammatik.lean:649`). The candidate's composition statement stays
  valid regardless — composition with the refinement is OPEN either way — but whoever
  integrates should rebase onto current master (candidate base `515546d0` predates the
  1233/1234 merges) and check the prefix against the now-present refinement statement
  as follow-up work, not as a condition on this leg.

## Builds
- Reviewer baseline `./lean-bau` in this clone: `Build completed successfully (651 jobs).`
  with `== exit 0; 0 error line(s) in the COMPLETE output`.
- Candidate build evidence (pinned, author-side): `./lean-probe` on the new file
  `== 0 error(s)`, and `./lean-bau` `Build completed successfully (644 jobs).` with
  `TsoGxStart` built at `[642/644]` and the 7 axiom lines as above. Consistent with the
  reviewer's independent grep/axiom/name-resolution checks; the file was not rebuilt in
  this clone because the review lane owns no Lean files.

## Integration note
- Rebase required at merge: candidate base `515546d0` vs current master; the
  `Grammatik.lean` import hunk is a one-line append (union-resolvable), and the new
  module's imports (`ZielOrtEinfadenZeuge`, `TsoRunInduction`) are unchanged on master.
- Follow-up (not this lane): compose the now-present `TsoGxRefine` refinement statement
  with this prefix leg via a cross-declaration lowering certificate.

## Definitions / theorems added by the reviewer
- None (report-only review lane).

VERDICT: ACCEPT
