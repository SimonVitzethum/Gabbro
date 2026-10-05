# MUSE-REPORT-1192: Exact re-review of author lane 1191 (Pipeline spill with privacy)

CANDIDATE: 1191 1749d2eb97a6ad8819665f4537b480fa9f527960

## Identity and pin
- Clone: /home/simon/Dokumente/gabbro-muse/a1192, branch muse/1192, `git status` clean.
- New pin: `.tmp/review/SNAPSHOT.json` lists author 1191 at head 1749d2eb97a6ad8819665f4537b480fa9f527960 on base 9b05e84a8377f2a718cecf9ca1a403d6c9c2b919, files MUSE-REPORT-1191.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineSpill.lean, clean true.
- Evidence read: `.tmp/review/author-1191/PATCH.diff` (872 lines), the pinned new-file copy (762 lines), MUSE-REPORT-1191.md, OWNER-TASK.md, BUILD-EVIDENCE.json. The prior procedural block (missing object for the old 12cd3bc6 pin) is superseded: the full new snapshot is present and was reviewed. Own scope respected: only this report created or modified.

## What changed since the stale finding
- The old report returned a procedural repair because the pinned object was absent locally. No substantive defect had been raised.
- The new head adds a review-response section to the author report and honesty lines to the file-level CUTS (address-register clobber with allocator freshness not re-checked, declared-extent versus placed-table agreement as deployer obligation). The author describes the delta as comment-only with no proof touched, which matches the reviewed CUTS text.

## Independent checks on the pinned files
- Forbidden tactics: no `sorry`, `admit` tactic, `axiom` declaration, `native_decide`, or `unsafe` in the new file (grep hits were only English prose such as admitted/refused); no `intro _` / `have _ :=` discards; no mathlib-only tactics.
- Axioms: every main theorem carries `#print axioms` (33 prints, file lines 728-760); reported axiom sets are within the standard triple, e.g. the closing theorem at propext plus Classical.choice plus Quot.sound and most lemmas fewer. No new axiom.
- Scope: existing tree untouched except the single appended import line in Grammatik.lean (verified tail); reserved optimiser files untouched (only a qualified type reference to OptimizationRules.PassKind/BlockCert, no edit); new work confined to the one new file.
- Lifted not copied: the file reuses the accepted pipeline lowering and validator (`pipeline_correct`, `validate`, `abbOf`, layout/world/env representation), the accepted spill-privacy vocabulary (`spillSlot`, `SpillFrisch`, `GetrenntK`, `spillPrivatOk`, `SpillZugelassen`, `ComposeSpillPrivacy_verbindung`), and the canonical step lemmas (`schritt_movImm64`, `schritt_store64_erfolg`, `schritt_load64_erfolg`, `effAddr_null`, `lauf_anhang`). No second IR or second evaluator.
- Premise use: the round-trip theorem threads plan admission, slot bound, privacy admission, freshness, disjointness, readability, checked store and reload through the accepted connection plus pairwise separation; the closing theorem feeds every source/pipeline premise through `pipeline_correct` and every spill premise through the validator legs. No unused-premise pattern found (the two linter notes on existential binders are witness instantiations, not discards).
- Refusals: table-extent, out-of-frame, and aliasing plans are refused by general theorems through the matching validator legs; probes decide each leg both ways (one positive plus table/frame/collision/code refusals, table also through the refusal theorem). Probe constants are coherent: witness frame at 16384 off the witness code and tables, slots 0 and 1, overlapping-tablet probe at 16384 genuinely overlapping slot 0.
- Witnesses: joint premises on the pipeline witness program with memory-changing rows 7 to 35 and 9 to 6, and a reached checked save of 42 with observable slot-byte change beside the writer program that writes konto. Non-degenerate by the lane standard.
- Silicon and scope honesty: fragments are the accepted pilot shape (address materialisation plus zero-displacement store/load) proved against canonical step lemmas; straight-line shape proved; CUTS disclose the address-register clobber, the un-rechecked allocator freshness, the declared-versus-placed table agreement, and the inherited fragment limits (no live-range splitting, no calls, TSO only via the reused vocabulary, no read-trace, no loaded-image shape). The refusal boolean is described as validator admission, never a hardware fault. No hardware-correspondence or W/GX claim. One note: a reload docstring mentions register preservation more broadly than the proved conclusion states (proved: memory unchanged, destination holds the value); this is comment scope, not a soundness gap, and does not change the verdict.

## Builds
- Reviewer baseline `./lean-bau` in this clone (without the author diff, which is not applied here by ownership): first line `== exit 0; 0 error line(s) in the COMPLETE output`, last line `Build completed successfully (619 jobs).`
- Author evidence for the pinned head: `./lean-probe` on the new file 0 errors, full `./lean-bau` green at 620 jobs (one more unit than this baseline, consistent with the one added file), and the sorry-gate at 627 files with 0 violations.

VERDICT: ACCEPT

## New definitions or theorems by this reviewer
- None (report-only review; own file only).

## Remaining work
- None for this review. Integration remains the coordinator merge gate business (axiom, import-scope, and emission checks at merge time).
