# MUSE-REPORT-1170: Independent exact re-review of author 1169 (Pipeline correctness over the multi-core TSO machine)

CANDIDATE: 1169 0c5f2ec6f4e45fdb424f535fc57c1f6ad7684252

Clone: /home/simon/Dokumente/gabbro-muse/a1170, branch muse/1170 (re-verified this session via allowed git calls; toplevel and branch match the lane task, so did not STOP).
Owns only: MUSE-REPORT-1170.md. No Lean file created or edited; no existing file touched.
Pinned snapshot for this re-review: author 1169, head 0c5f2ec6f4e45fdb424f535fc57c1f6ad7684252, base 062b979a6271b7b3044ab06be3f3cde411a0d4f1, files MUSE-REPORT-1169.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineTso.lean, clean true. Review material was read inside this clone under .tmp/review/author-1169 (PATCH.diff, module copy, author report, owner task, build evidence). Nothing outside this directory was touched.

## Relation to the previous decision

The previous ACCEPT on the prior head stands reviewed, not stale-approved: the author delta to this head is report-only. Evidence: the pre-commit `git diff --stat` in BUILD-EVIDENCE shows only MUSE-REPORT-1169.md changed (35 insertions, 1 deletion); the Lean files are byte-identical to the accepted state. The added report section is the integration-gate response (gate FAILED on resource grounds, nothing merged; attempted length-proof hunk recorded verbatim but reverted per the no-red-commit rule, so NOT in the tree). No changed proof is in the tree, and the recorded hunk will need a fresh review if ever re-applied. Every previous content finding was re-inspected against the new snapshot and carries over.

## Evidence inspected (all inside this clone)

- PATCH.diff: exactly the 3 snapshotted files. Grammatik.lean delta is one appended import line for the new module. No other existing file touched; reserved optimiser files untouched.
- PipelineTso.lean copy, re-checked: banned-token scan finds nothing (no sorry, admit, axiom declarations, native_decide, unsafe, split_ifs, discarded-premise patterns; the decide-based probe_tear is intact and no length-proof hunk is present).
- MUSE-REPORT-1169.md including the new gate-response section.
- BUILD-EVIDENCE.json in full: development probes with intermediate errors honestly shown, final module probe 0 errors with standard axioms, one full lean-bau 608 green, then two aggregator-only failures (exit 134, bad_alloc and failed-to-create-thread at step 607/608 with zero Lean errors), a confirming probe 0 errors, and the report-only commit for this head.
- OWNER-TASK.md (requirements unchanged).

## Checklist findings (re-verified on the new head)

- Banned constructs: clean as above. No Prop-typed premises; every theorem premise is a specific proposition.
- Axioms: standard only (no axioms, propext, or propext plus Quot.sound per the recorded probe output).
- Scope discipline: exactly the 3 owned files; the one existing-file edit is the single import line.
- Premise use: every theorem-level premise is consumed; underscore-prefixed names appear only on destructured auxiliary-lemma outputs, never as discarded theorem premises.
- Lifted, not copied: thin wrappers over accepted results, previously spot-verified present in this tree (load_nach_issue, issue_kein_speicher, hwGibAus_kein_speicher, hwWortAusgabe_puffer, hwWortAusgabe_kein_speicher, wort_gruppe_liest_zurueck, drain_installiert_aux, hwPilot_weiter, read64_nach_write64, writeBytesN_hit, hwLock_verweigert, kein_lock_schritt, hwTeilwort_keine_gruppe, hwGruppe_verweigert_bei_fremdeintrag, the hwWit witness family, canonical defs). No second interpreter, no new IR, no duplicated model.
- Refusals genuine: four refusal theorems plus three deciding probes (rfl on a concrete xadd64 request against the defined LOCK refusal, decide on a 2-of-8 buffer, accepted overlap no-group lemma).
- Witness non-degenerate: five-part conjunction over the accepted two-core run (initial 0, own-core forwarding of 42, foreign stale 0, post-drain 42 in actual shared memory from both cores). Memory-changing and joint.
- Silicon: no new hardware facts; everything reused from accepted canonical definitions.
- CUTS honest, claim matches proof: word plus per-footprint-byte agreement between the SC store and the exclusion-checked grouped drain, explicitly not whole-memory equality; full pipeline_correct lift, whole-word atomicity beyond grouped drains, LOCK paths, shared-atomic contracts, per-access W/GX simulation, fairness, progress, timing, budget, interrupts, devices, and anything beyond pilot ISA disclaimed. No hardware-correspondence or W/GX overclaim.

## Integration-gate status (new since last review, stated plainly)

The integration gate FAILED for this head on environmental resource grounds: the final Grammatik aggregator step died twice locally (bad_alloc, failed-to-create-thread, exit 134) with zero Lean errors, and nothing was merged. The module itself compiles (probe 0 errors, all 21 print-axioms lines emit). This matches the documented apparatus failure mode under concurrent-lane memory pressure. My content verdict below is not a claim that integration or publication passed; the merger must still clear a serial low-contention build. Downgrading content to REPAIR over an evidenced resource failure with no proof defect would be dishonest in the other direction, so the substantive content verdict is preserved.

## Decision and reasons

VERDICT: ACCEPT

The new head meets the exact-review bar: clean scans, standard axioms, exact 3-file scope with a one-line import, all premises used, accepted evaluator lifted rather than copied, refusals that genuinely refuse with deciding probes, a non-degenerate two-core memory-changing witness, no new silicon claims, and CUTS that state precisely what is and is not proved. The Lean content is identical to the previously accepted state; the only delta is the honest gate-failure report. No weakened guarantee and no desired-correctness premise was found.

## Build status

- This reviewer clone ./lean-bau: Build completed successfully (607 jobs), exit 0 with 0 error lines (run 2026-10-05; tree is base plus reviewer reports only, hence 607 vs the author tree 608).
- Author evidence for the reviewed head: module ./lean-probe 0 errors with standard axioms; one full ./lean-bau 608 green on this exact Lean tree; two later aggregator-only resource failures (exit 134, zero Lean errors) leaving nothing merged.
- New definitions or theorems by lane 1170: none (report-only review). Reviewed author theorems are listed in the checklist above.

## Task remarks

Nothing in the author task appears wrong. The word plus per-byte scoping note remains sound.

CUTS of this review: content re-verified against the new pinned snapshot by reading the diff text and re-running the scans; the author build was not re-executed here (recorded runs relied upon as quoted); nothing new about the pipeline itself is proved by this report.
