# MUSE-REPORT-1170: Independent exact re-review of author 1169 (Pipeline correctness over the multi-core TSO machine)

CANDIDATE: 1169 c14c2ef2ded9b965f182ba64e62a5bed6ba7fcc9

Clone: /home/simon/Dokumente/gabbro-muse/a1170, branch muse/1170 (re-verified this session via allowed git calls; toplevel and branch match the lane task, so did not STOP).
Owns only: MUSE-REPORT-1170.md. No Lean file created or edited; no existing file touched.
Pinned snapshot for this re-review: author 1169, head c14c2ef2ded9b965f182ba64e62a5bed6ba7fcc9, base 062b979a6271b7b3044ab06be3f3cde411a0d4f1, files MUSE-REPORT-1169.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineTso.lean, clean true. Review material was read inside this clone under .tmp/review/author-1169 (PATCH.diff, module copy, author report, owner task, build evidence). Nothing outside this directory was touched.

## Relation to the previous decision

The prior decision on the older head was a blocked REPAIR on purely apparatus grounds (no pinned diff text available then, every checklist item NOT CHECKED, zero content findings raised). That decision is now stale and superseded. The author delta between the older head and this head is report-only (review-response plus self-verification section in MUSE-REPORT-1169.md; commit message states no code change needed). This report is a full content review of the new head, not an approval of a stale snapshot.

## Evidence inspected (all inside this clone)

- PATCH.diff, 400 lines: exactly the 3 snapshotted files. Grammatik.lean delta is one appended import line for the new module. No other existing file touched; reserved optimiser files untouched.
- PipelineTso.lean, all 277 lines read: 1 definition (pipeHw) plus 21 theorems with closing print-axioms lines and a CUTS block.
- MUSE-REPORT-1169.md (author report with task, theorem list, verification log, open-items, scoping note on word/byte agreement vs whole-memory equality).
- BUILD-EVIDENCE.json: staged lean-probe runs ending at 0 errors, full lean-bau 608 jobs green on the final tree, plus the two commit records.
- OWNER-TASK.md (author task text, unchanged requirements).

## Checklist findings

- Banned constructs: clean. Grep over the snapshotted module for sorry, admit, axiom declarations, native_decide, unsafe, split_ifs, discarded-premise patterns finds only the 21 print-axioms lines (substring hits on the word axioms). No Prop-typed premises; every theorem premise is a specific proposition.
- Axioms: standard only. Build evidence lists every theorem at no axioms, propext, or propext plus Quot.sound. No Classical.choice needed, no extras.
- Scope discipline: exactly the 3 owned files; the one existing-file edit is the single import line. Nothing else in the tree is modified.
- Premise use: every theorem-level premise is consumed by its proof. Underscore-prefixed names (_hff, _hk0, _hk8) appear only on components of destructured auxiliary-lemma outputs, never as discarded theorem premises; _hbufN from the same tuple is used in a rewrite. No intro-underscore or have-underscore discards.
- Lifted, not copied: the module is thin over accepted results. Spot-verified present in this tree: load_nach_issue, issue_kein_speicher, hwGibAus_kein_speicher, hwWortAusgabe_puffer, hwWortAusgabe_kein_speicher, wort_gruppe_liest_zurueck, drain_installiert_aux, hwPilot_weiter, read64_nach_write64, writeBytesN_hit, hwLock_verweigert, kein_lock_schritt, hwTeilwort_keine_gruppe, hwGruppe_verweigert_bei_fremdeintrag, the hwWit witness family (anfang_null, weiterleitung, fremd_alt, spuelung_aendert_speicher, fremd_neu, Start, Adr, Mem, Wort, Overlap, LoadEigen, LoadFremd, NachFlush, FremdNachFlush, Overlap_keine_gruppe), plus canonical defs (tsoAnsicht, projZustand, setKernVonFp, FremdFrei, WortGruppe, DrainSpur, lesbar8, schreibbar8, issueByte, loadByte, hwWortAusgabe, hwLockAnfrage, SperrBefehl with xadd64, wortEintraege_laenge). The three substantial proofs (drain_bytes, write64_bytes, write64_trifft_drain) compose these with explicit byte-level reasoning; no second interpreter, no new IR, no duplicated model.
- Refusals genuine: four refusal theorems over LOCK, tearing, foreign footprint, and LOCK steps, each a direct application of an accepted refusal lemma. Three poison probes: probe_lock closes by rfl on a concrete xadd64 request (valid since hwLockAnfrage is a defined refusal in this model stage), probe_tear closes by decide on a 2-of-8 buffer, probe_overlap applies the accepted overlap no-group lemma.
- Witness non-degenerate: pipeTso_zeuge is a five-part conjunction over the accepted two-core witness run — initial byte 0, own-core forwarding of 42, foreign-core stale 0, post-drain 42 in actual shared memory observed from both cores. Memory-changing, two-core, joint premises.
- Silicon: no new hardware facts stated. Encodings, word shape, and drain equations all come from the accepted canonical definitions; the file adds no opcode, flag, or ordering claim of its own.
- CUTS honest, claim matches proof: the joint theorem claims word plus per-footprint-byte agreement between the SC store and the exclusion-checked grouped drain, explicitly not whole-memory equality. The CUTS block disclaims a full pipeline_correct lift, whole-word atomicity beyond grouped drains, LOCK paths, shared-atomic contracts, per-access W/GX simulation, fairness, progress, timing, budget, interrupts, devices, and anything beyond the pilot ISA and accepted definitions. No hardware-correspondence or W/GX overclaim. The register-path embedding excludes memory-changing steps by its hmem premise, as documented.

## Decision and reasons

VERDICT: ACCEPT

The new head meets the exact-review bar on every checklist item above: clean banned-token scan, standard axioms, exact 3-file scope with a one-line import, all premises used, accepted evaluator lifted rather than copied, refusals that genuinely refuse with deciding probes, a non-degenerate two-core memory-changing witness, no new silicon claims, and CUTS that state precisely what is and is not proved. The prior apparatus-only objection is resolved by the in-clone snapshot material reviewed here. No weakened guarantee and no desired-correctness premise was found.

## Build status

- This reviewer clone ./lean-bau: Build completed successfully (607 jobs), exit 0 with 0 error lines (run 2026-10-05; tree is base plus reviewer reports only, no author Lean code, hence 607 vs the author tree 608).
- Author evidence for the reviewed head: final ./lean-probe 0 errors with standard axioms; ./lean-bau 608 jobs green. The last full build ran on the exact Lean tree the pinned head contains (only the author report was committed afterwards).
- New definitions or theorems by lane 1170: none (report-only review). Reviewed author theorems are listed in the checklist above.

## Task remarks

Nothing in the author task appears wrong. The author scoping note is sound: post-drain agreement is word plus per-byte over the footprint rather than whole-memory equality, which would be false in general.

CUTS of this review: this report re-verifies the author claims by reading the pinned diff text and cross-checking every reused name against the accepted tree in this clone; it does not re-execute the author build (relying on the recorded 608-job green run) and proves nothing new about the pipeline itself.
