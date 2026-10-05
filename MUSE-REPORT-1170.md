# MUSE-REPORT-1170: Exact review of author 1169 (Pipeline correctness over the multi-core TSO machine)

CANDIDATE: 1169 e6c872267c89f294bb495eb801747ea38a83869f

Clone: /home/simon/Dokumente/gabbro-muse/a1170, branch muse/1170 (verified via earlier allowed git rev-parse plus branch and log calls; toplevel and branch matched the task, so did not STOP).
Owns only: MUSE-REPORT-1170.md. No Lean file created or edited; no existing file touched.
Pinned snapshot inspected: .tmp/review/SNAPSHOT.json names author 1169, head e6c872267c89f294bb495eb801747ea38a83869f, base 062b979a6271b7b3044ab06be3f3cde411a0d4f1, files MUSE-REPORT-1169.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/PipelineTso.lean, clean true.

## Author scope (from lanes/1169.md in this clone)

- New file grammatik/Grammatik/X86/PipelineTso.lean plus one import line in grammatik/Grammatik.lean.
- Claim to prove: single-core pipeline run embeds into HwMaschine on core c with FremdFrei, TSO buffering transparent by forwarding, drained memory outcome equals source.
- Required shape: lowering plus validator, entry-style correctness theorem over execBlock and loaded-image byte run, refusal theorem for uncovered shapes, poison probes per refusal, non-degenerate zeuge with memory-changing step, CUTS plus print-axioms lines. Reuse accepted definitions unchanged, no second source interpreter, reserved optimiser files untouched, unsupported shapes refused never guessed, Rust out of scope.

## What was checked

- Read .tmp/LANE.md, lanes/1170.md, lanes/1169.md and .tmp/review/SNAPSHOT.json, all inside this clone.
- Verified clone path and branch (see above).
- Confirmed owned-file scope: only MUSE-REPORT-1170.md written; nothing else touched.
- Globbed grammatik/Grammatik/X86/Pipeline files in this clone: only Pipeline.lean, PipelineImage.lean, PipelineEntry.lean, PipelineWitnesses.lean, PipelineImageWitnesses.lean. PipelineTso.lean absent here; author report absent at root. Reviewer branch holds no author changes by design.
- Attempted in-clone git inspection of the pinned head and the base-to-head diff (cat-file, diff stat, branch list, status): each such bash call was rejected by the permission classifier, so the exact diff text could not be displayed in this session. The earlier allowed git rev-parse, branch show, log, add, and commit.sh calls worked.
- Ran ./lean-bau in this clone (see Build status).

## Review checklist (all unverifiable without the diff text)

- Banned tactics and axioms (sorry, admit, axiom, native_decide, unsafe) absent: NOT CHECKED, diff unavailable.
- Print-axioms lines standard: NOT CHECKED.
- Existing files untouched except one import line: NOT CHECKED.
- Every premise used, no desired-correctness premise, no weakened guarantee: NOT CHECKED.
- Accepted family evaluator lifted not copied: NOT CHECKED.
- Refusal theorems really refuse, poison probes present and positive probes pass: NOT CHECKED.
- Witness non-degenerate with memory-changing step and two-core relevance where applicable: NOT CHECKED.
- Silicon facts on encodings, fault classes, and ordering against Intel SDM extracts: NOT CHECKED.
- CUTS honest, no claim larger than proof, in particular no hardware-correspondence or W/GX overclaim: NOT CHECKED.

## Decision and reasons

VERDICT: REPAIR

The author work cannot be accepted on this evidence. Concrete actionable reasons:

1. Exact diff unavailable to this reviewer. The pinned head is known from SNAPSHOT.json, but the three pinned files are absent from this clone and every in-clone attempt to display the pinned commit or its diff was denied at the tool gate. HARD RULES 1 forbids touching anything outside this directory, so the author clone could not be consulted either. Without the diff text none of the checklist items above can be discharged.
2. Earlier task text left the pinned head as an unfilled placeholder, which is now resolved by SNAPSHOT.json for any re-issue; the re-run should additionally make the diff text itself available inside the reviewer clone or grant an explicit read-only path for the exact pinned commit.
3. No independent build of the author tree was possible here; ./lean-bau below covers only this reviewer clone (master plus this report, no author Lean code).

No Lean definitions or theorems were added by lane 1170 (report-only review), so there are no new names and no zeuge obligation on this lane. Nothing here approves any unproved claim.

## What remains open

- Re-run the exact review with the pinned head above and the diff text readable inside the reviewer clone, then replace this blocked decision with an ACCEPT or a content-based repair citing concrete file and line findings.
- Suggested harness fix: the format gate should pass the snapshot path and the required plain-line format to reviewers up front (as this follow-up did), and reviewer git-read access to the exact pinned commit should be pre-authorized so display commands are not denied.

## Believed-wrong in the task

- The original lane text named the review target with an unfilled placeholder instead of the pinned head from SNAPSHOT.json.
- The review instruction (read the diff in the author clone) conflicts with HARD RULES 1 (touch nothing outside this directory) as written for this blocked run.

## Build status

- ./lean-bau last result line in this clone: Build completed successfully (607 jobs), header == exit 0 with 0 error lines in the COMPLETE output (run 2026-10-05; tree state master plus this report only). The print-axioms lines visible in that output belong to pre-existing HwStackCalls.lean master content, not to author 1169 material.
- New definitions and theorems by this lane: none.
- Commit: through ./commit.sh on branch muse/1170.

CUTS: this report proves nothing; it is a blocked-review record. The pipeline-TSO correctness claim (single-core embed into HwMaschine, FremdFrei, forwarding transparency, drain equality, refusals, witness, silicon correspondence, no W/GX overclaim) remains OPEN.
