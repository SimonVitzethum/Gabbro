# MUSE-REPORT-1128: Exact review of candidate 1127 (Multiply/divide and narrow widths connected)

## Scope and method

- Review-only lane. Owned file only: this report.
- Verified clone: `/home/simon/Dokumente/gabbro-muse/a1128`, branch `muse/1128`
  (checked via `.git/HEAD` -> `ref: refs/heads/muse/1128`; local ref
  `.git/refs/heads/muse/1128` present, `.git/refs/heads/master` = `d0be108c1da169cc1f616dfd096c9f86d691bc13`).
- Task text: "Read the candidate diff only (`git diff master..HEAD` in the author
  clone, pinned HEAD)". Candidate line: `CANDIDATE: 1127 <full pinned HEAD>`.
- Author task (from `lanes/1127.md` in this clone): NEW FILE
  `grammatik/Grammatik/X86/HwMulDivWidth.lean` + one import line in
  `grammatik/Grammatik.lean`; connect `MulDivWidthHardwareForms.lean` /
  `MulDiv.lean` narrow/width rows into `ExtendedExecution` unified byte
  dispatcher and a `HwAdapter`, reusing `HwRegAusgang`, with proofs of
  (1) `HwWf` preservation, (2) exact agreement with the family evaluator,
  (3) refusals, (4) non-degenerate multi-step `_zeuge` witness.

## What was checked

- Searched this clone for the candidate artefact:
  `grammatik/Grammatik/X86/HwMulDivWidth.lean` — NOT FOUND.
- Grepped `grammatik/` for `HwMulDivWidth|MulDivWidthHardwareForms`: only two
  hits — the `import Grammatik.X86.MulDivWidthHardwareForms` line in
  `grammatik/Grammatik.lean:486` and the family file header itself. No
  `HwMulDivWidth` definition, theorem, or import exists here.
- Local refs contain only `master` and `muse/1128`; there is no local
  `muse/1127` branch to diff. HARD RULES rule 1 forbids touching anything
  outside this directory (no access to the author clone, no network/fetch),
  so the prescribed `git diff master..HEAD` in the author clone could not be
  performed from here.
- A `git branch` probe for further refs was rejected by the permission
  classifier; directory/ref inspection above was done with read-only file
  tools instead.
- Ran the queued build wrapper: `./lean-bau` (base tree, without candidate).
  Result line: `Build completed successfully (602 jobs).` with header
  `== exit 0; 0 error line(s) in the COMPLETE output`.
- No `sorry`/`axiom`/`native_decide` review, no `#print axioms` check, no
  premise-use check, no evaluator-lift check, no refusal-probe check, no
  witness/silicon/CUTS check was possible: there is no candidate content in
  this clone to check.

## New definitions/theorems

- None. This lane owns no Lean file and added none.

## VERDICT: REPAIR

Concrete reasons (each sufficient to withhold ACCEPT):

1. No pinned candidate HEAD. The task gives `CANDIDATE: 1127 <full pinned HEAD>`
   with the hash unfilled, so there is no exact, verifiable review target.
2. No candidate diff available inside the owned clone under the HARD RULES.
   The expected file `grammatik/Grammatik/X86/HwMulDivWidth.lean` is absent,
   no `HwMulDivWidth` symbol is referenced anywhere in `grammatik/`, and no
   `muse/1127` ref exists locally. Reading the author clone at
   `/home/simon/Dokumente/gabbro-muse/a1127` would violate HARD RULES rule 1.
3. Consequently none of the mandated exact-review checks could be executed:
   no-sorry/axiom/native_decide, standard `#print axioms`, one-import-line
   discipline, premise use, evaluator lift (not copy), planted refusals,
   non-degenerate witness (memory-changing step, two cores where relevant),
   silicon facts against Intel SDM extracts, honest CUTS, no W/GX or
   hardware-correspondence overclaim. An ACCEPT on this evidence would be
   exactly the fake closure the task forbids.

## What remains open

- Supply a complete pinned HEAD for candidate 1127 (full 40-hex hash) and make
  the exact diff available to the reviewer without breaking clone isolation
  (e.g. fetch the author branch into the review clone through the coordinator
  channel, or re-issue the review with the candidate merged to a staging ref).
- Re-run this exact review against that pinned diff through the full checklist
  above, including `./lean-bau` on the candidate tree.

## Task correctness notes

- The review task is internally inconsistent as issued: it orders `git diff
  master..HEAD` "in the author clone" while HARD RULES rule 1 restricts the
  reviewer to its own directory. With the literal placeholder pin, the only
  honest outcome is REPAIR. This is a task/apparatus defect, not a verdict on
  the author's work, which was not visible here.
- Base-tree note (not a candidate finding): `./lean-bau` on this clone is
  green at 602 jobs, so the family-disconnected baseline described in
  `lanes/1127.md` still builds; nothing about candidate 1127 follows from that.

## CUTS

- Candidate 1127 unreviewed: all four required properties (HwWf preservation,
  exact family-evaluator agreement, refusals, non-degenerate witness) plus
  silicon, axioms, premise-use, CUTS-honesty and no-overclaim checks remain
  unverified by this lane.
- No hardware-correspondence or W/GX bridge claim is made or assessed here.

## Axioms

- No new theorems, hence no `#print axioms` output for this lane. Base build
  `./lean-bau` reports `== exit 0; 0 error line(s) in the COMPLETE output`
  and `Build completed successfully (602 jobs).`
