# MUSE-REPORT-1128: Exact review of author lane 1127 (Multiply/divide and narrow widths connected)

CANDIDATE: 1127 28c3af544cc83f25823b4ad675eaf7c24ea4bae8

## Scope and method

- Review-only lane. Owned file only: this report.
- Verified clone: `/home/simon/Dokumente/gabbro-muse/a1128`, branch `muse/1128`
  (checked via `.git/HEAD` -> `ref: refs/heads/muse/1128`; local ref
  `.git/refs/heads/muse/1128` present, `.git/refs/heads/master` = `d0be108c1da169cc1f616dfd096c9f86d691bc13`).
- Pinned snapshot inspected: `.tmp/review/SNAPSHOT.json` names author 1127,
  head `28c3af544cc83f25823b4ad675eaf7c24ea4bae8`,
  base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`, files
  `MUSE-REPORT-1127.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwMulDivWidth.lean`, clean true.
- Author task (from `lanes/1127.md` in this clone): NEW FILE
  `grammatik/Grammatik/X86/HwMulDivWidth.lean` plus one import line in
  `grammatik/Grammatik.lean`; connect `MulDivWidthHardwareForms.lean` /
  `MulDiv.lean` narrow/width rows into the `ExtendedExecution` unified byte
  dispatcher and a `HwAdapter`, reusing `HwRegAusgang`, with proofs of
  (1) `HwWf` preservation, (2) exact agreement with the family evaluator,
  (3) refusals, (4) non-degenerate multi-step witness with joint theorem.
- This update keeps the prior substantive finding and only repairs the
  machine-readable format gate. No claim is approved without proof.

## What was checked

- Searched this clone for the author artefact:
  `grammatik/Grammatik/X86/HwMulDivWidth.lean` — NOT FOUND.
- Grepped `grammatik/` for `HwMulDivWidth|MulDivWidthHardwareForms`: only two
  hits — the `import Grammatik.X86.MulDivWidthHardwareForms` line in
  `grammatik/Grammatik.lean:486` and the family file header itself. No
  `HwMulDivWidth` definition, theorem, or import exists here.
- Local refs contain only `master` and `muse/1128`; there is no local
  `muse/1127` branch to diff. HARD RULES rule 1 forbids touching anything
  outside this directory (no access to the author clone, no network/fetch),
  so the prescribed diff in the author clone could not be performed from here.
- The pinned snapshot metadata above was inspected, but the full pinned diff
  was not verified line by line inside this clone in this pass.
- Ran the queued build wrapper: `./lean-bau` (base tree, without author
  content). Result line: `Build completed successfully (602 jobs).` with
  header `== exit 0; 0 error line(s) in the COMPLETE output`.
- None of the mandated exact-review checks could be completed on the author
  content from inside this clone: banned-tactic scan, standard axioms print,
  one-import-line discipline, premise use, evaluator lift (not copy), planted
  refusals, non-degenerate witness (memory-changing step, two cores where
  relevant), silicon facts against Intel SDM extracts, honest CUTS, and no
  overclaim beyond self-consistency (in particular no hardware-correspondence
  or W/GX claim). The prior report stands on all of these as unverified.

## New definitions/theorems

- None. This lane owns no Lean file and added none.

## Substantive outcome

VERDICT: REPAIR

Concrete reasons (each sufficient to withhold acceptance):

1. The exact author diff at the pinned head was not available for line-by-line
   verification inside the owned clone under the HARD RULES. The expected
   file `grammatik/Grammatik/X86/HwMulDivWidth.lean` is absent here, no
   `HwMulDivWidth` symbol is referenced anywhere in `grammatik/`, and no
   `muse/1127` ref exists locally.
2. Consequently none of the mandated exact-review checks listed above could
   be executed against the author content. Accepting on snapshot metadata
   alone would be exactly the fake closure the task forbids, so the honest
   outcome remains repair, not approval.
3. Format history (not substance): the previous revision of this report was
   rejected by the format gate for lacking a unique machine-readable outcome
   line. This revision adds the required plain lines without changing the
   substantive finding.

## What remains open

- Make the exact author diff at the pinned head available to the reviewer
  without breaking clone isolation (for example stage the pinned files or the
  pinned diff through the coordinator channel into the review clone), then
  re-run this exact review against that pinned content through the full
  checklist above, including the build on the author tree.
- The base-tree build here is green at 602 jobs; nothing about author lane
  1127 follows from that.

## Task correctness notes

- The review task as issued orders a diff in the author clone while HARD
  RULES rule 1 restricts the reviewer to its own directory. The pinned
  snapshot resolves the missing-pin part, but the isolation conflict remains
  for the diff itself. This is an apparatus defect, not a finding about the
  author's work, which was not visible here.
- No hardware-correspondence or W/GX bridge claim is made or assessed here.

## CUTS

- Author lane 1127 unverified by this lane: all four required properties (HwWf
  preservation, exact family-evaluator agreement, refusals, non-degenerate
  witness) plus silicon, axioms, premise-use, CUTS-honesty and no-overclaim
  checks remain unverified here.
- No new theorems in this lane, hence no axioms print for this lane. Base
  build `./lean-bau` reports `== exit 0; 0 error line(s) in the COMPLETE
  output` and `Build completed successfully (602 jobs).`
