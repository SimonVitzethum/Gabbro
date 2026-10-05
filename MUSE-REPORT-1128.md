# MUSE-REPORT-1128: Exact review of author lane 1127 (Multiply/divide and narrow widths connected)

CANDIDATE: 1127 935072659336e759445600f58328eaa776214d7f

## Scope and method

- Review-only lane. Owned file only: this report.
- Verified clone: `/home/simon/Dokumente/gabbro-muse/a1128`, branch `muse/1128`
  (checked via `.git/HEAD` -> `ref: refs/heads/muse/1128`).
- New pinned snapshot inspected: `.tmp/review/SNAPSHOT.json` names author 1127,
  head `935072659336e759445600f58328eaa776214d7f`,
  base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`, files
  `MUSE-REPORT-1127.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwMulDivWidth.lean`, clean true.
- This supersedes the prior stale review of head `28c3af54...`. The staged
  bundle `.tmp/review/author-1127/` was re-read in full for this pass: the
  870-line staged new file, the staged report (now with a review-response
  section stating Lean content is byte-identical to the prior head and only
  report text was added), the staged build-evidence trail (now with final
  green build plus the response commit), the staged owner task, and the
  staged patch header/scope. Per the new instruction every previous finding
  was re-inspected against the new material; the prior apparatus-only repair
  is resolved by the staged files and does not carry over.
- Review boundary: static exact review of the staged files plus the staged
  evidence trail. The author build was not re-executed here (applying the
  patch to `grammatik/` would break the own-only rule); the base tree in
  this clone was built instead (result below).

## What was checked

- Scope: staged patch contains exactly three file diffs (report, one import
  line appended at the end of `grammatik/Grammatik.lean`, one new 870-line
  file). No other existing file is touched.
- Banned tokens: full staged-file scan for banned tactics and toolchain
  violations finds none. The only matches are English prose (`admits`) and
  the required prints. No new machine, no redefined evaluator.
- Axioms: staged evidence prints standard axioms for all main theorems
  (`[propext, Quot.sound]`, witness well-formedness `[propext]` only).
- Premise use: selection theorems rewrite with their hypotheses, adapter
  theorems consume well-formedness and step hypotheses by case split, and
  the joint witness theorem refines with all twelve helper lemmas plus the
  lock refusal. No discarded hypotheses, no `Prop`-typed premises found.
- Lift, not copy: 64-bit width steps are proved equal to the accepted
  64-bit steps by `rfl` (four equations), 32/64-bit writes are proved equal
  to the accepted narrow merge by `rfl`, and the dispatcher and step
  functions call the accepted decoders and evaluators directly.
- No shadowing: ten unified-chain refusals of the new rows plus three
  overlap pins are machine-checked in-file, and dispatcher pins route the
  pilot, six new rows, and two overlap rows to the correct arm.
- Planted refusals: LOCK, 8-bit, and 16-bit-override rows are refused
  through the dispatcher with both-side evidence; zero-divisor halt and
  bad-length refusal are proved beside the run.
- Witness: the joint theorem conjoins thirteen facts — concrete divide and
  multiply results on two cores over one shared memory, owner-only
  forwarding, a drain that changes actual shared memory from 0 to 42
  observed from both cores, well-formedness, halt, refusal, and decode
  refusal. The drain is the memory-changing step. The family itself is
  register-only (proved in-file), so memory is exercised through the TSO
  issue/forward/drain path; this interpretation is stated openly in the
  author report and is the honest shape, not a deviation.
- Silicon spot check: divide-fault-as-halt with no successor state matches
  the reference behaviour (divide error arrives without program-state
  change); overlapping 64-bit rows keep the unified arm by machine-checked
  pins; no new silicon claim is made — the CUTS block names the inherited
  assumptions explicitly.
- CUTS and claims: the file ends with an honest CUTS block and per-theorem
  prints. No hardware-correspondence claim, no W/GX bridge claim, no
  source/loader/budget claim. The report matches the file.
- Builds: staged evidence ends green — final single-file probe zero errors,
  full build `Build completed successfully (601 jobs)`. The trail also shows
  intermediate red probes that were repaired during development, which reads
  as an honest working trail. This clone's base build (without author
  content) reports `Build completed successfully (602 jobs).`
- Observation, not a finding: this clone's local master
  (`d0be108c...`) differs from the snapshot base (`8744590d...`); the
  review covers the staged files, and base reconciliation belongs to the
  merge gate.

## New definitions/theorems

- None. This lane owns no Lean file and added none.

## Substantive outcome

VERDICT: ACCEPT

The new pinned head resolves the prior apparatus repair (full staged files
plus evidence trail present), the Lean delta versus the previously reviewed
head is report text only by the author's statement, and every checklist item
above passes on the staged content within the stated self-consistency
boundary. No unsupported correctness premise, no weakened guarantee, and no
claim larger than the proof was found.
