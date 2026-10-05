# MUSE-REPORT-1254: Exact review of candidate 1253 — BLOCKED (no candidate accessible)

## Clone / branch verification
- Clone: `/home/simon/Dokumente/gabbro-muse/a1254` — matches task.
- Branch: `muse/1254` (`bd57fa7cff467a2c700a02b50775e6d14530ae9b`), currently identical to `master`.
- Owned file only: `MUSE-REPORT-1254.md` (this file). No other files created or modified.

## What was attempted
- Re-read `.tmp/LANE.md` and `lanes/1254.md` (task: report-only exact review of CANDIDATE 1253).
- Read `lanes/1253.md` inside own clone for task context (author task: NEW FILE
  `grammatik/Grammatik/X86/TsoGxStart.lean` + one import line; follow-up of lane 1215
  `TsoGxRefine.lean`; entry/call prefix from `RufStartG`, joint non-degenerate `_zeuge`).
- Tried to obtain the candidate pinned HEAD / diff via the author clone
  (`/home/simon/Dokumente/gabbro-muse/a1253`, `git diff master..HEAD`).
  The tool call was rejected by the permission classifier, and HARD RULES rule 1
  forbids touching anything outside this directory in any case.
- Task text gives the candidate as `CANDIDATE: 1253 <full pinned HEAD>` — a placeholder,
  not an actual commit hash. There is no pinned hash to verify against, and own branch
  `muse/1254` equals `master`, so there is no candidate diff in this clone either.

## Checks performed
- `./lean-bau` on own clone (baseline `master`): green.
  Last result line: `Build completed successfully (651 jobs).`
  First line: `== exit 0; 0 error line(s) in the COMPLETE output`.
- No candidate Lean file exists in this clone (`grammatik/Grammatik/X86/TsoGxStart.lean`
  absent — as expected, it belongs to lane 1253). No review checklist items
  (sorry/axiom/native_decide, `#print axioms`, premise use, evaluator lifting,
  planted refusals, witness non-degeneracy, silicon facts, CUTS honesty) could be
  executed against the candidate because the candidate bytes were never available.

## VERDICT
- No ACCEPT / REPAIR verdict is given: rendering either one without reading the pinned
  candidate diff would be fake closure, which the task itself forbids
  ("no fake closure", "no claim larger than the proof").
- If forced into the ACCEPT-or-REPAIR schema, the honest entry is REPAIR-BY-DEFAULT
  ONLY in the sense of "not accepted — evidence missing", NOT as a judgment on the
  author's work. I record it as BLOCKED rather than laundering it as a reviewed REPAIR.

## Precise blocker
1. Missing pinned candidate hash: `<full pinned HEAD>` is not a hash; exact review
   requires the full pinned HEAD to check `git diff master..HEAD` at that commit.
2. Author clone not readable from this lane: direct access to
   `/home/simon/Dokumente/gabbro-muse/a1253` was permission-rejected, and HARD RULES
   rule 1 prohibits leaving `/home/simon/Dokumente/gabbro-muse/a1254` anyway.
3. The correct delivery path (coordinator pasting the pinned hash + making the diff
   available inside this clone, or running the review where the candidate is checked out)
   did not happen for this lane.

## What remains open
- Re-issue lane 1254 (or a successor review lane) with: (a) the full pinned HEAD hash of
  candidate 1253, (b) the candidate diff reachable without leaving the reviewer clone
  (e.g. fetched branch `muse/1253` at the pinned hash inside the reviewer clone, or the
  review executed in a clone that has the candidate checked out).
- Then the full checklist from `lanes/1254.md` line 23 can be run: sorry/axiom scan,
  `#print axioms` standard, one-import-line rule, premise use, evaluator lift vs copy,
  planted refusals, non-degenerate witness (memory-changing step, two cores where
  relevant), silicon vs Intel SDM extracts, CUTS honesty, `./lean-bau` on the candidate,
  and exactly one ACCEPT/REPAIR.

## Task correctness notes
- `lanes/1254.md` line 20 titles this lane "Start-anchored bridged run for the GX
  refinement" (the author title) while the body is an independent exact review —
  misleading but harmless; the body controls.
- Line 25's `CANDIDATE: 1253 <full pinned HEAD>` placeholder should have been filled
  with the real hash before dispatch; without it the lane cannot proceed by design.
- "Read the candidate diff only (`git diff master..HEAD` in the author clone...)"
  conflicts with HARD RULES rule 1 ("Touch nothing outside this directory") as written;
  future review lanes should state how the candidate reaches the reviewer clone.

## Definitions / theorems added
- None (report-only review lane; no Lean work permitted beyond the report).
