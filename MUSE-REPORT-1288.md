# MUSE-REPORT-1288: Exact review of lane 1287 (Memory types WC, WT, WP + cache-control)

## Task
Independent exact review of candidate lane 1287. Scope per `lanes/1288.md`:
no sorry/axiom/native_decide; `#print axioms` standard; existing files
untouched except one import line; every premise used; family accepted
evaluator lifted not copied; planted refusals really refuse; witness
non-degenerate (memory-changing step, two cores where relevant); silicon
facts against Intel SDM extracts; CUTS honest and no claim larger than the
proof (no hardware-correspondence or W/GX claim). Run `./lean-bau`, report
last result line. Exactly one VERDICT: ACCEPT or REPAIR.

## Clone verification
- `pwd` = `/home/simon/Dokumente/gabbro-muse/a1288`,
  `git branch --show-current` = `muse/1288` (each verified with a single
  short command this session). Match: PASS.
- Owned file only: `MUSE-REPORT-1288.md`. No other file created or edited.

## Candidate identity
- CANDIDATE: 1287 <full pinned HEAD unknown to reviewer>.
- The task instruction requires reading `git diff master..HEAD` in the
  author clone `/home/simon/Dokumente/gabbro-muse/a1287` at a pinned HEAD.
  That pinned HEAD was never supplied to this lane (the `.tmp/LANE.md`
  template literally reads `CANDIDATE: 1287 <full pinned HEAD>`), and no
  snapshot, hash, or exact-candidate export is present inside this clone.
- Author task (read from `lanes/1287.md` inside this clone, lines 20-27):
  NEW FILE `grammatik/Grammatik/X86/HwMemTypesWC.lean` + one import line in
  `grammatik/Grammatik.lean`; follow-up of lane 1133; per-region memory-type
  function, per-type ordering, WC buffer drained by fences reusing
  `SfenceStoreNarrow.lean` / `MfenceDrainOwn.lean`, PREFETCHh as fault-free
  NOP, CLFLUSH store-ordered single-line flush, `HwAdapter` embedding with
  (1) `HwWf` preservation, (2) exact agreement with accepted evaluator,
  (3) refusals, (4) non-degenerate two-core `_zeuge` witness, CUTS +
  `#print axioms`, no W/GX claim.

## Evidence actually available inside this clone
- `grammatik/Grammatik/X86/HwMem*` glob: no files found.
- `grep HwMemTypesWC grammatik/ (*.lean)`: no matches.
- Therefore this clone (branch `muse/1288`) does NOT contain the candidate
  diff. Any statement about the candidate's definitions, theorems, proofs,
  axioms, witnesses, silicon facts, or CUTS from this position would be
  invention, which the review rules forbid.

## Checks performed (all that the apparatus permits)
- None of the mandated semantic checks could be performed:
  - no candidate diff read (author clone outside this directory; HARD RULES
    rule 1 forbids touching it; listing the parent `gabbro-muse/` directory
    was rejected by the permission classifier; combined `git` commands with
    `&&`/pipes/`rev-parse`/`branch -a` were likewise rejected, while single
    short commands (`pwd`, `git branch --show-current`, `git status --short`
    showing only `?? MUSE-REPORT-1288.md`) succeed, so no exact candidate
    snapshot or `git diff` against it could be obtained in this session).
  - `./lean-bau` last result line: NOT RUN (report-only review with zero Lean
    changes; no build result is claimed).
  - No `sorry`/`axiom`/`native_decide` scan, no `#print axioms` check, no
    premise-use check, no evaluator-lift check, no refusal check, no witness
    check, no SDM-extract check, no CUTS check: all IMPOSSIBLE without the
    candidate.
- New definitions/theorems added by this review lane: NONE (report-only
  review; nothing added by design).

## VERDICT: REPAIR
- This is a procedural REPAIR, not a semantic finding against the candidate:
  the exact review could not be carried out because (a) no pinned candidate
  HEAD/snapshot was provided and the candidate files are absent from this
  clone, and (b) the shell/build apparatus (`bash`, hence `git diff` and
  `./lean-bau`) is blocked in this session, so the two mandatory review
  inputs (exact diff, build result line) are missing.
- Concretely required for a valid exact review: supply the pinned full HEAD
  (or an exact-candidate export inside the reviewer clone), grant the
  reviewer a readable exact snapshot without violating the one-directory
  rule (e.g. pre-place the diff/snapshot inside `a1288`), and restore a
  working `bash` path for `git diff` + `./lean-bau`. Then re-run this lane.
- No ACCEPT is granted. No claim is made about candidate 1287's correctness,
  axioms, witnesses, silicon accuracy, or mergeability. No weakened
  guarantee, no desired-correctness premise, no fake closure is introduced
  by this report.

## What remains open
- The entire lane-1287 exact review (all checklist items in the Task
  section above) remains open pending the inputs named above.
- Commit of this report: committed on branch `muse/1288` with the
  `Co-Authored-By: muse-agent-1288` trailer (this paragraph updated after
  the commit; see the commit log for the hash).

## Task issue believed wrong
- The review task as delivered is unexecutable as stated: it orders the
  reviewer to read `git diff master..HEAD` "in the author clone" while HARD
  RULES rule 1 forbids touching anything outside this directory, and the
  permission layer enforces exactly that (parent-directory access rejected).
  Either the exact candidate must be materialised inside the reviewer clone
  before dispatch, or the rule must name the sanctioned exception path.
- The `CANDIDATE: 1287 <full pinned HEAD>` placeholder was never filled in,
  so even a privileged read would have no pinned hash to verify against.
