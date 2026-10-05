# MUSE-REPORT-1288: Exact review of lane 1287 (Memory types WC, WT, WP + cache-control)

## Task
Independent exact review of candidate lane 1287. Scope per `lanes/1288.md`:
no sorry/axiom/native_decide; `#print axioms` standard; existing files
untouched except one import line; every premise used; family accepted
evaluator lifted not copied; planted refusals really refuse; witness
non-degenerate (memory-changing step, two cores where relevant); silicon
facts against Intel SDM extracts; CUTS honest and no claim larger than the
proof (no hardware-correspondence or W/GX claim). Run `./lean-bau`, report
last result line. Exactly one machine-readable verdict line.

## Clone verification
- `pwd` = `/home/simon/Dokumente/gabbro-muse/a1288`,
  `git branch --show-current` = `muse/1288` (each verified with a single
  short command this session). Match: PASS.
- Owned file only: `MUSE-REPORT-1288.md`. No other file created or edited.

## Candidate identity

CANDIDATE: 1287 162a6d021e311bffc2ee516cfd39f6c84705fddf

- Pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 1287, head
  `162a6d021e311bffc2ee516cfd39f6c84705fddf`, base
  `738366545afbddf7ac664db92804703db24f8868`, files
  `MUSE-REPORT-1287.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwMemTypesWC.lean`, clean true.
- The task instruction requires reading `git diff master..HEAD` in the
  author clone `/home/simon/Dokumente/gabbro-muse/a1287` at the pinned HEAD.
  The pinned HEAD is now known from the snapshot above, but the candidate
  diff content is still not present inside this clone (the candidate files
  are absent here and the candidate git object cannot be inspected from
  this session), so no line-by-line review of the candidate was possible.
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

## Verdict

VERDICT: REPAIR
- This is a procedural REPAIR, not a semantic finding against the candidate:
  the exact review could not be carried out because (a) the candidate diff
  content is absent from this clone (candidate files not present; the
  candidate git object cannot be inspected from this session; only the
  pinned snapshot metadata above is available), and (b) no `git diff`
  against the candidate could be obtained and `./lean-bau` was not run, so
  the two mandatory review inputs (exact diff, build result line) are
  missing.
- Concretely required for a valid exact review: place the exact candidate
  export (the snapshot's three files at the pinned HEAD) inside the
  reviewer clone without violating the one-directory rule, and restore a
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
- The lane template's candidate placeholder was unfilled at dispatch; it was
  resolved during this format fix from `.tmp/review/SNAPSHOT.json` (head
  `162a6d021e311bffc2ee516cfd39f6c84705fddf`, see Candidate identity).
  The underlying one-directory problem remains: the task orders a diff read
  in the author clone while HARD RULES rule 1 forbids touching anything
  outside this directory.
