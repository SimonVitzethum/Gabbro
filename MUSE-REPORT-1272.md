# MUSE-REPORT-1272 — exact review of candidate 1271 (blocked: candidate not inspectable)

## Identity
- Clone: `/home/simon/Dokumente/gabbro-muse/a1272` — verified.
- Branch: `muse/1272` — verified (`git branch --show-current`, `git status`).
- HEAD == master == `47c7ee1e` (`git rev-parse HEAD master` identical, `git log master..HEAD` empty).
- `git diff master..HEAD --stat` in this clone: empty. This clone contains no candidate work.

## What was requested
Review candidate lane 1271 ("Byte-level entry/call linkage for the start-anchored bridged run",
new file `grammatik/Grammatik/X86/TsoGxEntryBytes.lean` + import line + `MUSE-REPORT-1271.md`),
at pinned HEAD — but the task states `CANDIDATE: 1271 <full pinned HEAD>` with no hash,
so there is no pinned snapshot to check out or verify.

## Evidence gathered (inside this clone only, per HARD RULES isolation)
- `grammatik/Grammatik/X86/TsoGx*.lean` here: only `TsoGxStart.lean`, `TsoGxRefine.lean`,
  `TsoGxChecker.lean`. `TsoGxEntryBytes.lean` does not exist.
- No `MUSE-REPORT-1271.md` in the repository root (only `messung/muse/MUSE-REPORT-127.md` matches `MUSE-REPORT-127*.md`).
- The author task `lanes/1271.md` is present (it is the assignment, not the candidate).
- The author clone (`a1271`) is outside this directory: HARD RULES §1 forbids touching it,
  and the tool permissions deny external-directory access and `git fetch`, so the candidate
  diff cannot be obtained without violating isolation. No review-by-proxy was attempted;
  inferring acceptance from a missing diff is explicitly out of scope.
- This matches the precedent of lane 1258 vs candidate 1257 (commit `2f43e578`:
  "review blocked, candidate not inspectable").

## Checks performed
- None of the exact-review checks could run: no diff, no new theorems to axiom-check,
  no witness to verify, no refusal probes to test, no silicon facts to compare, no CUTS to read.
- `./lean-bau` on this clean clone (baseline only, NOT the candidate):
  first line `== exit 0; 0 error line(s) in the COMPLETE output`,
  last line `Build completed successfully (659 jobs).`
  This says the base tree is green; it says nothing about candidate 1271.

## VERDICT: REPAIR
Concrete reason: the review is blocked, not decided. The candidate snapshot was never
delivered to this lane — no pinned HEAD hash, no diff in this clone, and the author clone
is unreachable under the isolation rules. This verdict carries NO semantic finding about
lane 1271's work (no claim of sorry/axiom misuse, no witness defect, no silicon error:
nothing was inspected). ACCEPT is refused because granting it without evidence would be
a fabricated review.
Repair action for the coordinator: re-issue this review with a real pinned HEAD hash for
candidate 1271 and the candidate snapshot made available inside the reviewer clone
(fetch `muse/1271` before dispatch, or equivalent), then run the full exact-review gate
(sorry/axiom scan, `#print axioms`, premise use, evaluator reuse vs copy, refusal probes,
non-degenerate witness, SDM silicon check, CUTS honesty, `./lean-bau` on the candidate).
