# MUSE-REPORT-1272 — exact review of candidate 1271 (blocked: candidate not inspectable)

CANDIDATE: 1271 c73645e2f3b678c7ecef169c917a1dcf989c936d
VERDICT: REPAIR

## Identity
- Clone: `/home/simon/Dokumente/gabbro-muse/a1272` — verified.
- Branch: `muse/1272` — verified (`git branch --show-current`, `git status`).
- HEAD == master == `47c7ee1e` (`git rev-parse HEAD master` identical, `git log master..HEAD` empty).
- `git diff master..HEAD --stat` in this clone: empty. This clone contains no candidate work.

## What was requested
Review candidate lane 1271 ("Byte-level entry/call linkage for the start-anchored bridged run",
new file `grammatik/Grammatik/X86/TsoGxEntryBytes.lean` + import line + `MUSE-REPORT-1271.md`),
at its pinned HEAD. The lane task carried only a placeholder with no hash; the follow-up
format notice pointed at `.tmp/review/SNAPSHOT.json`, which pins author 1271 to
`c73645e2f3b678c7ecef169c917a1dcf989c936d` (base `c8bb42086282d1e2a7c5874a40303e7f060d3fad`,
files `MUSE-REPORT-1271.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/TsoGxEntryBytes.lean`, clean). The commit object is however absent
from this clone (`git show` reports bad object) and cannot be fetched under the isolation
rules, so the pinned snapshot still cannot be checked out or verified here.

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

## Verdict detail (substance unchanged)
Concrete reason: the review is blocked, not decided. The candidate snapshot was never
delivered to this lane — the pinned hash is now known but its objects are absent from
this clone, there is no diff here, and the author clone is unreachable under the
isolation rules. This verdict carries NO semantic finding about lane 1271's work
(no claim of sorry/axiom misuse, no witness defect, no silicon error: nothing was
inspected). Approving without evidence would be a fabricated review, so approval is refused.
Repair action for the coordinator: re-issue this review with the candidate snapshot
(`c73645e2f3b678c7ecef169c917a1dcf989c936d`) made available inside the reviewer clone
(fetch `muse/1271` before dispatch, or equivalent), then run the full exact-review gate
(sorry/axiom scan, `#print axioms`, premise use, evaluator reuse vs copy, refusal probes,
non-degenerate witness, SDM silicon check, CUTS honesty, `./lean-bau` on the candidate).
