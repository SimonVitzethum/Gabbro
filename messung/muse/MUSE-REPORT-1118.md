CANDIDATE: 1115 ae4b2d974db6139c0af294efb3e0b9e7da62594d

# MUSE-REPORT-1118: Independent exact-candidate review of lane 1115 (short-branch rel8)

Model: opencode-go/muse-spark-1.3-contributor. Review-only lane: no Lean file,
no doc, no counter changed. This reviews ONLY the new pin above (base
`41512d5a`, same 3 owned files); the old pin `0265e70c` is stale and its
REPAIR stands for those old bytes, unwithdrawn. The hash string is taken as
pinned by the coordinator in `.tmp/review/SNAPSHOT.json`; re-verifying it by
fetch is forbidden by HARD RULES rule 1, so it is trusted as pinned, not
independently re-fetched.

VERDICT: ACCEPT

## What was re-reviewed

The refreshed snapshot `.tmp/review/author-1115/`: `SNAPSHOT.json` (author
1115, new head `ae4b2d97`, `clean: true`), `PATCH.diff` (431 lines: the new
exact committed bytes — 318-line `ShortBranchEncoding.lean`, one import line
in `Grammatik.lean`, new `MUSE-REPORT-1115.md`), the repair report (91 lines),
and `BUILD-EVIDENCE.json` (352 lines: full iteration log ending in green).

## Finding-by-finding recheck (old F1-F6 vs new pin)

F1 (no green measurement of pinned commit): FIXED. Final pinned probe
(`BUILD-EVIDENCE.json:335`): `== 0 error(s) in the COMPLETE output; exit 0`.
Final pinned build (`:340`): `== exit 0; 0 error line(s)`, `Built
Grammatik`, `Build completed successfully (576 jobs)`. The tail `#print`
positions (file lines 304-316) coincide exactly with the committed file's
`#print` block (`PATCH.diff:416-428` = file lines 304-316), binding the green
result to the committed bytes.
F2 (`sorryAx`): FIXED on the new pin. Committed bytes grep-clean for
`sorry|admit|axiom|native_decide|unsafe` (only `#print axioms` lines match);
no `sorry` in source means no `sorryAx` in any axiom set. Final tail shows
only `[propext]`, `[propext, Quot.sound]`, or none (`:340`).
F3 (false report claims): FIXED. The new report lists exactly the committed
theorems (including the previously absent `decodeShortJcc_nichts_kurz`), and
its axiom table matches the pinned tail.
F4 (committed vs built bytes differed): FIXED per the line-coincidence above;
additionally the log shows the commit staged right after the green build
(`:344-350`: the two files staged following the green runs).
F5 (reviewer-side probe undone): CARRIED AS PROCESS NOTE, not a candidate
defect. Patch application in this clone remains classifier-denied (denial
from the previous round stands; no workaround attempted), so no reviewer-run
build line exists. Everything below rests on the pinned bytes plus the
pinned log, both inspected in-clone.
F6 (E8 + Jcc truncation missing): FIXED. Committed bytes now contain
`decodeShortJcc_nichts_kurz` generic over every `Bedingung`
(`PATCH.diff:192-210`), four E8 rows in both directions (`:269-299`),
canonical-`decode` refusal of both short witness strings (`:301-309`), and
`encodeShortJcc_opcode_all` (`:311-320`).

## Checks (1)-(6) on the new pin, with evidence

(1) Fidelity — PASS. Same three owned files (`SNAPSHOT.json:6-10`); the
`Grammatik.lean` hunk adds only the import (`PATCH.diff:98-106`); no
`Typen.lean`/`Befehl` change, no emission counter. Sixteen conditions covered
generically (`condCode`/`codeCond` invert, `Codec.lean:35-55`) with the
all-16 opcode-shape theorem and per-condition truncation refusal on top.
(2) Keywords/axioms — PASS. Grep-clean committed bytes (see F2); green
elaboration; standard-only axioms in the pinned tail.
(3) Witnesses — PASS. All three required names present on concrete values
(`PATCH.diff:354-378`): EB FE via `encodeShortJmp (-2)` (= `[235, 254]`),
74 05 via `encodeShortJcc Bedingung.e 5` (= `[116, 5]`), target `4096`.
Green in the final pinned runs.
(4) CUTS — PASS, honest. Claims only the proved rows, names the generic
disp round-trip as follow-up instead of claiming it (`PATCH.diff:393-398`),
keeps admission, lane 804/338, layout, hardware, source/TSO/ABI scope-outs.
The false "all proved" opener is gone.
(5) Builds — PASS on pinned evidence (final green probe + 576-job green
build quoted under F1); no reviewer-run line for the F5 reason.
(6) Byte substance — PASS. EB-vs-E9 tested explicitly both directions over
actual bytes (`decodeShortJmp_distinct_nearJmp` with a 233-headed input,
`decodeNearJmp_distinct_shortJmp` over `encode (.jump32 d)`); sign handling
computed through the reused `disp8Signed`, not asserted; the range theorems
conclude the two-sided bound with premise `h` genuinely used by `omega`;
out-of-range refused, never widened.

## New definitions/theorems by this lane

None. Review-only; nothing added, renamed, or weakened.

## Build lines on record (author pinned runs, not reviewer runs)

Probe (final): `== 0 error(s) in the COMPLETE output; exit 0` (only unused
simp-arg linter warnings). Build (final): `== exit 0; 0 error line(s) in the
COMPLETE output`, `Build completed successfully (576 jobs)`, with the
standard-only axiom tail quoted under F1/F2. No reviewer-run line exists, per
the carried F5 note. The log's long red-then-green iteration history
(unsolved goals converging to zero across entries) reads as authentic repair
work, and the final green positions coincide with the committed bytes.

## What remains open

Nothing on the candidate: all six checks pass on the new pin. Standing
process notes: reviewer-side re-execution in this clone still wants a
coordinator-provided path the classifier permits (F5); the owner verify path
naming clone `a1115` while reviewers are clone-confined stays load-bearing
for future dispatches, as does hash handoff with in-clone availability.

## History (preserved, not rewritten)

First dispatch: no candidate in this clone, correctly recorded as blocked
(`7dd899df`). Second dispatch: pin `0265e70c` reviewed on pinned bytes,
REPAIR with six concrete findings (`4a75fca3`) — that decision stands for
those bytes. Third dispatch (this report): new pin `ae4b2d97` re-reviewed
finding by finding; F1-F4 and F6 verified fixed, F5 carried as environment
note. No stale snapshot approved; no unproved claim accepted.
