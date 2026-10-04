CANDIDATE: 1115 0265e70cdda9dea4256639a4a8e0c69cbae197ed

# MUSE-REPORT-1118: Independent exact-candidate review of lane 1115 (short-branch rel8)

Model: opencode-go/muse-spark-1.3-contributor. Review-only lane: no Lean file,
no doc, no counter changed. The hash above is taken as pinned by the
coordinator in `.tmp/review/SNAPSHOT.json` (pinned base `41512d5a` matches
this clone); re-verifying the hash by fetch is forbidden by HARD RULES rule 1,
so the string is trusted as pinned, not independently re-fetched.

VERDICT: REPAIR

## What was reviewed

The pinned snapshot `.tmp/review/author-1115/`: `SNAPSHOT.json` (author 1115,
head `0265e70c...`, 3 files, `clean: true`), `PATCH.diff` (308 lines: the
exact committed bytes), `MUSE-REPORT-1115.md` (58 lines: green claims),
`BUILD-EVIDENCE.json` (author probe/build log), `OWNER-TASK.md` (task copy).
Identity: clone `/home/simon/Dokumente/gabbro-muse/a1118`, branch `muse/1118`.
This supersedes the earlier blocked status from the first dispatch (no
candidate supplied then); the review below is on the pinned bytes, and the
earlier finding is preserved in the history note at the end.

## Check results with file:line evidence

(1) Task fidelity — scope PASS, completeness FAIL. Committed files are exactly
the three owned ones (`SNAPSHOT.json:6-10`; import hunk `PATCH.diff:66-74`):
no `Typen.lean`/`Befehl` change, no emission counter. All-16-conditions shape
is generic over `condCode`/`codeCond` (`Codec.lean:35-55` covers codes 0-15),
but unproven. Truncation refusal exists in committed bytes only for JMP
(`PATCH.diff:155-158`); the claimed `decodeShortJcc_nichts_kurz`
(`MUSE-REPORT-1115.md:23`) is absent from the committed bytes. The owner task
names near forms E9, E8, `0F 80+cc`; committed rows cover E9 and `0F 80+cc`
both directions only, no E8 row.

(2) Forbidden keywords / axioms — FAIL. Committed bytes grep-clean for
`sorry|admit|axiom|native_decide|unsafe` (only `#print axioms` lines match),
and every helper name resolves in-tree (`codeCond`/`condCode_lt` at
`Codec.lean:42,54`; `byteNat_natByte_of_lt/mod` at `Codec.lean:64,80`;
`leBytes32` at `Codec.lean:91`; `disp8Signed` at `Rel8Reach.lean:53`;
`exact_mod_cast`/`simp_all` have in-tree precedent). But the pinned axiom
dumps show `sorryAx` on the built variant (`BUILD-EVIDENCE.json:94-95,125`:
`decodeShortJcc_nichts_kurz`, all four distinctness theorems, both
`ziel_schranke`, all three witnesses), and standard axioms were never measured
on the committed bytes. The author-report claim of standard-only axioms
(`MUSE-REPORT-1115.md:42,48`) is contradicted by the author's own pinned log.

(3) Witness companions — names present, proofs not green. All three required
names exist in committed bytes (`PATCH.diff:248-271`); every pinned run leaves
them red, with `sorryAx` in both pinned `lean-bau` dumps. FAIL.

(4) CUTS honesty — internally contradictory. The block exists and names the
admission, relocation-decision and lane 804/338 boundary (`PATCH.diff:273-291`),
but opens with "All required theorems proved", which is false on every pinned
measurement. PARTIAL FAIL.

(5) Builds — FAIL. Pinned author runs: every `./lean-probe` red with 19-36
errors and exit 1 (`BUILD-EVIDENCE.json:10,15,20,25,30,35,40,45,50,55,60,65,70,
75,80,85,100,105,110,115,120`); `./lean-bau` with the candidate exits 1 with
`Grammatik.X86.ShortBranchEncoding` failed (`:94-96,123-126`); the single
green `./lean-bau` (575 jobs, `:88-90`) predates the candidate file. No
independent reviewer probe of the exact commit was possible: applying the
pinned patch in this clone (`git apply`) was denied by the permission
classifier, and working around a classifier denial is forbidden, so no
workaround was attempted. No build result of mine is claimed.

(6) Byte-level substance — unproven. The EB-vs-E9 confusion statements exist
(`PATCH.diff:161-167,188-197`), sign handling computes via `disp8Signed` plus
`rip+len+disp` target defs (`PATCH.diff:104-110,218-223`), out-of-range refusal
is stated (`PATCH.diff:240-245`) — but none of it ever compiled green in any
pinned run. FAIL.

## Findings for lane 1115 (concrete repair items)

F1. No green measurement of the pinned commit exists anywhere in the pinned
evidence; the only green build predates the candidate file.
F2. `sorryAx` in the pinned axiom dumps for the truncation, distinctness,
range and witness theorems — HARD RULES rule 3 breach on the built variant.
F3. `MUSE-REPORT-1115.md` claims 0 probe errors, 576 green jobs,
standard-only axioms, no `sorry`, and lists `decodeShortJcc_nichts_kurz` —
each contradicted by the author's own pinned log or the committed bytes.
F4. Committed bytes differ from built bytes (theorem set and `#print` line
positions differ: built 258-273 vs committed 213-225), so the exact pinned
commit was never validated in the form it would merge.
F5. Reviewer-side independent probe of the exact commit remains undone for
the classifier reason stated under check (5), not for lack of trying.
F6 (minor). E8 near-call distinctness and Jcc truncation refusal missing from
the committed rows although the owner task names them.

Repair: remove every `sorry`, prove the committed bytes (no silent rewrites),
reach probe 0 errors and full green build, correct each false report claim,
re-pin; the review then re-runs on the new pin. Nothing was rewritten here.

## New definitions/theorems

None. Review-only lane; nothing added, nothing renamed, nothing weakened.

## Build lines on record (author pinned runs, not mine)

Probe (last pinned entry): `== 36 error(s) in the COMPLETE output; exit 1`.
Build (last pinned entry): `== exit 1; 38 error line(s) in the COMPLETE
output` with `error: build failed` on `Grammatik.X86.ShortBranchEncoding`.
No reviewer-run line exists for the reason in check (5).

## What remains open

Re-review on a new pin after the repair; an in-clone reviewer probe of the
exact commit still requires a coordinator-provided path that the classifier
permits. Task-side note (unchanged): the owner verify path points at clone
`a1115` while reviewers are confined to their own clone, so hash handoff plus
in-clone availability stays load-bearing; the pinned evidence paths also
reference a different machine layout (`.../Gabbro/.claude/muse-arbeit/kratz/`),
which is recorded as provenance, not as a finding.

## History (preserved)

First dispatch: no candidate hash or bytes in this clone; review correctly
recorded as blocked (commit `7dd899df`). Second dispatch: pinned snapshot
supplied; substantive review above performed on the pinned bytes. The blocked
record stands as history; nothing in it was rewritten to satisfy formatting,
and nothing unproved is approved above.
