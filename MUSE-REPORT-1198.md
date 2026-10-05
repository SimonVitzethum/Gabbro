# MUSE-REPORT-1198: exact review of lane 1197 (block-level table reads, scaled-index addressing)

CANDIDATE: 1197 a4974696b782ad10184e27097dc728a084e6e1cb
VERDICT: ACCEPT

Re-review of the repaired candidate (previous verdict on
c3da85d5bce725a2dfb7379dbd4bda09f7a44d7b was REPAIR with R1-R4; this report
re-inspects the NEW pinned snapshot only). Reviewed material, all in-clone:
`.tmp/review/SNAPSHOT.json` (head above, base 4ed3590d85cf770cb098132aed8ee9752e29e013,
files MUSE-REPORT-1197.md + Grammatik.lean import line +
PipelineBlockTables.lean, clean true), `.tmp/review/author-1197/PATCH.diff`,
the snapshot copy of `PipelineBlockTables.lean` (now 1907 lines, +241),
author report (154 lines, with Review-1198 resolutions) and
`BUILD-EVIDENCE.json` including the two new tail entries. The candidate is NOT
applied in this clone (this lane owns only this report), so no candidate
build was run here; `./lean-bau` below is master state without the candidate.

## Resolution of every previous finding

R1 (missing `_zeuge` for correctness theorems): REPAIRED and verified. All
four now exist — `senkSkalLesen_korrekt_zeuge` (file line 1661),
`senkStmtSkal_korrekt_slot_zeuge` (1799),
`senkStmtSkal_korrekt_durch_zeuge` (1817), `senkStmtSkal_korrekt_zeuge`
(1834). Read in full: each instantiates ALL premises jointly on concrete
values (stride-8 anchor `ankerSkala8`, represented environments
`envReprSkal1`/`envReprSkal2`, rechecked world `worldRepSkal8` via decided
`tabOkSkal8`/`tabWeltSkal8`, checked bounds `bndSkal1`/`bndSkal2`,
lowering equations closed by kernel `rfl` in `lowSkal1`/`lowStmtSkal2`/
`lowDurchSkal2`) and carries the non-degeneracy beside it
(`zeV.schreibt false = true`, `zeRunChange`/`zeRunChangeProof`). CUTS lists
them as Done.

R2 (fetched-bytes closing theorem missing, header overclaim): REPAIRED as
explicitly allowed (narrow the header). The header now promises
statement-level correctness only and states the block closing theorem is OPEN
(file lines 14-17); `korrektBytes` has zero matches, `laufBytes`/`CodeAt`
appear only in reuse-list prose; CUTS keeps the closing theorem OPEN with
the exact missing piece (transport lemma + per-shape casing + future
`CodeAt` region). No overclaim remains.

R3 (no full-build evidence, stale base): REPAIRED as far as a lane can.
`BUILD-EVIDENCE.json` now ends with a `./lean-bau` entry:
`== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (627 jobs)`. The tail `./lean-probe` entry is
`== 0 error(s)` with the full `depends on axioms` info block. Base is still
4ed3590d (this clone's master builds 687 jobs); the candidate touches only
its 3 owned files, so rebase is the serial merge gate's mechanical job, not
a semantic risk.

R4 (axioms taken on word): RESOLVED by evidence. The probe/build outputs now
in evidence list every main theorem including the four new witnesses:
correctness theorems and all four `_zeuge` depend on exactly
`[propext, Classical.choice, Quot.sound]`; helpers on subsets; no `sorryAx`
anywhere. The merge gate still re-checks mechanically at integration.

## Checks (all re-run on the NEW snapshot)

C1 — No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in code. Grep
finds these tokens only inside prose "admitted" and `#print axioms` lines.
C2 — Existing files untouched except the single appended
`+import Grammatik.X86.PipelineBlockTables` in `grammatik/Grammatik.lean`
(PATCH touches exactly the 3 snapshotted files).
C3 — Accepted evaluator lifted, not copied (unchanged reuse of lane-1159
anchors/world, pipeline `kanon`/`lauf` machinery, `skaliertAddr`/`skalaOk`/
`adrOk`, machine steps; new imports are existing family modules only).
No second IR, no second interpreter, no per-program rule.
C4 — Refusals really refuse with joint non-degenerate witnesses (unchanged
section, re-confirmed: 7 shapes + 7 `.durch` corollaries, each `rfl`/`simp`
on the lowering def plus table-writing program and memory-changing run).
C5 — Silicon: no new encodings; SIB doubling proved (`skalExp_sound`),
`rsp` exclusion correct, pilot forms reused. No hardware-correspondence or
W/GX claim; single-core pilot scope needs no two-core witness.
C6 — CUTS honest (Done vs one OPEN item with the precise missing lemma);
premises spot-checked as used; English throughout.

## Build and lane notes

- `./lean-bau` on this clone (master, candidate NOT applied): last result
  line `Build completed successfully (687 jobs).`
- New definitions/theorems by this lane: none (report-only review).
- Nothing in the lane-1197 task text found wrong. Remaining work is the
  author's stated OPEN item (fetched-bytes closing theorem + its future
  `_zeuge`), correctly cut, not claimed.
- History: b9500e19 (no candidate visible), 7d94e990 (REPAIR on c3da85d5
  with R1-R4). This revision supersedes both with ACCEPT on the new head.
