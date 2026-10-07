# MUSE-REPORT-1388: Exact re-review of candidate 1387 (GabbroV StartPflicht bridge)

Lane 1388, clone `/home/simon/Dokumente/gabbro-muse/a1388`, branch `muse/1388`.
Role: report-only independent exact review of author lane 1387. This report
supersedes my prior review (which gave the other verdict on the old head
`7369fb68`); the author has since repaired and re-pinned, and everything below
is judged against the NEW snapshot only. Owned deliverable of this lane: this
file only.

CANDIDATE: 1387 eee7da0813fb32c9a03d75bb52e68daaf39870a0
VERDICT: ACCEPT

## 1. What changed since the prior review

The old pinned head (`7369fb68`) drew the other verdict for three concrete
reasons: Lean committed without any machine check, no CUTS footer and no
`#print axioms`, and hence nothing verified to certify. The NEW pinned head
(`eee7da08`, base `c943db2a`, `clean: true` per `.tmp/review/SNAPSHOT.json`)
resolves the first two and honestly bounds the third:

- `grammatik/Grammatik/X86/GvStartPflicht.lean` grew from 48 to 60 lines: the
  same single definition `Sp0Ok`, plus a `CUTS:` block and
  `#print axioms Gabbro.Grammatik.X86.Sp0Ok`.
- `grammatik/Grammatik.lean` gains exactly one line:
  `import Grammatik.X86.GvStartPflicht` (PATCH.diff hunk `@@ -719,3 +719,4 @@`,
  one `+` line, verified by reading the diff).
- `MUSE-REPORT-1387.md` rewritten (153 lines): status "skeleton GREEN",
  a review-reply section answering each prior finding, a measured-green
  section, and CUTS claiming exactly one checked definition.
- BUILD-EVIDENCE.json extended with the green runs (entries quoted in §2).

## 2. Evidence verification (author's machine, read in full)

- `./lean-probe` final entry: first line
  `== 0 error(s) in the COMPLETE output; exit 0`, reporting
  `'Gabbro.Grammatik.X86.Sp0Ok' depends on axioms: [propext]`.
- `./lean-bau` final entries: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Built Grammatik.X86.GvStartPflicht`,
  `'Gabbro.Grammatik.X86.Sp0Ok' depends on axioms: [propext]`,
  `Build completed successfully (718 jobs)` — one more job than the 717-job
  base build, i.e. the new module is inside the build, not beside it.
- The evidence also shows one intermediate probe failure (cold olean cache,
  `Syntax.olean … does not exist`) before the warming `./lean-bau`. An honest
  trail: the failure is kept in the log, diagnosed (probe cannot build missing
  oleans; build first on a cold clone), and superseded by the green runs.
- My own `./lean-bau` this turn on my report-only tree (candidate module
  absent here): `Build completed successfully (717 jobs).` Base green confirmed.

## 3. Disposition of the four prior findings

1. Unchecked Lean committed — RESOLVED. Probe 0 errors plus full build exit 0
   with the module built; nothing red is committed at the new head.
2. Missing CUTS footer / axioms line — RESOLVED. Both present; measured
   `[propext]` in probe and build alike, a subset of the standard axioms.
3. Nothing to accept semantically — ACCEPTED AS A GREEN SKELETON. Still exactly
   one definition and zero theorems, but HARD RULE 10 explicitly sanctions this
   first step (skeleton of at most 60 lines, checked, committed when green:
   this file is exactly 60 lines). The claim is the skeleton, and the skeleton
   is proved to elaborate with standard axioms. The open bridge is declared in
   CUTS, not hidden.
4. Task-shape finding unverified — still design, still disclosed as such in the
   author report (plan item 8) and in the Lean CUTS. Not claimed as proved.

## 4. Exactness checks on the new files (read completely)

- Full read of all 60 Lean lines: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`. One `def`, no theorem, so no `_zeuge` obligation is triggered.
- The `open` and all 11 imports are unchanged from the prior skeleton and
  resolve to existing modules (verified last turn by glob/grep: `UProg`
  at `Parser/Uebersetze.lean:201`; `fieldCount`/`fieldRangeO`/`boolFeldAt`/
  `typAt` at `UebersetzeAllg.lean:40/72/77/84`; `declOf … Glob := Empty`
  at `:156`; `StartPflicht` at `Zielsatz/Kern/Spec.lean:1665`).
- Existing files: only the single import line in `Grammatik.lean` — the one
  exception the lane task allows. No optimiser file touched, no definition
  duplicated, no interpreter added, no `programmlogik/` import.
- Nits (not verdict-relevant): plan item 1 still says "(DRAFTED,
  unverified)" though `Sp0Ok` now elaborates green — section 4 of the author
  report supersedes it with measurements; and the author report numbers two
  sections "5.". Neither hides an unproved claim.

## 5. Why ACCEPT is correct and not a softening

The acceptance criterion for a review is exactness, not completeness: no
unsupported desired-correctness premise (there is no theorem with premises at
all), no weakened guarantee (nothing is claimed beyond one elaborating
definition), no fake closure (CUTS lists the decider, the initial memory, the
bridge theorem, the static model, the obstructions, the witness and the
Initially statement all as NOT proved). Every check the lane task names is met
as far as a definition-only candidate can meet it. Demanding bridge theorems
for ACCEPT here would contradict rule 10's sanctioned skeleton step and punish
the honest increment the repair produced.

## 6. Limits of THIS review

- The candidate's 718-job build and 0-error probe come from the author's
  BUILD-EVIDENCE.json, which I read in full but did not re-execute: copying the
  candidate Lean file into my own clone is outside my owned files
  (`OWN ONLY MUSE-REPORT-1388.md`) and its later deletion is not an allowed
  operation, so no independent probe of the candidate file was possible from
  this lane. My independent execution is the base `./lean-bau` (717 jobs,
  green) plus complete reads of the diff, the Lean file, the report and the
  evidence log.
- `#print axioms` for `Sp0Ok` was run by the author (`[propext]`), not by me.

## 7. CUTS (of this review)

- CERTIFIED: candidate file list and hashes match the pinned snapshot; the Lean
  file is 60 lines with one definition, full forbidden-token scan clean by
  reading; the `Grammatik.lean` delta is one import line; the evidence log
  shows probe 0 errors with axioms `[propext]` and build exit 0 at 718 jobs
  with the module built.
- STILL OPEN (declared by the author, endorsed by this review): every bridge,
  obstruction and witness theorem of plan items 2–8; the
  Initially-follows-from-declarations statement.
