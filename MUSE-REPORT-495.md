# Muse report 495: independent exact-candidate review of 415

Clone: `/home/simon/Dokumente/gabbro-muse/a495`, branch `muse/495` (verified).
Candidate base `0b3132b7` exists in this clone; candidate HEAD
`78d57179879cb076a20e5115e5bfd747ac9abf7f` is not present (no fetch per
hard rules). Reviewed the supplied `.tmp/review/SNAPSHOT.json`,
`.tmp/review/author-415/` (OWNER-TASK.md, PATCH.diff, BUILD-EVIDENCE.json,
MUSE-REPORT-415.md, full audit text) against the actual tree.
Own file only: `MUSE-REPORT-495.md`. Nothing else touched; tree was clean
before and after.

## What was done

- Confirmed scope: PATCH.diff touches exactly two files,
  `MUSE-REPORT-415.md` (new) and `dokumente/x86/AUDIT-END-TO-END-TRUST.md`
  (new). No Lean, Rust, emitter, checker, Spec, friend, or config path
  touched. Scope clean.
- Confirmed the three focus modules are byte-identical between the
  candidate base `0b3132b7` and this clone's HEAD (`git diff --stat base
  HEAD` over the three files plus QUELLBRUECKE.md: empty), so every
  citation was checked against the exact version the author read.
- Verified every checkable claim in delivered sections 0-3 by direct read:
  Bild.lean canonical theorems (99-113, cited 98-117), mapping/disjointness
  helpers, `wohlgeformt` (260-272), loaded-memory facts (283-324), all four
  refusal theorems (395/411/420/431), witnesses incl. `schreibLese_zeuge`
  (454) and `zeugenByte_geladen` (byte 9 at 0x2000, confirmed in source),
  CUTS at 529, 26 `#print axioms` lines (551-576, counted 26). Byteschritt.lean
  `fetchCap = 15`, `byteschritt` takes only the state (70-76), all cited
  theorems at 81/94/121/144/157/185/195/203/214/227, witnesses at
  339/358/396/421/445, CUTS at 452. InvariantenOpt.lean `isWahrAll` (46-52,
  no `nicht` arm confirmed), soundness chain at 68/79/95/113/140,
  folding/widening at 188/192/199, trace-transfer theorems at 215/228/261,
  `InvScope` at 250, `_zeuge` companions at 428-505, CUTS at 517.
  Zero real `sorry|admit|axiom|native_decide|unsafe` hits in all three
  modules (only English "admits" in comments). All correct.
- Verified section 0's closing shape against accepted
  `dokumente/x86/QUELLBRUECKE.md` section 4: the `valX86_sound` /
  `schluss_x86_aus_verfeinerung` (internal-only `hR`) / delivered
  `schluss_x86` split matches, including the 2026-10-01 review-repair note
  that the delivered theorem takes no independent refinement premise. The
  "NONE exists as a Lean definition" claim holds for the closing chain
  (`TableLayout.layoutOk` at TableLayout.lean:80 is a different,
  table-layout predicate, not `layoutOk(Gn, B, Img)`; the `valX86_sound` /
  `schluss_x86` sketches in QUELLBRUECKE.md are commented target shapes in
  a design doc, not accepted Lean definitions).
- Verified BUILD-EVIDENCE.json corroborates the honest build note (queued
  `lean-probe` timeout entry present; docs-only commit, no Lean rebuild
  owed). No forged benchmark or axiom evidence: the report claims no build
  numbers.
- Found the defect (below) by byte-level check (`tail | od -c`): the file
  literally ends with `...[truncated 9113 chars]`.

## The defect (repair direction)

The deliverable `dokumente/x86/AUDIT-END-TO-END-TRUST.md` as committed is
truncated mid-sentence in section 3 (breaks off at "through a NAMED
`InvScope` (`ruhe|sich" followed by a tool-truncation marker as the final
file bytes). Consequences, all mechanical:

1. Promised content absent: MUSE-REPORT-415.md claims "9 sections +
   appendices A-C" including consumer-gap analysis of neighbouring modules,
   vacuity-risk audit, validator-input trust table, runtime/link/loader
   coverage, proof-vs-CUTS ledger, P0-P3 list, and finding F3. None of
   sections 4-9, appendices, F3, or P0-P3 exist in the file.
2. Dangling references inside the delivered text: "(see §4)" at audit
   lines 133 and 205, "numbered closure gap in §7" (line 15), "the §8
   ledger" (line 79) — none of these sections exist in the file.
3. Report/file mismatch: the report describes findings (F3, P0-P3) that
   are not in the deliverable; a reader of the committed file cannot check
   them.

Repair direction (cheap, no re-audit needed): the author evidently holds
the full text (the report describes it precisely). Re-commit the complete
document verbatim minus the truncation artifact, confirm all forward
references resolve, and align the report's "9 sections + appendices A-C"
claim with the file. Sections 0-3 as delivered need no rework — every
checkable citation verified correct above. No safety weakening, no vacuity,
no forged evidence, and no scope violation was found; this is purely an
incomplete deliverable plus an overclaiming report.

## Exact names of new definitions/theorems

None (review lane; none tasked). No probe files created.

## Last `./lean-bau` result line

No `./lean-bau` run: review-only lane, no Lean/Rust file touched, and the
candidate itself is docs-only. No queued build was issued (the shared Lean
slot already timed out once for the author; verification by direct read of
`by decide`/`by simp`/`by rfl`-closed theorems in base-identical files is
sufficient for the citations checked, and the defect found needs no build).

## What remains open

- Re-review after the author re-commits the complete audit (changed
  candidate means a fresh substantive review per the lane task).
- The substantive end-to-end chain stays OPEN per the audit's own section
  0 (no SCFG/lowerOk/check_C/valX86/valX86_sound/schluss_x86, IR still
  working) — expected, not a candidate defect.
- Minor, non-blocking: the "`DIRECT-COMPILER.md` §§27-33" citation does
  not match that document's unnumbered section headers (verified in both
  base and HEAD versions); suggest citing the append-only ledger entry or
  design-doc section instead during repair.

## Anything in the task believed wrong

Nothing wrong. One note: the generic "actual reproduced Lean probes"
ask fits author lanes; for this docs-only candidate, citation-level
verification against base-identical sources plus the byte-level truncation
check was the exact probative work, and no queued probe could add to the
truncation finding.

CANDIDATE: 415 78d57179879cb076a20e5115e5bfd747ac9abf7f
VERDICT: REPAIR

Co-Authored-By: muse-agent-495 <muse-agent-495@noreply.invalid>
