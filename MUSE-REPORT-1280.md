# MUSE-REPORT-1280: Exact re-review of repaired candidate 1279 (BSF/BSR/POPCNT/BSWAP)

CANDIDATE: 1279 b7ffb7c97ad3dd945e8d6b5b8448f0f7fa4da441
VERDICT: REPAIR

The repair keeps the executed machine Intel-exact but adds a
spec-level admissibility relation whose stated justification
contradicts the supplied reference, cites a rule that does not
exist, and leaves the author report describing two different
candidates at once. Minimal repairs R1-R4 below are concrete and
small; the previous ACCEPT (commit cf407e52) is superseded and
stale, not carried over.

Clone `/home/simon/Dokumente/gabbro-muse/a1280`, branch `muse/1280`
(`.git/HEAD` reads `ref: refs/heads/muse/1280`; verified first, no mismatch).
Owned file: only this report. No Lean or Rust code added or changed by
this lane.

## Review basis

New pinned `.tmp/review/SNAPSHOT.json` (author 1279, head
`b7ffb7c97ad3dd945e8d6b5b8448f0f7fa4da441`, base
`738366545afbddf7ac664db92804703db24f8868`, same three files, clean
true). The author clone was not touched (HARD RULES 1). Read in full:
the new 1845-line `IntBitScan.lean`, the complete new `PATCH.diff`,
the new `MUSE-REPORT-1279.md` (157 lines, incl. the repair section),
the new `BUILD-EVIDENCE.json` (247 lines, incl. the repair's red and
green runs), the unchanged `OWNER-TASK.md`, the cited SDM extract
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`),
`REFERENCES.json`, and this clone's `AGENTS.md`. Every finding from
the previous review was re-inspected against the new files.

## What still holds (re-verified, unchanged)

- Scope: same three files; `grammatik/Grammatik.lean` gains exactly
  the one import line (`PATCH.diff` line 172). No other existing file
  touched.
- No forbidden tactics or declarations in the new file (full-text
  search: only English "admitted"/"admits" in comments; no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `sorryAx`,
  `split_ifs`, `norm_num`, `ring_nf`, `intro _`, `have _ :=`).
- Axioms: author evidence records `./lean-probe` 0 errors with all
  28 `#print axioms` outputs inside `propext`/`Classical.choice`/
  `Quot.sound`, and final `./lean-bau` exit 0, 659 jobs, with only
  read-only git commands before commit `b7ffb7c9`.
- Accepted evaluator still lifted, never copied, including the new
  reuse `regSet_fremd` (exists at `Ausfuehrung.lean:144`). All
  premises of the eight new theorems are used; no `Prop`-typed
  premise; the executed step (`bsSchritt`), the adapter and the
  machine outcome are byte-identical to the reviewed version.
- Planted refusals still refuse (16 kernel-checked `bs_nichts_*`
  decode equations plus dispatcher, feature, length and memory
  refusals). The joint witness `bsHw_zeuge` is still non-degenerate:
  two cores (scan core 0 index 4, count core 1 value 8), in-place
  swap, owner-only forwarding of byte 42, a drain changing actual
  shared memory 0 to 42, zero-source ZF, and refusals beside it.
- Unchanged silicon parts still match the extract (opcodes, ModRM:reg
  destination, REX.W/R, POPCNT all-cleared/ZF plus CPUID bit 23 and
  LOCK #UD, BSWAP O-encoding/flags-none/16-bit-refused/LOCK #UD,
  F3-on-scan deferred with the profile rule).

## New findings (the repair under review)

F1. False silicon statement in the candidate file.
`IntBitScan.lean:824-825` justifies the free modeling with
"(Intel documents the destination and the other flags as undefined
or model-specific; AMD keeps the destination)". Against the
supplied SDM-093 extract this is wrong twice: the destination on a
zero source is UNMODIFIED (extract ll. 42739, 42822), and the flags
are DEFINED (ZF/PF set by rule, CF/OF/SF/AF cleared; ll.
42755-42758, 42838-42840); the older-processor footnotes say
"unmodified", never "undefined". The AMD half has no supplied
provenance at all: `REFERENCES.json` records "AMD URLs returned
404; no AMD reference snapshot is available" and scopes the
register to "Intel-profile architectural evidence; do not claim
vendor differences". A green proof (`bsScan_null_frei`,
`bsScan_flags_frei`) of non-determinism the supplied manual
forbids, justified by a reference that does not exist, is exactly
the failure mode HARD RULES 16 names.

F2. Fabricated authority. CUTS (`IntBitScan.lean:1768-1776`)
grounds the repair in "the standing vendor neutrality rule
(AGENTS.md, repair of 2026-10-05)". This clone's `AGENTS.md`
contains no vendor-neutrality rule (its only AMD line, :828,
states that AMD retrieval failed and no AMD provenance is
claimed). "Repair of 2026-10-05" is the author's own repair
cited as its own authority. The lane task's MECHANISM still
requires checking "against the Intel SDM extracts supplied to
the clone", and the unchanged `OWNER-TASK.md` still says to
model "free/unchanged exactly as the manual states" -- the
manual states UNMODIFIED, so "unchanged" was the compliant
reading, now abandoned without new evidence.

F3. The author report describes two different candidates.
`MUSE-REPORT-1279.md` "Task-text corrections" items 1
("destination operand is UNMODIFIED -- modeled as kept (whole
register...)") and 3 ("BSF/BSR PF is DEFINED...") are presented
as current, while the "Repair" section items 1 (destination
FREE, kept-theorems `bs_bsf/bsr_null_laesst_liegen` deleted) and
2 (only ZF defined) state the opposite. Both cannot describe
head `b7ffb7c9`. A reader cannot tell what was proved; the
report misdescribes the candidate it ships with.

F4. Counts still wrong (minor, but the repair claimed
exactness): 28 `#print axioms` lines
(`IntBitScan.lean:1816-1843`), not "22" plus "8 new" (it is 21
old plus 7 new, and `bsScan_rahmen_allgemein` has no `#print`
line); 16 `bs_nichts_*` decode refusals, not 17; `popNull`
remains prose-only (header, CUTS, open list) with no code use.

Direction note, to be fair to the author: the executed
semantics did NOT move -- `bsSchritt`, the adapter and the
machine still execute the Intel-exact reference (still pinned by
`bsScanNach_zulaessig` and the first conjunct of
`bsScan_null_unveraendert_zulaessig`). The defect is the
spec-level relation plus its false justification and the
contradictory report, not the machine. That is why the verdict
is REPAIR with small fixes rather than rejection of the work.

## Requested minimal repairs

- R1: correct `IntBitScan.lean:824-825` to state the Intel-defined
  facts (dest unmodified on zero; full defined flag row, with
  extract lines), mark FREE as a portability abstraction that goes
  beyond the supplied evidence, and drop the AMD factual claim
  unless its reference is supplied with line provenance (currently
  barred by the REFERENCES.json scope).
- R2: remove or correct the AGENTS.md standing-rule citation in
  CUTS; cite a real rule or none.
- R3: reconcile `MUSE-REPORT-1279.md`: mark the superseded
  corrections historical or rewrite them to describe head
  `b7ffb7c9` (FREE destination, ZF-only definedness), so the
  report describes one candidate.
- R4: fix the numbers (28 prints incl. 7 new, add the missing
  `#print axioms bsScan_rahmen_allgemein`, 16 refusals) or drop
  the exact counts; use or unname `popNull`.

## Reviewer build

`./lean-bau` re-run in this review clone (report-only lane, no Lean
code touched): `Build completed successfully (676 jobs).` Green.
The candidate file is not part of this tree (snapshot only), so
this confirms the lane adds no breakage; candidate build status
rests on the author's recorded green build (probe 0 errors, bau
exit 0, 659 jobs) on the committed tree, and the merge gate
rebuilds `grammatik/` mechanically before committing.
