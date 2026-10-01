# Muse report 316: independent review of candidate 312 (re-review after repair)

## Scope and snapshot (RE-REVIEW, new pin)

Reviewed ONLY the NEW pinned snapshot `.tmp/review/author-312/` (no
other clone, no code edits, no central-file changes). The previous
verdict (REPAIR on `946e107d`) is stale and superseded by this section.

- `SNAPSHOT.json`: author 312, HEAD
  `defda05ab2fdabb250ea7a9e5bcff109529e5bc0`, base
  `345627a46732923a03a5f792ff4050b7e3b7c837`, clean, files
  `MUSE-REPORT-312.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/Regionen.lean` (now 631 lines, +41 vs the
  first snapshot: exactly the two required repairs, nothing else).
- `PATCH.diff` is a full-file diff containing the repaired theorems;
  `BUILD-EVIDENCE.json` appends the repair-pass trail (one red
  intermediate probe at line 323, fixed; final probe 0 errors plus
  `./lean-bau` 372 jobs success with `region_schreibLese_zeuge` at the
  new line 629).
  `MUSE-REPORT-312.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/Regionen.lean`.
- `PATCH.diff` confirms exactly that file set: one new Lean file
  (590 lines) plus one umbrella import line in `grammatik/Grammatik.lean`.
- `BUILD-EVIDENCE.json`: development trace with intermediate red probes,
  ending green (`./lean-bau` 372 jobs success, final probe 0 errors,
  standard axioms). The intermediate failures are ordinary development
  iterations, not evidence against the final snapshot.

Isolation: `pwd`/`toplevel`/`branch` are
`/home/simon/Dokumente/gabbro-muse/a316` / `muse/316`. This tree has no
`grammatik/Grammatik/X86/Regionen.lean` of its own, so the probe below
ran against the snapshot copy only. No full `./lean-bau` was run (lane
task: no gratuitous full builds for prose).

## Method

1. Read the snapshot Lean file in full, the owner task, the author
   report, the patch, and the build evidence.
2. Ran the queued wrapper on the snapshot copy:
   `./lean-probe .tmp/review/author-312/grammatik/Grammatik/X86/Regionen.lean`
   Result: `== 0 error(s) in the COMPLETE output`. Every `#print axioms`
   line is standard: `regionEnde`/`vorratEnde`/three `decide` probes
   depend on no axioms at all; all other theorems depend on subsets of
   `propext, Classical.choice, Quot.sound`. Matches the report.
3. Grepped the snapshot for banned tokens (`sorry`, `admit`,
   `native_decide`, `unsafe`, `axiom` declarations): no matches (only
   `#print axioms` lines). No `Prop`-typed premise, no `intro _` /
   `have _ :=`.
4. Checked every report-claimed definition/theorem name against the
   file: all 19 definitions and all 30 theorems present (script-verified,
   zero missing).
5. Verified no universal quantification over source syntax
   (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`): no matches
   outside comments, so no INHABITATION `_zeuge` companion is required;
   the report's statement of this is correct. Target-helper probes are
   present instead (`decide` facts plus the memory-changing
   `region_schreibLese_zeuge`).
6. Cross-checked the canonical vocabulary in this tree
   (`Typen.lean`: `Speicher` has exactly the four fields
   `bytes/lesbar/schreibbar/ausfuehrbar`; `Speicher.lean`: `addrOff`,
   `lesbar8`, `schreibbar8`, `read64`, `write64`, `writeBytes`,
   `writeBytesN`, `writeBytesN_hit`, `addrOff_null`,
   `read64_nach_write64`). The candidate uses every name with a matching
   signature; the `read64_nach_write64` application passes the
   pre-store readability proof as required. No second word/memory model.
7. Hand-verified the witness arithmetic: `ausricht 65536 8 = 65536`,
   `65536 + 8 = 65544 <= 65536 + 4096 = 69632`; refusal probe
   `65536 + 8192 = 73728 > 69632` gives `none`; the joint witness has
   `len = 8`, both permission bridges applicable, pre-store byte 0 and
   post-store byte `wortByte 42 0 = 42`. All consistent with the green
   `decide` proofs.
8. Robustness note: the snapshot file probes 0-error even against this
   tree's newer base (`cf1f9b4f` vs author base `345627a4`), so it is not
   brittle to the drift since the author branched.

## Verified true (bounded claim holds mathematically)

- Region/Vorrat handles, `innerhalb` (range plus `<= 2 ^ 64`),
  `regionDisjunkt`, `ausricht` with zero-refusal: as defined.
- `reserviere` refuses `len = 0` and `ausr = 0`, aligns the cursor,
  refuses over-ceiling/wrap, else hands a fresh capability
  deterministically: proved by `reserviere_leer_verweigert`,
  `reserviere_ausr_null_verweigert`, `reserviere_ausmass`,
  `reserviere_innerhalb`, `reserviere_decke`, `reserviere_frisch`,
  `reserviere_voll_verweigert`. All proofs check.
- `initialisiere` frame/extent facts plus the `schreibbar8`/`lesbar8`
  bridges through the shared canonical checks: all prove.
- Ceiling-free model still fails (`freiReserviere_kann_scheitern`,
  `freiReserviere_leer_verweigert`) and provably exceeds every
  `B < 2 ^ 64` (`freiReserviere_ohne_statik_gebunden`) while each extent
  keeps `basis + len <= 2 ^ 64`: no physical unbounded-address claim.
- No number-to-pointer region creation: regions come only from
  `reserviere`/`freiReserviere`; `natAdresse` names addresses for
  lemmas/probes under checked containment.
- Claim boundaries honest: source correspondence, Spec/goal coverage,
  runtime/OS contracts (beyond the `scheitert` answer point),
  TSO/concurrency, loader/image, decoder/ABI/cost are all labelled OPEN
  in CUTS and claimed nowhere. No hardware/source theorem is drawn from
  the green build. No name/example-specific rule; all theorems quantify
  generically.
- Fresh regions are capabilities, runtime/OS allocation is user logic,
  no new word/memory model: as required by the owner task.

## Re-review of previous findings (new snapshot)

F1 (unused `_hq`, old line 284) — RESOLVED as the preferred variant:
`reserviere_disjunkt_unten` (new lines 281-299) now takes
`(hinv : alleUnten s) (q : Region) (hq : q ∈ s.belegt)` and derives
`have hunter := hinv q hq` (line 288), which the closing `omega`
uses. Every premise is used (`h` via `reserviere_frisch` /
`reserviere_ausmass`, `hinv`+`hq` via `hunter`). No underscore-silenced
binder remains anywhere in the file (grep for `_hq`/`intro _`/`have _`
empty). The statement is now about tracked regions, otherwise
unchanged — no weakening.

F2 (old-entries-only preservation) — RESOLVED by addition, not
rewording: new helper `reserviere_belegt` (lines 313-331,
`s'.belegt = r :: s.belegt`, premise `h` used throughout the case
split) and new corollary `reserviere_haelt_alleUnten` (lines 335-350,
conclusion `alleUnten s'`). The proof is the natural case split (new
region ends exactly at the new cursor via `reserviere_frisch`, old
entries via `reserviere_haelt_unten`); all premises used
(`h` via `hfr`/`halt`/`hbel`, `hinv` via `halt`). The report's
"cursor invariant preservation" claim now matches a proved theorem
exactly, and the report's name list was updated with both new
theorems (script-verified present, with `#print axioms` lines).

Fresh independent checks on the NEW snapshot: `./lean-probe` gives
`== 0 error(s)`; both new theorems depend only on
`[propext, Quot.sound]`; banned-token grep empty; source-syntax grep
(`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`) empty, so still no `_zeuge`
companion needed; claim boundaries/CUTS unchanged. No new defects
found; the earlier non-blocking observations stand as notes.

## Required findings (REPAIR — FIRST snapshot, now superseded)

F1: Unused premise contradicts a hard gate and the report.
File `grammatik/Grammatik/X86/Regionen.lean` line 284, theorem
`reserviere_disjunkt_unten` (lines 281-299): the premise
`(_hq : q \in s.belegt)` is never referenced in the proof body (lines
286-299 use only `reserviere_frisch`, `reserviere_ausmass` and `hunter`).
This violates HARD RULE 3 (every premise must be used; the underscore
prefix silences the linter instead of fixing it) and falsifies the
report's claim "every premise is used". The theorem itself is true (it
holds for ANY `q` below the cursor), so this is hygiene, not
unsoundness — but the gate is explicit.
Required fix, preferred variant (makes the statement about tracked
regions and uses every premise): replace lines 284-285
`(q : Region) (_hq : q \in s.belegt) (hunter : q.basis + q.len <= s.naechst)`
with `(hinv : alleUnten s) (q : Region) (hq : q \in s.belegt)`, and
derive `hunter := hinv q hq` at the start of the proof. Minimal
alternative: delete the `_hq` line entirely (the proof stays green
unchanged since it never mentions `_hq`).

F2: `reserviere_haelt_unten` (lines 302-311) proves the old-entry half
only (`forall q \in s.belegt, q.end <= s'.naechst`), while the report
sells it as "cursor invariant preservation (`reserviere_haelt_unten`,
`alleUnten`)". Full `alleUnten s'` additionally needs the new region's
case (`r.end = s'.naechst`, available from `reserviere_frisch`).
Required fix: either add the corollary `alleUnten s'` (one short proof
combining `reserviere_haelt_unten` with `reserviere_frisch`), or reword
the theorem doc-comment and the report to "old entries stay below the
new cursor" so the claim matches exactly what is proved.

## Non-blocking observations (no action required for this verdict)

- `regionEnde`, `vorratEnde`, `ausgerichtet` have no theorems; no
  theorem connects `reserviere` success to `ausgerichtet r ausr`. Dead
  but harmless helpers; alignment postcondition was not in the
  mandatory property list.
- Report phrase "refuses ... unaligned requests": only `ausr = 0`
  refuses; nonzero alignments are rounded up, never refused. Loose
  wording, not a false theorem.
- A `Vorrat` with `lo + umfang > 2 ^ 64` is degenerate but still sound:
  the `start + len <= 2 ^ 64` conjunct independently caps every success.
- BUILD-EVIDENCE intermediate red probes are development history; the
  pinned final state is what was reviewed and is green.

## Build/witness gates summary

- `./lean-probe` on snapshot copy (this review): 0 errors; axioms
  standard; no banned tokens. BUILD-EVIDENCE final `./lean-bau`:
  `Build completed successfully (372 jobs)` — consistent, not re-run
  here per lane instructions.
- Witnesses: `zeugenReserviere_erfolg`, `zeugenReserviere_voll`,
  `zeugenSchreibschutz_verweigert` (`decide`), plus nonzero
  memory-changing `region_schreibLese_zeuge` (`write64` 42, `read64`
  round-trip, byte 0 -> 42). Real and sufficient for target helpers.
- No Lean file written by this review; no central file touched; only
  this report is owned and committed.

CANDIDATE: 312 defda05ab2fdabb250ea7a9e5bcff109529e5bc0
VERDICT: ACCEPT

Note: the ACCEPT above refers to the NEW pin `defda05a`. The stale
first snapshot `946e107d` remains VERDICT: REPAIR (findings F1/F2 as
documented); it must not be approved or merged.
