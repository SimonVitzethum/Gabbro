# MUSE-REPORT-292: Independent source and invariant trust-boundary review

Lane 292, model opencode-go/muse-spark-1.3-contributor. Isolation gate passed
before any work: pwd `/home/simon/Dokumente/gabbro-muse/a292`, toplevel
`/home/simon/Dokumente/gabbro-muse/a292`, branch `muse/292`.

## What was done

Independent review of the actual Lean source parser/elaborator/unit
computations, `Bruecke`/`Pflichten` duties and Zielsatz source invariants
against `dokumente/x86/QUELLBRUECKE.md` and `dokumente/x86/IR-VALIDIERUNG.md`,
per the lane task. Read the defining Lean files (full bridge files
`Quelle`/`Pflichten`/`Pruefung`/`Simulation`/`Start`/`Atomar`/
`Nachbedingung`/`Realisierung`, front-end `Schlusssatz`/`Uebersetze`/
`UebersetzeAllg`/`UebersetzeAllg2` excerpts, `Zielsatz/Spec.lean` unit and
NOT CLAIMED sections, plus `SperreSem`/`ZielOrtRahmenBeweis`/`ZielOrtInv`/
`KorrespondenzAllg`/`Budget` anchors). Verified by grep that none of the
phase-B schema names (`DutyExport`, `EffectExport`, `AtomicExport`,
`FpExport`, `CostExport`, `LowerMap`, `valX86`, `schluss_x86`,
`X86Verfeinerung`, `SCFG`, `check_C`, `layoutOk`, `lowerOk`) is defined in
any `.lean` file under `grammatik/` or `bruecke/`.

Deliverable written (only owned file besides this report):

* `dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md` — §§0-11 plus CUTS:
  file-anchored audit of QUELLBRUECKE §1 (three precisions: implicit
  `gestartet := []` default, unlisted `declOf` all-false/all-empty rows,
  `startsAllg` filtering), exact per-site source evidence (entry ranges
  only, whole-function writes, vacuous invariants), full defaulted-field
  table, refusal-vs-erasure analysis (`getD False`/`hyps False` safe;
  `preExpr` lock-to-`true`, dropped non-`int` params, absent answer clause
  must never be read back), writer/held-section unavailability with
  `Spec.lean` NOT CLAIMED anchors and a concrete unsound hoist shape,
  program-name exclusion list confirmation, proved-vs-schema separation
  with absence evidence, all-six-SCFG-exports-absent table with existing
  substitutes, per-optimisation-family verdicts, eight counterexample
  shapes (C1-C8), claim ledger with no source-to-IR or binary closure.

## Exact names of new definitions/theorems

None. Docs-only lane: no Lean definition, theorem, or witness added; no
existing theorem changed, weakened, or renamed. No diagnostic, gift,
example, CLI, or MARKE number taken.

## Last `./lean-bau` result line

No Lean build was run. The task orders "no gratuitous builds" and "claim
checks only for docs"; this lane added no Lean code, so no build was owed.
Baseline untouched: `git status --short` shows only the two owned untracked
files (`dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md`, this report). No
`grammatik/` modification to revert.

## What remains open

* All phase-B constructions audited as absent (§§7-8 of the review):
  SCFG syntax/semantics/checkers/rule register, six source-computed
  exports, lowering checker, per-access TSO table and spill/vector
  correspondences, decoder, validator + `valX86_sound`, ghost call/return
  events, ghost budget correspondence, lane-278 timing bounds.
* Anchor drift: every file:line citation is valid at this commit only;
  front-end or bridge edits invalidate individual anchors.
* The review flags but does not fix one documentation gap: QUELLBRUECKE
  §1.2's defaults list is correct yet `einheitAllg` itself leaves
  `gestartet` implicit — suggest the coordinator cite the structure default
  explicitly when reusing that paragraph.

## Anything believed wrong in the task or sources

Nothing found wrong in the task. In the sources, no unsound theorem was
found; the risks identified are all on the consumer side (reading
erasures as facts, assuming interior range/ownership/invariant evidence
the bridge does not compute, binding `P` instead of the full unit,
assuming the refinement). QUELLBRUECKE §4's review-repair (derived, not
assumed, refinement; full-unit identity) already blocks the two most
severe shapes (C1, C2); this review endorses both without reservation.
IR-VALIDIERUNG §§3/7 correctly mark every load-motion, invariant-motion,
SIMD, and budget-transfer admission as refused-until-proved; the review
adds only that on the currently bridged fragment the refusal is total
(`S = leer`, no interior facts), not conditional on a failed check.
