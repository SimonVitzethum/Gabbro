# MUSE-REPORT-323: detailed generic direct compiler design, with fast compilation

## Latest steering extension (2026-10-01, second commit)

Added §2A "Selective hardware model and why 14 forms are not maximal
performance" (~42 lines): hardware model covers EXACTLY the emitted forms
(registers/flags, permissions/alignment, decode/fetch, faults,
TSO/interrupt/FP interactions as selected); whole pipeline/cache/transistor
model out of scope for functional validation; time needs named conservative
assumptions + separate cost transfer; all reachable final code covered,
unmodelled forms refused; 14 stated plainly as proof pilot inadequate for
high performance (no mul/div/shifts/FP/atomics/SIMD, long encodings);
scalar profile then gated tiers; selected-forms model still nontrivial over
async events; proof boundaries, goal statement and guarantees unchanged;
no numerical count target, no maximal-performance claim.
New measured line count: 506 (was 462).

## What was done

Wrote the NEW root document `DIRECT-COMPILER-DESIGN.md` (462 lines), a
coherent detailed PROPOSED architecture covering all 11 requested sections:
objective/trust chain, exact 14-constructor pilot table, planned practical-
performance ISA table, SSE2 binary64 FP baseline, TSO concurrency bridge,
SIMD tiers, optimisation inventory with premises/failure cases/5 generic
examples, fast compilation architecture, fast validation, measurement
protocol, implementation sequence with open obligations.

## Factual source material checked

- `DIRECT-COMPILER.md` (ledger, sequence, lane states)
- `dokumente/x86/BYTE-PILOT.md`, `LEAN-ZUERST.md`, `EMITTER-INVENTAR.md`,
  `IR-VALIDIERUNG.md`, `TSO-GX-BRUECKE.md`, `QUELLBRUECKE.md`,
  `IMAGE-ABI.md`, `FLOAT-ZEIT.md`, `REVIEW-QUELLE-INVARIANTEN.md`,
  `REVIEW-TSO.md`, `REVIEW-OPT-BINAER.md`
- `grammatik/Grammatik/X86/Typen.lean` (14 `Befehl` constructors verified
  against the §2 table)
- `grammatik/Grammatik/Zielsatz/Spec.lean` header (via QUELLBRUECKE/TSO docs);
  GabbroV bridge via `nutzer_aus_quelle`/`nutzerA_aus_quelle` as cited in
  QUELLBRUECKE §1.4
- Actual emitter constructs from EMITTER-INVENTAR §§2–10 (never examples)

## Verification

- Markdown links: 23 relative links extracted by script, all resolve to
  existing repo paths; primary references are plain https URLs (Intel SDM,
  AMD APM vol.3, Intel optimisation manual, LLVM NewPassManager/ThinLTO).
- Pilot consistency: 14 constructors, mnemonics, widths/forms and
  length/encoding choices match Typen.lean constructors + BYTE-PILOT rows.
- Line count 462 (task range 450–850).
- No Lean file touched/added; no `Grammatik.lean` edit; no build owed by this
  docs-only task (skeleton commit + content commits through `./commit.sh`).
- Last `./lean-bau` result line: not run — documentation-only task, no Lean
  changes; baseline untouched (per task: no gratuitous full builds).

## What remains open

Everything substantive: all profile rows PROPOSED, all validators/bridges
unproved, no speed measured (stated in CUTS). Reviewer 324 checks the exact
committed candidate independently.

## Believed-wrong items in the task

None. The constraints (no mini-models, profiles PROPOSED, examples generic,
links to ledger not a second progress table) were followed; the design cites
rather than duplicates.

## Owned files

`DIRECT-COMPILER-DESIGN.md`, `MUSE-REPORT-323.md`. Nothing else touched.

## CUTS

No theorem proved; no decoder/validator/refinement/cost result; no runtime
or compiler speed measurement; no `cargo`/`lake` run by this lane.
