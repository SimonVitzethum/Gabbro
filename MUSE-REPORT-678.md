# MUSE-REPORT-678: Organise and audit complete essential hardware-model coverage

## What was done

- Verified clone `/home/simon/Dokumente/gabbro-muse/a678`, branch `muse/678` (match; proceeded).
- Wrote the owned deliverable `dokumente/x86/HARDWARE-MODEL-COMPLETION.md` (single actionable
  completion matrix) and this report. No other files touched; no Lean/Rust changes.
- Read as evidence: `DIRECT-COMPILER-DESIGN.md` §§0–12 (essential/deferred scope, §2 pilot table,
  §2B compact encodings, §2D admission test/stop rule, §§3–6 planned rows/tiers, §§7–11 gates),
  `dokumente/x86/EMITTER-INVENTAR.md` §§0–13 (emitter-driven scope, refused paths, §12 gaps incl.
  the two OS-knowledge gaps), all nine hardware task prompts `lanes/660.md`–`lanes/676.md`
  (even numbers), `ExtendedExecution.lean` interface + CUTS (828 lines: `ExtInstr`, `decodeExt`,
  `stepExt`, `fetchExt`, `extByteschritt`, joint witness, refusal pins), per-module declaration
  counts + CUTS first-lines for ~40 X86 modules, and targeted omission greps (AF, failed-CAS,
  noncanonical, FP sticky/payload, XCR0/OSXSAVE, device ordering).
- Verified every link cited in the matrix resolves in this clone (link check: no missing files).

## Exact names of new definitions/theorems

None. Docs-only organisation lane: no Lean definitions or theorems were added, none were
modified, and `grammatik/Grammatik.lean` is untouched. The matrix references existing
proved names only (e.g. `decodeExt`, `stepExt`, `fetchExt`, `extByteschritt`,
`cas_fehlschlag_stottert`, `guard_sticky_offen`, `kanonischBereich`, `realisiert_fuss_abdeckung`).

## Last `./lean-bau` result line

No Lean build was run, by task design: the lane owns only two Markdown files and changes no
Lean/Rust input, so there is nothing to build and no fictitious build is reported
(task: "docs-only diff/link checks, no fictitious Lean build"). `git status` shows only the
two owned files as new; the tree builds exactly as before this lane.

## Matrix summary (classifications, no percentages or ETAs)

- Pilot 14 forms: partial (proved) — vocabulary, abstract steps, codec round trip, fetched
  execution proved; silicon correspondence, TSO bridge, full chain OPEN.
- Address encodings (664): unimplemented. Per-access canonical-form rule not found
  (`OhneUmbruch` + extents + permissions only); canonical rule exists at image level only
  (`Bild.lean:43`, profiles 48/57).
- Integer widths (666): partial (proved helpers, dispatcher-connected). Defined-AF rows OPEN
  (`af : Option Bool` is an abstraction, not a defined result).
- LOCK/fences (662): partial with proved obstruction — `casSchritt` failure is a proved
  stutter (`cas_fehlschlag_stottert`), which blocks citing `LockedOps` as full LOCK
  correspondence; failed-path access rules, flag/register/RIP effects OPEN.
- Scalar FP (668): partial (proved). NaN class-level only (`ScalarFloat.lean:1013,1459-1462`),
  sticky MXCSR unmodelled (`:1467`, `FloatExceptions.lean:182-186`), f32 bridge refused/OPEN.
- Faults (670): partial catalogue over admitted rows; priority/privilege/per-access
  canonical faults OPEN. Interrupts/entries (672): admission proved; async transition rules
  unimplemented.
- SIMD/enabled-state (674): partial with proved obstruction — two packed-integer register
  rows proved; no CPUID/XCR0/XGETBV model exists (only `osXmm : Bool`, `FeatureProfile.lean:42-63`);
  AVX2/VEX/context rows unimplemented.
- Ports/devices (676): unimplemented in Lean (C emitter rows exist); MMIO/DMA stay refused.
- TSO bridge: partial (byte machine + fragments); typed-carrier per-access simulation OPEN.
- Image/ABI/entry/budget: partial components; loaded-mapping/relocation-re-decode/duties/
  `valX86_sound`/closing theorem OPEN.
- The matrix also records coherence/composition duties (660 umbrella, stable producer APIs,
  no competing IR, rejection anti-patterns), the assumption-vs-contract ledger (incl. the two
  §12 item 7 gaps), essential-vs-deferred scope, a finite 8-point auditable DONE condition,
  and eight follow-up tasks F1–F8 with NEW paths, dependencies, sketches, negative witnesses
  and rejection criteria.

## What remains open

- All producer work itself (660/662/664/666/668/670/672/674/676 candidates, reviews,
  integration, publication checks). This lane organised the closure; it closed nothing.
- The matrix must be updated when producers land: move rows only on merged + independently
  reviewed evidence, never on candidate existence.

## What I believe is wrong or risky in the task/setup

- Nothing in the task statement is wrong. One observation: `DIRECT-COMPILER-DESIGN.md` is a
  root file, not under `dokumente/x86/` as the prompt's path shorthand suggests — found at
  repo root; content matches the cited sections. Connection-wave lanes 558–575 referenced in
  AGENTS.md §11 have no prompts in `lanes/` of this clone, so producer state beyond 660–676
  prompts is correctly recorded as not visible (no control-dir access per task rules).
