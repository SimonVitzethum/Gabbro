# MUSE-REPORT-732: Organise exact essential hardware integration and executable coverage

Clone: `/home/simon/Dokumente/gabbro-muse/a732`, branch `muse/732` (verified before work).
Owned files only: `dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md` (new),
`MUSE-REPORT-732.md` (this report). No other file touched.

## What was done

Wrote the owned organisation document
`dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md` (7 sections). It builds a
concrete constructor/form/observable matrix over the accepted tree with the
tasked columns (real codec, manual provenance, canonical evaluator, common
fetched dispatcher, TSO/per-access effects, control/fault/flags, joint
reached witnesses, tests/review evidence), grounded in files actually read in
this clone:

- Design: `DIRECT-COMPILER-DESIGN.md` §§2A/2D/3–6 (809 lines, read in full).
- Scope record: `dokumente/x86/HARDWARE-MODEL-COMPLETION.md` (lane 678, read
  in full); this document references it and does not duplicate it — it adds
  the integration mechanics (where each row's bytes execute, producer versus
  consumer closure, dependency sequence).
- Accepted modules (headers, imports, entry theorems, CUTS read):
  `HardwareExecution` (660), `LockedInstructionExecution` (662),
  `AddressEncoding` (664), `IntegerHardwareForms` (666),
  `ScalarFloatHardwareForms` (668), `HardwareFaults` (670),
  `VectorHardwareProfile`/`VectorIntegerHardwareForms` (674/686),
  `DeviceHardwareForms` (676), `IndirectControlHardwareForms` (680),
  `FpControlHardwareForms` (682), `CpuFeatureHardwareForms` (688),
  `ArchitecturalFlags` (692), `MemoryTypeHardwareExecution` (694),
  `MulDivWidthHardwareForms` (700), `ScalarFloat32HardwareForms` (702),
  plus `ExtendedExecution` dispatcher.
- Registry: `DIRECT-COMPILER.md` progress table (lanes 660–739 states);
  committed task prompts `lanes/718.md`, `720.md`, `722.md`, `724.md`,
  `726.md`, `728.md`, `730.md`, `734.md`, `736.md`, `738.md` (read in full);
  merged reports 660–702 (headers and owned-module claims).
- Measured source baseline hash recorded in the document: `9fc15bf4`.

## Key findings (all with exact file/theorem locations in the document)

1. `HwSchritt.reg` (`HardwareExecution.lean:173-176`) steps only through the
   old `stepExt` vocabulary; every newer producer family reaches the common
   `HwMaschine` solely via the scheduled consumers 718–724. Producer ACCEPTs
   cover exact delivered claims only.
2. Each accepted producer owns a parallel fetched-step loop over its own
   machine (`extByteschritt`/`hwByteschrittReg`, `intHwByteschritt`,
   `lockByteschritt`, `mmioByteschritt`); lane 718 owns unification with an
   explicit "no second competing executor" duty.
3. No contradictory accepted evaluator semantics: producers reuse canonical
   helpers (`Ganzzahl`/`ShiftLogic`/`logikFlags`, binary32 kernel,
   `stepExt`). One proved intentional divergence is pinned:
   `vecShlQ_satt_vs_maske` (saturate, not mask).
4. Named abstractions that must never be cited as completion: AF=none,
   `cas_fehlschlag_stottert`, eight-byte `hwWortAusgabe` grouping,
   `osXmm : Bool`, codec round trips.
5. Coverage gap: binary32 (702) and packed-integer (686) producers have NO
   scheduled consumer (724 defers both); proposed as disjoint follow-ups
   F-B32/F-VEC alongside F-AF/F-DEV/F-RET/F-AVX/F-6B with dependency gates.
6. `.tmp/HARDWARE-REFERENCES/` is absent in this clone by `.gitignore`
   design (clone-local); provenance lives in producer reports/module CUTS.

## New definitions/theorems

None. Organisation lane; no Lean work, no code changes.

## Last `./lean-bau` result line

Not run: no Lean file was created or modified (`git status` shows only the
two owned Markdown files), so the tree build state is unchanged from the
measured baseline `9fc15bf4`. A docs-only commit cannot turn the build red;
the serial integration gate rebuilds before any merge.

## What remains open

- Reviewer 733 reviews this exact candidate (ACCEPT or REPAIR).
- All §5 follow-ups (F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX/F-6B) are proposals
  with dependency gates, not claims; scheduling belongs to the coordinator.
- In-flight states (672/696/698/690/708/704) were taken from the registry
  and prompts, not inspected — producer clones were never accessed.
- Nothing here claims model completion or any source-to-final-bytes closure.

## What I believe is wrong in the task or surroundings

Nothing in the task itself. One registry observation: `DIRECT-COMPILER.md`
lists lane 733 (this lane's reviewer) as "scheduled" with only a task file;
that is correct procedure, not an error. No decorative counts or percentages
are presented as effort coverage anywhere in the deliverable, per the task.
