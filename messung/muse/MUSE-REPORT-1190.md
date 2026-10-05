# MUSE-REPORT-1190: Exact review of candidate 1189 (PipelineCallsExec)

Lane 1190, clone `/home/simon/Dokumente/gabbro-muse/a1190`, branch `muse/1190`.

CANDIDATE: 1189 6af837f8dd7bb3f157a3a9be846ec525e048f040

Report-only exact review of CANDIDATE 1189, pinned HEAD
`6af837f8dd7bb3f157a3a9be846ec525e048f040` (base `81efbbddc54cc9c074deb23ef6733290ea4145f8`),
via `.tmp/review/SNAPSHOT.json` + `author-1189/PATCH.diff` + `OWNER-TASK.md` +
`MUSE-REPORT-1189.md` + `BUILD-EVIDENCE.json`. No candidate files applied to this clone.

## Scope check

Files in snapshot: `MUSE-REPORT-1189.md`, `grammatik/Grammatik.lean` (one added
import line `import Grammatik.X86.PipelineCallsExec`, confirmed in PATCH.diff),
`grammatik/Grammatik/X86/PipelineCallsExec.lean` (new, 591 lines). Existing
files otherwise untouched; `OptimizationRules.lean`/`OptimizationWitnesses.lean`
not edited (only `open ...OptimizationRules` in the new file). Clean: true.

## Checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in code: `rg` over
  PATCH.diff finds only the English sentence "No `sorry`/..." in the report.
  No `intro _` / `have _ :=` / `Prop`-typed premise patterns.
- Axioms: BUILD-EVIDENCE `lean-probe` shows every definition/theorem within
  `[propext, Classical.choice, Quot.sound]`; main `einzelRuf_korrekt` and joint
  witness `einzelRuf_korrekt_zeuge` depend on exactly
  `[propext, Classical.choice, Quot.sound]`. File ends with CUTS + `#print axioms`
  for all 36 names.
- Every premise used: `einzelChunk_lauf` consumes `hc` (regs/frei/var), `hp`,
  `hwr`, `hE`, `hlo/hhi`; `einzelRuf_korrekt` consumes `hval` (via
  `rufExecOk_teile`), `hsep` (`worldRep_store`), `hfremd` (`calleeFremd_mem`),
  `hcode`/`hrip` (`lauf_zu_laufBytes`), `hW`/`hE`, `hsrc` (rewritten then
  cased); `rufExecOk_rahmen` forwards all premises to `pipeline_ruf_rahmen`.
  Refusals consume their hypotheses. No conclusion restates a premise; no
  `forall rho/v` contract quantification; real `execBlock`/`exec` worlds used.
- Evaluator lifted, not copied: no new machine/loader/interpreter. Reuses
  `rufOk`, `calleeGerettet`, `pipeline_ruf_rahmen`, `senkBlock`/`senkBlock_assign`,
  `senkWertT_korrekt`, `validate`/`validate_sound` (`certs = []` + `optimise_nil`),
  `lauf_zu_laufBytes`, `worldRep_store`, and witnesses `pwD/pwV/pwL/pwSrc/pwHw`,
  `rufWitBelegung/ok/wechselt/rundreise` (verified present in base tree).
- Refusals genuine: `cwProbe_mul` (`validate ... = false` by `decide`),
  `cwProbe_form` (`istEinzelZuweisung pwSrc = false` by `rfl`; `pwSrc` is two
  assignments in `PipelineWitnesses.lean:120`), `cwProbe_formRuf`/`cwProbe_rot`
  via the proved refusal theorems. Unsupported shapes refused, never guessed.
- Witness non-degenerate: `cwBody` is `T[0].f = x + 5`, one assignment;
  `cw_quelle` is `rfl`-proved with row 0 7 -> 35 and row 1 kept at 9
  (memory-changing source run); `pwHw : pwV.schreibt () = true`; frame saves
  change memory (`rufWit_wechselt`); byte run preserves all callee-saved
  registers. `cw_rufExec` accepts by `decide`. `adr := .r11` (caller-saved)
  documented for `calleeFremd`.
- Silicon: no new encodings/flags/faults/ordering. Uses canonical `kanon`,
  `encodeAll`, `gerade`, `movImm64/store64` producers; CUTS claims no silicon
  beyond accepted producers, no loader/entry/relocation/time, no TSO/GX, no
  push/pop emission (cited to `ComposeStackAbi`), single-assignment scope only.
  No hardware-correspondence or W/GX claim. Honest.
- Author notes (lowercase `vertrag`, `execBlock.nil` simp, `r11` vs `rbx`):
  checked harmless; new file uses capital `Vertrag` and elaborates.

## Builds

- Candidate evidence: `lean-probe ...PipelineCallsExec.lean` = `0 error(s)`;
  `lean-bau` = `Build completed successfully (618 jobs)` (one earlier apparatus
  flake `failed to create thread` retried clean).
- This reviewer clone (base without candidate): `./lean-bau` last line
  `Build completed successfully (619 jobs).` with first line
  `== exit 0; 0 error line(s) in the COMPLETE output`.

## Open (not defects)

Multi-statement callee bodies, optimiser certificates, TSO/GX bridge, push/pop
emission, silicon beyond accepted producers, run-time recursion enforcement.

VERDICT: ACCEPT

Candidate 1189 meets the exact-review bar: real `execBlock` correspondence for
the single-assignment callee with callee-saved preservation, recomputed bytes,
loud refusals, and a non-degenerate memory-changing joint witness, with
standard axioms and honest CUTS.
