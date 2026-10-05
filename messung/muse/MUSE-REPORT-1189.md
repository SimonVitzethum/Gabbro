# MUSE-REPORT-1189: Pipeline calls — real source execBlock correspondence

Lane 1189, branch `muse/1189`, clone `/home/simon/Dokumente/gabbro-muse/a1189`.
Follow-up of lane 1157 (`PipelineCalls.lean`): the callee body was an
abstracted result-word write there; this lane delivers the real
correspondence for a callee whose body is a lowered straight-line block.

## What was delivered

NEW FILE `grammatik/Grammatik/X86/PipelineCallsExec.lean` (+ one import
line in `grammatik/Grammatik.lean`). Reuses accepted definitions
unchanged; no existing file edited; optimiser files untouched.

- `rufExecOk` — joint validator: admitted caller frame (`rufOk`),
  single-assignment shape (`istEinzelZuweisung`), recomputed bytes
  (`validate` with `certs = []`), with unpacking `rufExecOk_teile`
  and `optimise_nil`.
- `calleeFremd` (decided) + `calleeFremd_mem`: every callee-saved
  register off `dst`/`adr`/`tmp :: frei`.
- Refusals: `rufExecOk_verweigert_rot/_form/_bytes`, with planted
  probes `cwProbe_mul` (body needing optimisation, `validate = false`
  by computation), `cwProbe_form`/`cwProbe_formRuf`
  (multi-statement source), `cwProbe_rot` (red zone).
- `einzelChunk_lauf`: lowered value code + address materialisation +
  store writes the representation word of the exact source value, keeps
  the environment, preserves every register off the working set.
- `einzelRuf_korrekt` (main): admitted frame + validated bytes of ONE
  source assignment imply the fetched byte run reaches the code end
  with the world of the REAL `execBlock` run represented, the
  environment represented, and all six callee-saved registers
  preserved. Proved by `senkBlock` inversion, the chunk run,
  `lauf_zu_laufBytes` and `worldRep_store`.
- `rufExecOk_rahmen`: caller-frame consequence via
  `pipeline_ruf_rahmen` (argument transport, result round trip,
  untouched callee-save slots).
- Joint witness `einzelRuf_korrekt_zeuge`: `T[0].f = x + 5` over the
  reused `pwD` declaration; source run turns row 0 from 7 to 35;
  validator accepts by computation; byte run preserves all
  callee-saved registers; frame saves turn the result byte
  (`rufWit_wechselt`) and reload the argument word. Non-degenerate:
  `pwV` writes its table; both source run and frame saves change memory.
- CUTS block + `#print axioms` for every definition/theorem.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineCallsExec.lean`:
  `== 0 error(s)`, axioms within `[propext, Classical.choice,
  Quot.sound]` throughout.
- `./lean-bau`: `Build completed successfully (618 jobs)` — whole
  project green. First attempt hit the known apparatus flake
  (`failed to create thread` at 616/618, resource exhaustion, no proof
  content); clean retry passed.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; English only.

## What remains open (see CUTS)

Single-assignment callee bodies only; multi-statement bodies, optimiser
certificates, TSO/GX bridge, push/pop emission, silicon beyond accepted
producers, run-time recursion enforcement — all refused or cited, none
claimed.

## Notes for the reviewer (things I believe are worth knowing)

1. `Pipeline.lean:1366` writes `variable {V : vertrag D}` (lowercase).
   In my scope lowercase `vertrag` is unknown (`Vertrag`, capital,
   `Syntax.lean:451`, is the real type). After adding
   `open Gabbro.Grammatik.X86.OptimizationRules` (matching
   Pipeline.lean's own opens), `#check @senkBlock_assign` prints
   `{V : Vertrag D}` and all lemma applications elaborate. I used
   capital `Vertrag` throughout; the mechanism behind the lowercase
   spelling deserves one glance at review (it behaves like an
   autoImplicit/alias quirk, harmless here since every application
   unified with the real contract).
2. `execBlock`/`execStmt` are `mutual`: the `.nil` outcome is not
   `rfl` in my context — `by simp [execBlock]` (equation lemma) was
   needed for `hnilOk`.
3. Witness config uses `adr := .r11` (caller-saved) instead of lane
   1157's `rbx`: `rbx` is callee-saved, so `calleeFremd` would be false
   with it. Documented in `cw_fremd`.
