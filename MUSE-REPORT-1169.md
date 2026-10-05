# MUSE-REPORT-1169: Pipeline correctness over the multi-core TSO machine

## Task
NEW FILE `grammatik/Grammatik/X86/PipelineTso.lean` (+ import line in
`grammatik/Grammatik.lean`). Single-core pipeline run embedded into
`HwMaschine` on core `c` with `FremdFrei`, TSO buffering transparent by
forwarding, memory outcome after drain equals the source's. Shared
atomics out of scope (refused). No edits to existing files except the
import; `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched.

## What was done
New module `Gabbro.Grammatik.X86.PipelineTso`, reusing accepted
definitions unchanged (`HardwareExecution`, `WordAccessGrouping`,
`FenceDrain`, `Speicher`/`TSO` equations). No new IR, no second
interpreter, no weakened guarantee; unsupported shapes refused.

Definitions:
- `pipeHw (s : Zustand) (c : Nat) (hw : HwProfil) (ber : Nat → BereitProfil)`:
  shared memory `s.speicher`, core data of `s` on `c`, default data
  elsewhere, empty buffers on all cores.

Theorems:
- `pipeHw_puffer_leer`, `pipeHw_fremdFrei` (empty buffers foreign-free),
  `pipeHw_proj` (acting core projects back to the pipeline state),
  `pipeHw_reg_einbettung` (successful pilot `schritt` with unchanged
  memory is a machine `HwSchritt.reg` step via accepted
  `hwPilot_weiter` + the memory-unchanged gate),
- `pipeTso_issue_forward` (own-load forwarding, from
  `load_nach_issue`), `pipeTso_issue_still`,
  `pipeTso_hw_issue_still` (issues memory-silent),
  `pipeTso_wort_puffer`, `pipeTso_wort_still` (word issue = eight
  canonical entries, memory-silent),
- `pipeTso_gruppe_liest` (grouped read-back from
  `wort_gruppe_liest_zurueck`), `pipeTso_drain_bytes`,
  `pipeTso_write64_bytes`, `pipeTso_write64_trifft_drain` (SC
  `write64` and exclusion-checked grouped drain read back the same
  word and agree on every footprint byte — the post-drain outcome
  other cores observe),
- refusals `pipeTso_refuses_lock`, `pipeTso_refuses_atomic_step`
  (LOCK/shared atomics), `pipeTso_refuses_tear`,
  `pipeTso_refuses_foreign`, with poison probes `pipeTso_probe_lock`
  (`rfl`), `pipeTso_probe_tear` (`decide`), `pipeTso_probe_overlap`,
- witness `pipeTso_zeuge`: joint two-core run, forwarding on the
  acting core, stale read on the other core, drain 0 → 42 in actual
  shared memory observed from both cores (memory-changing,
  non-degenerate).

Axioms: every `#print axioms` is `[]`, `[propext]`, or
`[propext, Quot.sound]` — within the standard set; no
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Verification
- `./lean-probe grammatik/Grammatik/X86/PipelineTso.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (608 jobs).`

## Open / not claimed
- No full `pipeline_correct` lift onto `HwMaschine` (validator,
  optimiser certificates, layout separation, loaded-image connection
  reused, not re-proved under TSO). Store instructions must take the
  issue/drain path; `pipeHw_reg_einbettung` excludes them by its
  `hmem` premise.
- No whole-word atomicity beyond grouped drains, no LOCK RMW, no
  shared-atomic contracts, no per-access W/GX simulation, no
  fairness/progress/timing/budget transfer, no interrupt/device model,
  pilot ISA only, no silicon correspondence beyond accepted canonical
  definitions. See CUTS in the file.

## Task remarks
Nothing in the task appears wrong. One scoping note: the task asks for
"the memory outcome observed by the other cores after drain equals the
source's" — delivered as word + per-byte agreement between SC
`write64` and the grouped drain (no shared-memory premise needed since
both sides equal `wortByte`), rather than a whole-`Speicher` equality,
which would be false in general (frame bytes outside the footprint).
