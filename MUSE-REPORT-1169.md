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

## Review response (2026-10-05, reviewer lane 1170)

Reviewer verdict: REPAIR, but on purely apparatus grounds — the
reviewer clone could not display the pinned diff (tool-gate denials),
so every checklist item stands at NOT CHECKED. No content finding
against any definition, theorem, proof step, axiom, refusal, probe,
witness, or CUTS sentence of this lane was raised.

Self-verification after the review (this clone, unchanged tree):
- Banned scan `rg "sorry|admit|native_decide|sorryAx|unsafe|^axiom "`
  over `PipelineTso.lean`: no hits.
- Diff scope `git diff --stat 062b979a..HEAD`: exactly the 3 owned
  files (new `PipelineTso.lean`, 1 import line in `Grammatik.lean`,
  this report). Reserved optimiser files untouched.
- `./lean-probe`: 0 errors; all `#print axioms` are `[]`,
  `[propext]`, or `[propext, Quot.sound]`; no linter warnings on this
  file (every premise used — the one unused premise found during
  development was removed, not worked around).
- `./lean-bau`: exit 0, 0 error lines, 608 jobs green (the one
  visible linter note belongs to pre-existing master file
  `G719_lock_taken_nowhere.lean`, not to this lane).

Nothing was weakened and no finding required a code change; the
deliverable stands as reviewed-pending-content. CUTS in
`PipelineTso.lean` unchanged and honest.

## Integration-gate response (2026-10-05, gate FAILED, nothing merged)

Gate evidence: `Grammatik.X86.PipelineTso` (and in the merge log the
same module) dies with `lean::exception: failed to create thread`,
exit 134 — a resource failure, with zero Lean errors. No proof
defect is evidenced.

Local reproduction (this clone, twice, unchanged tree): the module
itself compiles — all 21 `#print axioms` lines emit, `./lean-probe`
reports `0 error(s)` — then the final `Grammatik` aggregator step
(607/608) dies with `failed to create thread` once and
`std::bad_alloc` once. The aggregator loads all 600+ modules; my file
adds no new transitive dependency (`HardwareExecution`,
`WordAccessGrouping`, `FenceDrain` are pre-existing aggregator
imports), only 277 lines of elaboration. This matches the documented
apparatus failure (AGENTS.md §9/§11: virtual-address exhaustion kills
builds even on unchanged source under concurrent-lane memory
pressure). Conclusion: environmental OOM, not a deliverable defect;
no guarantee weakened, no proof changed.

Repair attempted within the module: replaced the single kernel
`decide` in `pipeTso_probe_tear` by a length-based proof
(`congrArg List.length` + `simp [List.length_take,
wortEintraege_laenge]`), which passed `./lean-probe` with 0 errors.
Per HARD RULES 8 (never commit on a red `./lean-bau`) this hunk was
reverted and is NOT in the tree — the tree stands at its
probe-green, last-full-green state. Verbatim hunk recorded here for
re-application when memory allows; a fresh independent review is then
required for the changed commit either way.

Concrete blocker: machine out of memory/address space while building
the `Grammatik` import-all aggregator, reproduced locally. Unblocks
when a serial low-contention build slot is available (nothing in the
owned module evidences any other cause). No acceptance of the full
source/binary chain is claimed.

## Task remarks

Nothing in the task appears wrong. One scoping note: the task asks for
"the memory outcome observed by the other cores after drain equals the
source's" — delivered as word + per-byte agreement between SC
`write64` and the grouped drain (no shared-memory premise needed since
both sides equal `wortByte`), rather than a whole-`Speicher` equality,
which would be false in general (frame bytes outside the footprint).
