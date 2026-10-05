# MUSE-REPORT-1227: Pipeline spills — variable homing and live-range splitting

## What was done

New file `grammatik/Grammatik/X86/PipelineSpillHoming.lean` (plus one
`import Grammatik.X86.PipelineSpillHoming` line appended to
`grammatik/Grammatik.lean`). Follow-up of lane 1191
(`PipelineSpill.lean`): where 1191 saves/reloads whole named slots with
no homing decision and whole-block live ranges, this lane adds a decided
homing — per variable a private spill home slot (`heim`, parallel to the
register allocation) plus live-range splits at statement boundaries
(`schnitte`: variable index with its slot at that boundary) — validated
by a decided check, with a closing theorem composing accepted pipeline
correctness with homing privacy. A homing that clobbers is refused.

Design (no second IR, no second evaluator, no optimiser edit; all
accepted definitions reused unchanged):

- `PipeSpillHoming`: `{ alloc : PipeRegAlloc, heim : List Nat,
  schnitte : List (Nat × Nat) }`.
- `homingSlots H = H.heim ++ splits`: every slot the homing names.
- `pipeHomingOk H c codeLen daten`: `pipeRegAllocOk` over the allocation
  && home/variable length agreement && `spillPlanOk` over every named
  slot && every split names an in-range variable.
- Closing `pipeHoming_haelt_bedeutung` (in the style of
  `pipeline_correct`): validated bytes under the homed allocation plus a
  validated homing over a table-free frame give the fetched byte run
  (world/environment represented), `PipeInterferenzFrei`, homing-table
  privacy, pairwise slot separation, slot-vs-extent separation. Composed
  from `pipeline_correct` plus the accepted allocator/spill legs; every
  premise is used.
- Four general refusals: clobbered registers, table extent,
  out-of-frame slot, out-of-range split. One positive and five refusal
  probes (clash/table/out-of-frame/split through their refusal
  theorems).
- Joint non-degenerate witness `pipeHoming_haelt_bedeutung_zeuge` on the
  pipeline witness program `pwSrc` (rows 7 -> 35, 9 -> 6).

## Exact new names

Defs: `PipeSpillHoming`, `homingSlots`, `pipeHomingOk`,
`HomingVonTabellenGetrennt`, `pipeH0`, `pipeHD0`, `pipeHBadClash`,
`pipeHBadAussen`, `pipeHBadSchnitt`, `pipeHBadCode`.
Theorems: `pipeHoming_allocOk`, `pipeHoming_laengen`,
`pipeHoming_planOk`, `pipeHoming_schnittOk`,
`pipeHoming_tabellenGetrennt`, `pipeHoming_schlitze_getrennt`,
`pipeHoming_haelt_bedeutung`, `pipeHoming_verweigert_kollision`,
`pipeHoming_verweigert_tabelle`, `pipeHoming_verweigert_aussen`,
`pipeHoming_verweigert_schnitt`, `pipeHoming_probe_pos`,
`pipeHoming_probe_clash`, `pipeHoming_probe_tabelle`,
`pipeHoming_probe_aussen`, `pipeHoming_probe_schnitt`,
`pipeHoming_probe_code`, `pipeH0_getrennt`, `pipeH0_cfg`,
`pipeHoming_haelt_bedeutung_zeuge`.
Axioms: at most `propext`, `Classical.choice`, `Quot.sound` (verified
via `#print axioms` for every name).

## Last build result

`./lean-bau`: `exit 0`, `Build completed successfully (641 jobs)`.
`./lean-probe grammatik/Grammatik/X86/PipelineSpillHoming.lean`:
`0 error(s)`. Note: the first three `./lean-bau` runs failed on
transient apparatus faults at the root `Grammatik` step only
(`failed to create thread`, then `failed to read file` for a different
unrelated `.olean` each run while all module oleans including my new
one were present); the fourth run passed 641/641 with no source change.
This matches the known resource-pressure pattern, not a code defect.

## What remains open

See CUTS in the file: no save/reload bytes are spliced at split points
(the homing decides homes; lane 1191's fragments are the vocabulary a
splitter would splice); one home slot plus split slots per variable, no
merging of overlapping ranges into one slot (refused by plan `Nodup`);
no calls/callee-saved/argument passing; TSO freshness beyond the reused
`SpillFrisch` vocabulary; no `pipeline_correct_loaded` re-proof.

## Task remarks

Nothing in the task is believed wrong. One clarification: the task asks
for a correctness theorem "in the style of `pipeline_correct_entry`"
and a refusal "(`pipeline_refuses_*`)". The homing validator sits at
the `pipeline_correct` level (whole-program bytes + frame), not at the
ABI-entry level (no parameter ABI is involved in homing), so the
closing theorem is stated in the style of `spill_haelt_bedeutung` /
`pipe_alloc_haelt_bedeutung` (which themselves wrap
`pipeline_correct`), and refusals follow the `spill_verweigert_*` /
`pipe_alloc_verweigert_kollision` pattern. The entry-level connection
is inherited, not re-proved.

## Repair response to MUSE-REPORT-1228 (REPAIR: candidate not readable)

The 1228 exact review reports `bad object` for pinned candidate
`638654c2736f9dfd6e0ed5d03af60c411d9261a5` in reviewer clone a1228 and
performs no content checks. Verified in this clone (a1227):

- branch is `muse/1227`, HEAD is `638654c2` (full hash above), tree clean;
- `git show HEAD --stat` lists exactly the three snapshotted files
  (`MUSE-REPORT-1227.md`, `grammatik/Grammatik.lean` +1 line,
  `grammatik/Grammatik/X86/PipelineSpillHoming.lean` new, 394 lines).

The finding identifies no defect in the deliverable content, so no Lean
content was changed. The missing object is a fetch/availability matter
between clones: HARD RULES rule 1 forbids this lane from touching
anything outside its own directory (no push, no cross-clone copy, no
network), so the repair on this side is to keep the candidate intact and
fetchable at its canonical location (`muse/1227` in this clone) for the
coordinator's `muse-merge.sh` fetch path. Re-verified green after the
review: `./lean-probe` 0 errors, axioms at most
`propext, Classical.choice, Quot.sound`; prior `./lean-bau` green at
641 jobs on this exact tree.
