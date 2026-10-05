# MUSE-REPORT-1218: Exact review of candidate 1217 (Pipeline atomics: execBlock correspondence)

Lane 1218, clone `/home/simon/Dokumente/gabbro-muse/a1218`, branch `muse/1218`
(verified at start: `pwd`, `git branch --show-current`, `git rev-parse HEAD`
= `d457fd09`). Report-only exact review; owned file is this report alone.
No Lean or Rust files touched.

## Candidate

CANDIDATE: 1217 8b5ae874afa50216dfee107411603dae0ed30dd1

- Author lane 1217, pinned HEAD `8b5ae874afa50216dfee107411603dae0ed30dd1`,
  base `988d75ef42521f5d437a0cb4b9d92b5d5c2e38f2`
  (from `.tmp/review/SNAPSHOT.json`; the lane file carried only a
  placeholder without the pinned hash, the staged snapshot
  supplied the exact hash; `clean: true`).
- Reviewed material (inside my own clone only, hard rule 1): staged
  `.tmp/review/author-1217/PATCH.diff` (741 lines, read in full),
  `OWNER-TASK.md`, `MUSE-REPORT-1217.md`, `BUILD-EVIDENCE.json`, plus the
  snapshot copies of the new file and `Grammatik.lean`. The author clone
  itself was never touched.
- Candidate diff: one new file
  `grammatik/Grammatik/X86/PipelineAtomicsBlock.lean` (609 lines),
  one appended line `import Grammatik.X86.PipelineAtomicsBlock` in
  `grammatik/Grammatik.lean`, and `MUSE-REPORT-1217.md`.

## Checks (each against the pinned diff)

1. **No banned tactics/axioms.** The final `.lean` code contains no `sorry`,
   `admit`, `axiom`, `native_decide`, `unsafe`, `split_ifs`, `norm_num` or
   `ring_nf` (grepped the staged file; the only matches for these tokens in
   the snapshot are `#print axioms` lines and prose). One intermediate
   `lean-probe` run in BUILD-EVIDENCE shows a `declaration uses sorry`
   warning at line 286 during development; the final file is clean and the
   final probe is `0 error(s)`. Process transparency only, not a defect.
2. **Axioms standard.** Final `./lean-bau` in the author clone: exit 0,
   640 jobs, every `#print axioms` within
   `{propext, Classical.choice, Quot.sound}` (most on subsets, several on
   none). No new axiom.
3. **Existing files untouched except one import line.** PATCH shows exactly
   one added import line in `Grammatik.lean`; nothing else modified.
   `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched. No new
   diagnostic codes, gift/example numbers, or German text (refusals reuse
   `senkListe = none` / `valAtom = false`).
4. **Every premise used; no rule-4 violation.** All theorem premises occur
   in their statements and proofs (checked each: `sperrlauf_*` consume
   their run proofs by induction; `bind_cas_fehlschlag` rewrites every
   hypothesis into the accepted adapter; `abblock_correct` uses `hsrc`
   via determinism rewrite; `gift_block_val_nested`'s `ts` stays in the
   statement, it is a validator parameter, not a contracted-away value).
   `ab_quelle`/`abblock_correct` conclusions are computed values
   (`rfl`-closed `execBlock` run), not premises renamed. No `intro _`,
   no unused-hypothesis dodge.
5. **Family evaluator lifted, not copied.** The file imports only
   `Grammatik.X86.PipelineAtomicsBind` and reuses accepted definitions
   unchanged, each confirmed present in this tree: `senkListe`/`valAtom`
  /`senk_cas`/`sperre_korrekt`/`erreichbar_kette`/`senkAtom_zeuge`
   (`PipelineAtomics.lean`), `lockVoll_cmpxchg_fehlschlag_adapter`
   (`LockedInstructionExecution.lean`), `mfenceDrain`/`mfenceDrain_leert`
   /`fdS2`/`fdStart`/`fdX` (`MfenceDrainOwn.lean`, `FenceDrain.lean`),
   `drainKernN_null`, `cas_schliesst`, `pinMfence`, `witD`. No canonical
   definition duplicated; all new names are `Sperr*`/`ab*`/`block_*`/
   `gift_block_*`.
6. **Refusals really refuse.** `block_nested_verweigert` by `decide`;
   `gift_block_val_nested` by rewrite with it; `gift_block_val_ueberlang`
   by `decide`; `abblock_refuses_nested` by induction over the prefix
   following the lane-1163 shape. All decided/computed, none assumed.
7. **Witness non-degenerate.** `abblock_zeuge` jointly instantiates the
   source run (rows 7 -> 42 and 9 -> 17, atomic 41 -> 42, all `rfl`-closed
   through the real `execBlock`), the written table
   (`abV.schreibt () = true`), the emitted lowering (`abOps_senk`),
   a memory-changing target run (reused accepted `senkAtom_zeuge` MFENCE
   run: `s2.mem.bytes fdX != s3.mem.bytes fdX`, nonempty buffer),
   the bracketed section (`ab_sperrlauf_inst` over the accepted `fdS2`
   drains with proved drain idempotence), the register-bound CAS failure
   stutter, and the block refusal. Source and target sides both change
   memory; a table is written. The target leg reuses the accepted two-core
   `fd` witness states; the new section instance is single-core core-0,
   consistent with the ONE-core `Pipeline` scope the task cites.
8. **Silicon facts.** No new hardware facts: MFENCE bracketing, LOCK
   CMPXCHG failure stutter, release/acquire as plain MOVs are the accepted
   family's decided behaviours (recomputed by `rfl`/`decide`, never
   restated). Concrete addresses/registers reuse accepted witnesses.
   Nothing checked against the SDM extracts because nothing new is
   claimed about silicon.
9. **CUTS honest; claim matches proof.** Full CUTS block present,
   `#print axioms` for all 26 theorems. Explicitly NOT claimed: TSO word
   install for the block MOVs, integer-slot machine run (both cited to
   lanes 1163/1203 and accepted `Pipeline`), SFENCE/LFENCE, per-step
   framing of arbitrary middles (stays an explicit premise of
   `SperrSchritt`), seq_cst total order, fairness, retry bounds, timing,
   interrupts, devices, MMIO, DMA. No hardware-correspondence or W/GX
   claim. Two honest narrowings recorded, both documented: `sperrlauf_leer`
   needs its `!= []` premise (the empty block drains nothing — true), and
   `ab_sperrlauf_inst`'s middle run is the empty reached run (real work is
   the entry drain of the nonempty `fdS2` buffer; the definition promises
   no more).

## My own build

`./lean-bau` in this clone (which does NOT contain the candidate):
`== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (642 jobs)`.
This validates the base tree only; the candidate's own green build
(exit 0, 640 jobs, per-theorem axiom lines) is recorded in BUILD-EVIDENCE.

## Integration note (not verdict-changing)

The candidate base (`988d75ef`) predates this clone's HEAD (`d457fd09`):
`Grammatik.lean` has since gained `HwLockFetch`, `HwDrainGeneric`,
`TsoRmwLink` imports. The candidate's import append will need the usual
import-union at merge; its new file depends only on `PipelineAtomicsBind`
and additive accepted definitions, so rebase risk is low, but the merged
tree must rebuild (merger's gate, not this review).

VERDICT: ACCEPT

Candidate 1217 at `8b5ae874afa50216dfee107411603dae0ed30dd1` is accepted as
reviewed: exact scope kept (one new file + one import line + report), green
build with standard axioms, no banned constructs, lifted-not-copied family
definitions, genuine refusals, non-degenerate joint witness, honest CUTS,
and no claim beyond the proof.
