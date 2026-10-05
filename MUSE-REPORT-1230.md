# MUSE-REPORT-1230: Exact review of candidate 1229 (PipelineCallsBlock)

Lane 1230, clone `/home/simon/Dokumente/gabbro-muse/a1230`, branch `muse/1230`
(verified: `git branch --show-current` = `muse/1230`).
OWN ONLY `MUSE-REPORT-1230.md`. Report-only exact review, no Lean/Rust edits.

CANDIDATE: 1229 39f795fc54ca317ef9e27db09b5220c0caaf486e
VERDICT: ACCEPT

## Candidate

- Author lane 1229, pinned HEAD `39f795fc54ca317ef9e27db09b5220c0caaf486e`
  (from `.tmp/review/SNAPSHOT.json`; base `cbc0afe00eeb8708961b13489750e41e998740d1`).
- Reviewed material (in-clone, no outside touch): `.tmp/review/author-1229/PATCH.diff`
  (680 lines, read in full), `MUSE-REPORT-1229.md`, `BUILD-EVIDENCE.json`,
  `OWNER-TASK.md`, snapshot file `grammatik/Grammatik/X86/PipelineCallsBlock.lean`.
- Files touched by candidate (per SNAPSHOT.json): exactly 3 —
  `MUSE-REPORT-1229.md` (new), `grammatik/Grammatik.lean` (one appended import
  line `import Grammatik.X86.PipelineCallsBlock`), and the new owned file
  `grammatik/Grammatik/X86/PipelineCallsBlock.lean` (547 lines). No existing
  theorem touched, no `OptimizationRules`/`OptimizationWitnesses` touch.

## Checks performed (all on the exact diff/snapshot)

- **Banned tokens:** grep over the new file finds no `sorry`, no standalone
  `admit` (8 hits are all the English word "admitted" in comments), no `axiom`
  declaration, no `native_decide`, no `unsafe`, no `sorryAx`. No `intro _`,
  no `have _ :=`. No `Prop`-typed premise (all premises are `Bool` equalities,
  `WorldRep`/`EnvRepr`/`CodeAt`/`LayoutSep` facts, or concrete `execBlock`
  equations). No `split_ifs`; only `split`-safe `cases`/`by_cases` reasoning.
- **`#print axioms`:** BUILD-EVIDENCE probe output lists every new
  definition/theorem; main theorems depend only on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard). `zweiRuf_korrekt` and
  `zweiRuf_korrekt_zeuge` are exactly `[propext, Classical.choice, Quot.sound]`.
- **Premise use (`zweiRuf_korrekt`):** every premise is consumed — `hval` via
  `rufBlockOk_teile` (frame admission + recomputed bytes through
  `validate_sound`), `hsep` in both `worldRep_store` steps, `hfremd` via
  `calleeFremd_mem` for the chained preservation, `hcode`/`hrip` in
  `lauf_zu_laufBytes`, `hW` for the first store representation, `hE` into both
  `einzelChunk_lauf` derivations, `hsrc` rewritten through the two
  `constInt?_sound` inversions and `cases`-closed. No discarded hypothesis.
- **Lifted, not copied:** per-chunk runs come from the accepted 1189
  `einzelChunk_lauf`; target composition calls 1195's `KetteLauf` /
  `ketteLauf_lauf` as library lemmas. No redefinition of the family vocabulary
  in the new file. `PipelineChunkDerive` (1211) is correctly NOT imported
  (absent from tree); the otherwise-branch is honored and improved upon —
  chunk runs derived, only composition reused.
- **Refusals really refuse:** shape gate `istZweiZuweisung` plus validator
  refusals `rufBlockOk_verweigert_rot/_form/_bytes`; planted probes close every
  path by computation (`bwProbe_form1`, `_formNil`, `_formPruef` by `rfl`;
  `bwProbe_bytes` by `decide`; `bwProbe_formRuf`, `_rot`, `_bytesRuf` through
  the refusal theorems). Unsupported shapes refused, never guessed.
- **Witness non-degenerate:** `zweiRuf_korrekt_zeuge` jointly proves
  `pwV.schreibt () = true`, validated bytes, `LayoutSep`, `CodeAt`, `WorldRep`,
  `EnvRepr`, a source run turning rows 0/1 from 7/9 to 35 (memory-changing),
  a reached byte run preserving all six callee-saved registers, frame saves
  that observably change memory (`rufWit_wechselt`), and the `ladeWort`
  round trip (`some 42`).
- **Silicon:** no new encodings, fault classes, or ordering claims. Witness
  bytes are produced by the accepted `encodeAll`; execution via accepted
  `laufBytes`/`decodiertZu`/`kanon`. Address register `r11` is off the
  callee-saved set per reused `cwCfg`. New-file scope only.
- **CUTS honest, no overclaim:** CUTS block (lines 467-511 of the new file)
  records exactly two-assignment scope, `certs = []`, sequential `Speicher`
  only with the TSO/GX bridge OPEN, preservation via `calleeFremd`
  disjointness (no spill modelling), and no loader/entry/relocation/cost/time
  claim. No hardware-correspondence or W/GX claim anywhere.

## Build status (honest)

- `./lean-bau` in this review clone (base tree, candidate NOT applied —
  OWN ONLY forbids it): last result line
  `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (641 jobs)`). Base is healthy.
- Candidate's own builds (BUILD-EVIDENCE.json): `./lean-probe` on the complete
  new file 4x `0 error(s)`, including axioms output; `./lean-bau` in the
  author clone RED with `failed to read file ...` for a DIFFERENT dependency
  artifact on each of 3 runs (toolchain `Init/Data/SInt` olean, then a present
  project olean, then a toolchain `Std/...RupAddResult` olean) while the probe
  elaborates the same file fully. This pattern (unreadable toolchain-owned
  oleans, varying victim, green probe) is apparatus failure in that clone, not
  a defect attributable to the new module's content. The merge flow rebuilds
  `grammatik/` in its own tree before committing, which is the correct remedy;
  noted here so the merger re-verifies green rather than trusting this report.

## Substantive finding: accept the candidate

Candidate 1229 at `39f795fc54ca317ef9e27db09b5220c0caaf486e` is accepted as
reviewed: probe-green complete file, standard axioms, single import line,
premises fully consumed, evaluator lifted not copied, refusals planted on every
path, non-degenerate memory-changing witness, no silicon invention, honest
CUTS with no hardware-correspondence or W/GX claim. Condition for the merger:
rebuild `grammatik/` via `muse-merge.sh` and confirm green (author-clone
apparatus red is documented above, not a candidate defect).

## Open / notes

- Three-or-more-statement callee bodies stay OPEN (refused here by design).
- This review could not execute the candidate in its own tree (ownership rule);
  it rests on the full diff, the snapshot file, and the recorded probe/axiom
  evidence. The merger's rebuild is the final gate.
- Nothing in the owner task (lane 1229 prompt) is believed wrong.
