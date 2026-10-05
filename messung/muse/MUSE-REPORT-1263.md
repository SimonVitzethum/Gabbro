# MUSE-REPORT-1263: per-chunk derivation for if/else and checks

Lane 1263, follow-up of lane 1219 (`PipelineChunkDerive.lean`).
Clone `/home/simon/Dokumente/gabbro-muse/a1263`, branch `muse/1263`: verified.
Owned files only: `grammatik/Grammatik/X86/PipelineChunkIte.lean` (new),
`grammatik/Grammatik.lean` (one appended import line),
`MUSE-REPORT-1263.md` (this file).

## What was done

New module `Gabbro.Grammatik.X86.PipeChunkIte` deriving the chunk
run/coverage premises for `ite` and bound checks (`Block.pruefung`)
from the lowering alone, reusing the accepted `Pipeline.lean` if/else
lowering (`senkBlock_ite_inv`, `senkPruef`, `senkBedT`,
`senkBlock_korrektC`) and `ExpressionLoweringDeep.lean`
(`senkVergleich`) as black boxes. No second IR, no second
interpreter, no optimiser edit, no existing-file edit (except the
import line), no `OptimizationRules` touch. All `#print axioms` are
standard (`propext`, `Classical.choice`, `Quot.sound` at most); no
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Definitions: `iteCheckValidate`, `witIteT1263`, `witIteE1263`,
`witIte1263`, `witIteProg1263`, `iteMemBytes1263`, `iteCode1263`,
`iteMem1263`, `iteStart1263`, `witPruef1263`, `witPruefProg1263`,
`pruefMemBytes1263`, `pruefCode1263`, `pruefMem1263`,
`pruefStart1263`, `witCallArgs1263`.

Generic theorems: `iteChunk_inv_abgeleitet`,
`iteChunk_lauf_abgeleitet`, `pruefChunk_inv_abgeleitet`,
`pruefChunk_lauf_abgeleitet`, `iteChunk_deckung_abgeleitet`,
`pruefChunk_deckung_abgeleitet`, `iteCheckValidate_sound`,
`iteChunk_sprungZiele`, `iteChunk_sprungOk_entscheidung`,
`pipelineChunkIte_schluss`,
`pipelineChunkIte_verweigert_traverse`,
`pipelineChunkIte_verweigert_call`.

Witnesses/Helpers: `witIteLow1263`, `iteChunk_inv_abgeleitet_zeuge`,
`witIteLowLit1263`, `ite_len1263`, `ite_code1263`,
`ite_worldRep1263`, `ite_envRepr30_1263`, `ite_envRepr70_1263`,
`iteChunk_lauf_abgeleitet_zeuge`, `witPruefLow1263`,
`witPruefLowLit1263`, `pruefChunk_inv_abgeleitet_zeuge`,
`pruef_len1263`, `pruef_code1263`, `pruef_worldRep1263`,
`pruef_envRepr30_1263`, `pruef_envRepr70_1263`,
`pruefChunk_lauf_abgeleitet_zeuge`, `pruefChunk_grund1263` (concrete
failing route to the refusal exit),
`iteChunk_deckung_abgeleitet_zeuge`,
`pruefChunk_deckung_abgeleitet_zeuge`,
`iteCheckValidate_sound_zeuge`, `pipelineChunkIte_schluss_zeuge`,
`witCallHw1263`, `witCallHk1263`, `witCallHg1263`, `witCallHh1263`,
`witCallHp1263`, `witCallHr1263`.

Poison probes (fire by `rfl`/the named refusal): `gift1263_traverse`
(`traverse` head refused), `gift1263_call` (`call` head refused),
plus `pipelineChunkIte_verweigert_traverse_zeuge` and
`pipelineChunkIte_verweigert_call_zeuge` joint witnesses with the
shared non-degenerate `PipePaket` (one table its contract writes;
source runs `7 -> 35`; memory-changing fetched-byte run).

Jump layout and relaxation: `iteChunk_sprungZiele` pins the
`iteSprung`/`iteEnde` displacements with the taken-jump landing facts
from the decided `sprungOk` checks; the check inversion carries the
reason-exit landing equation; `iteChunk_sprungOk_entscheidung` states
the gate is exactly the 32-bit round trip (out-of-range is refused,
never truncated).

## Last build results

- `./lean-probe grammatik/Grammatik/X86/PipelineChunkIte.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (652 jobs).`

## What remains open (see CUTS in the file)

- Only closed single-`ite` and single-`pruefung` chunks are derived;
  longer sequences compose through accepted `senkBlock_korrektC`.
- Short (rel8) branch relaxation is not introduced; the `ISARelax`
  layout stays unconnected (named OPEN, not claimed).
- Single core, model memory, no TSO/concurrency; entry/image/ABI via
  `PipelineImage`/`PipelineEntry`; timing stays a hardware assumption.
- `retry`/`forever` refusals are reused from `PipeWorkBranches`, not
  re-proved.

## Notes on the task

- "Bound checks" is read as `Block.pruefung` checks with reason
  exits (the only check form `senkBlock` lowers); both the passing
  (empty code) and failing (exit jump) shapes are covered by the
  inversion, but only the jump shape is witnessed (the witness
  condition is not a literal `true`).
- The derived runs specialize the accepted `senkBlock_korrektC`
  (like `zweig_arbeit_korrekt` does) instead of re-proving the
  jump cases; the new content is the closed-chunk inversion, the
  validator, the jump-layout facts, the coverage derivation and the
  refusals. This is weaker than a from-scratch chunk simulation but
  it is exactly the "premises derived from the lowering" the task
  asks for.
- Two findings for future lanes: (a) `cases h : x` on `Endblock`
  did not substitute the variable in this file while plain `cases`
  did (worked around, no proof impact); (b) inline `nomatch` inside
  a structure instance broke parsing, named helper theorems did not.
