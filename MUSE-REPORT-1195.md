# MUSE-REPORT-1195: Pipeline block-size induction over multi-statement blocks

## What was done

New file `grammatik/Grammatik/X86/PipelineBlockInduct.lean` (510 lines,
namespace `Gabbro.Grammatik.X86.PipeBlock`) plus one import line appended to
`grammatik/Grammatik.lean`. Follow-up of lanes 1165/1189/1191: single shallow
assignment chunks now compose by induction over the block.

**Deliberate deviation from the task text, stated plainly:** the task asked
for "a lowering/validator" in the new file. No new lowering was introduced:
`senkStmt`/`senkBlock` are the canonical lowering and rule 16 forbids
duplicating them. The composition is proved OVER the existing lowering
(`senkBlock_assign` reused for the block-lowering equation). This is
stronger for the pipeline (one lowering, one validator) and matches the
architecture decision (no second representation).

## New definitions/theorems (exact names)

- `KetteLauf` (inductive): run chain over statement chunks; block-size
  induction is induction on this chain.
- `decodiertZu_append`, `ketteLauf_lauf` (chain run = flattened-block run
  via reused `lauf_anhang`), `ketteLaenge_sum` (work = sum of chunk works).
- `deckung_append_pipe` (two coverages concatenate at the sum budget, via
  reused `pipeSummary_expand` — honest zero spill/fence, never a premise),
  `blockDeckung_eins` (induction over the chunk list), `zeit_append_pipe`
  (time sums via reused `laufKosten_anhang_erfolg`).
- `block_zwei_korrekt`: two lowered-correct assignment chunks compose —
  source `execBlock` run, target `lauf` run, `Deckung`, named time, retired
  work, the `senkBlock` lowering equation, and the time-transfer bound
  (reused `budgetAusfuehrung_transfer`). Every premise is used
  (`hlow1/hlow2` feed the lowering equation; `hb1/hb2` feed the transfer).
- Refusals (all `= none`, never guessed): `block_verweigert_tief`
  (generic, `frei = []`, reuses accepted `senkTief_verweigert_tief`),
  `block_verweigert_tief_stmt` (statement level, same index/layout as the
  accepted shallow chunk, so the refusal is from depth alone),
  `block_verweigert_verzweigung` (`onOption`), `block_verweigert_schleife`
  (`retry` head), `block_verweigert_bind` (`bind` block).
- Poison probes firing by computation: `gift_block_tief_wert`,
  `gift_block_schleife`, `gift_block_bind`, `gift_block_verzweigung`.
- Witnesses: `tiefWert1195`, `tiefWertFeld1195`, `witStmt1195`,
  `block_verweigert_tief_zeuge`, `block_verweigert_verzweigung_zeuge`,
  `block_verweigert_schleife_zeuge`, `block_verweigert_bind_zeuge`,
  `block_zwei_korrekt_zeuge` (joint on the accepted `pw` package: one
  table its contract writes, two reached source steps, two 5-instruction
  chunk runs with named time 8 / bound 3, plus reused `PipePaket` with the
  fetched-byte memory-changing run).

## Last build result

- `./lean-probe grammatik/Grammatik/X86/PipelineBlockInduct.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (627 jobs).`
- `#print axioms`: every theorem depends only on subsets of
  `propext, Classical.choice, Quot.sound`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no Prop-typed
  premise; existing files untouched except the import line.

## What remains open (see CUTS)

- Per-chunk derivation: chunk runs/coverage are premises here; deriving
  them from lowering alone stays with `senkBlock_korrekt`/`pipeline_correct`.
- n-chunk dependent source `Block` chains beyond two `assignSlot` conses.
- Entry/image admission, TSO/concurrency, `forever`/`call` theorems
  (same catch-all arms, prose only).

## Task assessment

Nothing in the task appears wrong. The "carried `Deckung`" composition the
task names is exactly `blockDeckung_eins` + `block_zwei_korrekt`; the
additivity is `deckung_append_pipe` + `ketteLaenge_sum` + `zeit_append_pipe`.
