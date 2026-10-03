# MUSE-REPORT-849: Composition closing — unwind-table closing

## Task
Close unwind tables to actual frame layouts: unwinding a frame the tables
misdescribe refuses. Compose already-accepted modules into one checked
closing step; no re-proofs, no second interpreter.

## What was done
New file `grammatik/Grammatik/X86/ComposeUnwindTable.lean` (registered in
`grammatik/Grammatik.lean`), composing the accepted `Stapel` frame/layout
vocabulary (`Rahmen`, `Belegung`, `sichereWort`/`ladeWort`,
`sichere_lade_rundreise`, `rahmenZeuge`/`speicherZeuge`,
`zeuge_lesbar8`/`zeuge_schreibbar8`) with the `StackUnwind` consumer side.
Closed producer/consumer interface: unwind-table producer rows
(`UnwindEintrag`: code range `start`/`len` plus claimed depth `tiefe` and
saved `slot`) describe; the checked frame-layout consumer
(`Rahmen` extent, `Belegung` callee-save range, actual `Speicher` bytes)
admits via the decided `unwindPasst`.

Definitions/theorems (all in `Gabbro.Grammatik.X86`):
- `UnwindEintrag` (structure: `start len tiefe slot`)
- `unwindPasst` (decided admission: rip in row range, depth equality,
  slot in layout callee-save range and in frame)
- `unwindPasst_schranke` (passing row pins slot inside frame)
- `unwindLese` (composed read: passing row loads via accepted
  `ladeWort`, misdescribing row returns `none`)
- `unwindLese_trifft` (hit through an actual memory-changing frame save;
  composes `sichere_lade_rundreise`)
- `unwindLese_falsch_tiefe` / `unwindLese_falsch_slot` /
  `unwindLese_falsch_rip` (depth / slot / range misdescription refuses)
- `ComposeUnwindTable_verbindung` (TARGET: passing row delivers the
  saved word AND the same row with depth off by 16 refuses)
- `ComposeUnwindTable_verbindung_zeuge` (joint witness: layout with two
  callee-save words, 42 observably stored at the described slot,
  byte-level memory change shown, hit plus planted refusal)
- `zeugenBelegung849`, `zeugenEintrag849`, `zeugenRip849`, `zeugenM849`,
  `zeugenPasst849`, `zeugenSchreibt849` (witness parts)
- `sonde_reichweite_verweigert849`, `sonde_slot_verweigert849`
  (planted range/slot refusal probes on the witness shape)

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeUnwindTable.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (511 jobs).`
- `#print axioms`: every theorem depends at most on `[propext,
  Quot.sound]` (subset of the standard `gabbro_ziel` set); no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`; every premise is used.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched. Only owned files changed.

## What remains open
See the `CUTS:` block in the file: no decoder/fetch/TSO bridge,
no canonical `.eh_frame` byte correspondence (row shape is the checked
interface, not parsed object bytes), no multi-frame cascade (single row,
single frame; nesting stays with `StackUnwind`), `none` is absence of a
transition (no termination claim), async unwinding and concurrency OPEN.
Owning lanes for the missing producer legs: codec/execution/bridge/
validator-skeleton lanes behind `decodeExt`, `schritt`/`extByteschritt`,
the TSO bridge and `valX86` (named generically, not assumed).

## Task assessment
Nothing in the task looked wrong. The INHABITATION bar for X86 hardware
modules was met the StackUnwind/TableLayout way (concrete frame, layout
with callee-save words some function saves, reached memory-changing save
with byte-level change, planted refusals); there is no source-level
`Vertrag`/`Stmt` quantification here, so the source-program witness
reading of rule 13 does not apply beyond the joint target witness,
which is provided.
