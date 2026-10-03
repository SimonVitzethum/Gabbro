# MUSE-REPORT-839: FP-ledger closing

## What was done

New file `grammatik/Grammatik/X86/ComposeFpLedger.lean` (~350 lines) plus the
one-line import in `grammatik/Grammatik.lean`. It closes every FP operation
to its control-state ledger at its site by composing already-accepted
modules, reusing their definitions by name without re-proving internals and
without duplicating any interpreter or executor.

Closed producer/consumer interface: input is the scope ledger entry `k :
FpLedger` (= `FPKontext`, the admitted word of the scope) plus the fetched
site (`fpFetchDekodiert` from actual executable bytes); output is the
accepted `fpSchritt` successor with the ledger still holding.

Definitions:
- `FpLedger` (abbrev for `FPKontext`): the scope's admitted word.
- `fpLedgerSchritt k d t`: admit (`fpEintritt`: RNE, masks, no FTZ/DAZ) AND
  scope match (`t.fp = k`) at entry, then the accepted `fpSchritt`, then
  ledger still holds (`t'.fp = k`). `none` is explicit refusal.
- `fpLedgerByteschritt k t`: fetch via accepted `fpFetchDekodiert`, then
  the §1 ledger step. A forged decoded value can never inject an
  instruction.

Theorems (every premise used by its proof):
- `fpLedgerSchritt_ledger_verweigert`, `fpLedgerSchritt_kreuzung_verweigert`,
  `fpLedgerSchritt_erfolg`, `fpLedgerSchritt_schritt` (runs the accepted step),
  `fpLedgerByteschritt_hol_verweigert`, `fpLedgerByteschritt_schritt`.
- `ComposeFpLedger_verbindung` (TARGET): guarded byte success implies the
  accepted step on the fetched form ran AND `t1.fp = k` AND admission still
  holds.
- `ComposeFpLedger_keineKontraktion`: one guarded ADDSD is exactly one
  `fpRechne .add` application (one rounding, no FMA contraction).
- Planted refusals, one varied leg each, decided on actual words:
  `ComposeFpLedgerNeg_ftz` (0x9F80), `_daz` (0x1FC0), `_runde` (0x3F80, RNE
  leg), `_maske` (0x0F80, mask leg), `_kreuzung` (admitted 0x1FBF under the
  reset ledger: scope crossing refuses), `_nachLaden` (reached LDMXCSR load
  installs 0x1FBF, so the old ledger entry no longer matches).
- `ComposeFpLedgerWit_schritt` + `ComposeFpLedger_verbindung_zeuge`
  (companion): all premises jointly on the accepted `fpCodecT` store image;
  the word reads back (`+inf` at 0x2004/0x2000 region, address 8192) and one
  byte observably changed. Non-degenerate reached memory-changing run.

## Last build result

`./lean-bau`: `Build completed successfully (509 jobs).` Zero errors.
`./lean-probe grammatik/Grammatik/X86/ComposeFpLedger.lean`: 0 errors.
Axioms per theorem: `[propext, Quot.sound]`, witness theorems additionally
`Classical.choice` — all within the standard `gabbro_ziel` set
(`propext, Classical.choice, Quot.sound`). No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`.

## What remains open (explicit CUTS in the file)

- No new semantics/decoder/encoder/profile data (reuse only).
- No per-form ledger frames beyond the post-step word check (follow-up lane).
- No VEX/x87/FMA/packed forms, REX extension, TSO/GX leg, or
  validator/image/entry/budget integration (other lanes per
  DIRECT-COMPILER.md). Missing legs are cuts, never assumed.

## Task feedback

Nothing in the task was wrong. The scope-crossing leg needed an admitted word
distinct from the ledger entry; the sticky-flag word 0x1FBF (admitted, from
`mxcsr_sticky_egal_gueltig`) fills exactly that role, and the reached
LDMXCSR fragment (`mxcsrWit_schritt1`) supplies the control-change case.
