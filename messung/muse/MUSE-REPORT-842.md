# MUSE-REPORT-842: Composition closing — fault-ledger closing

## What was done
Closed the fault/refusal/stop order across the whole image in one checked
composition step, over already-accepted modules only.

New file `grammatik/Grammatik/X86/ComposeFaultLedger.lean` (owned), plus the
one-line import in `grammatik/Grammatik.lean` (owned). No other files touched.

Producer/consumer interface closed: the admitted image (`valX86`, consumer of
`wohlgeformt` + decode coverage, lane 349) feeds the byte step from actual
executable memory (`extByteschritt`, producer of `weiter`/`halt`/`verweigert`,
lane 575); the fault classifier (`klassifiziereExt`/`ArchFehler`, lanes 670/543)
reports the kind; the two-step ledger (`ledgerSchritt2`) keeps the order;
trapping divisions stay impure (motion/DCE refusal, producer `DecodeFault`
lane 543); stops are reported by kind with order preserved (reused joint
source/target stopping order `stoppReihenfolge` and refusal projection
`beobachtung_stopp_sichtbar`, lane 572).

## Exact new definitions/theorems
- `LedgerOut` (inductive: `weiter`/`halt`/`verweigert`), `ledgerSchritt`,
  `ledgerSchritt2`
- `ledger_verweigert_bei_mapping`, `ledger_halt_klasse`,
  `ledger_weiter_ohne_fehler`, `ledger_verweigert_bei_schritt`
- `ledger_ordnung_kopf`, `ledger_ordnung_halt`, `ledger_stopp_nach_art`,
  `ledger_falle_nie_optimiert`
- `ComposeFaultLedger_verbindung` (TARGET) with companion
  `ComposeFaultLedger_verbindung_zeuge` (jointly inhabited: admitted minimal
  image + reached one-step store run moving cell 8192 observably 0 -> 42,
  two planted refusals, zero-divisor trap with #DE class, impurity pair)

## Last `./lean-bau` result line
`Build completed successfully (509 jobs).` — whole-project green.
`./lean-probe grammatik/Grammatik/X86/ComposeFaultLedger.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
Every `#print axioms` reports `[propext, Quot.sound]` only (subset of the
`gabbro_ziel` standard `[propext, Classical.choice, Quot.sound]`).

## What remains open
See the `CUTS:` block in the file: no fault priority / #UD membership beyond
the reused classifier (lanes 670/672); no `valX86_sound` and no
source/TSO/GX/concurrency/contract/budget-transfer/cost/time/FP claim; no new
target semantics; no checker/source/Spec/goal/emitter change.

## Task fidelity notes
Nothing in the task is believed wrong. No new diagnostic/gift/example/CLI
numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
friend-reserved optimiser files. No `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`; every premise is used; no conclusion restates a premise.
