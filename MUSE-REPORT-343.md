# Muse Report 343 — Reviewed organisation plan B3: SpillPrivate (O-spill producer half)

Branch `muse/343`, clone `/home/simon/Dokumente/gabbro-muse/a343`.
Task: TSO-side freshness => disjointness => commutation lemma for private
spill slots (`GetrenntK` shape); SCFG-side application waits for the accepted
287 interface. Reviewer: 381.

## What was done

New file `grammatik/Grammatik/X86/SpillPrivate.lean` (~400 lines), plus one
additive import line at the end of `grammatik/Grammatik.lean`
(`import Grammatik.X86.SpillPrivate`). No other file touched. No source,
checker, Spec, goal, central canonical, Typen, Rust, emitter, docs, or
friend-reserved path touched.

Definitions (all over canonical vocabulary only, no second IR/evaluator):

- `spillSlot r idx := r.schlitzAddr idx` — honest helper reusing the
  canonical frame slot address.
- `SpillFrisch s r idx` — TSO-side freshness: no buffered byte of any core
  touches the eight spill footprint bytes.
- `GetrenntK r idx fremd := Disjunkt (spillSlot r idx) fremd` — concurrent
  separation between spill slot and foreign access footprint.
- `spillPrivatOk genommen extent imRahmen : Bool` — validator admission;
  `false` refuses, faults no hardware.
- `SpillZugelassen genommen extent s r idx` — joint admission (Bool + freshness).
- Witness frame `spillRahmenW` (base 0, depth 32: slot 0 at address 0,
  slot 2 at address 16) and reached TSO states `spillTSO0/1/2`.

Theorems:

- §1 admission: `spillPrivatOk_verweigert_genommen`,
  `spillPrivatOk_verweigert_extent`, `spillPrivatOk_verweigert_aussen`,
  `spillPrivatOk_positiv` (rfl), `spill_zugelassen_verweigert_genommen`,
  `spill_zugelassen_verweigert_extent` (address-taken / extent-named slots
  are never jointly admitted — the refusal half).
- §2 visibility: `spill_speichern_ist_write64`, `spill_laden_ist_read64`
  (spills ARE permission-checked `write64`/`read64`, never invisible),
  `spill_ausserhalb_verweigert` (loud out-of-frame refusal).
- §3 freshness: `spill_frisch_meidet_puffer`, `spill_frisch_leer`.
- §4 commutation: `spill_fill_kommutiert` (GetrenntK + four stores =>
  byte-extensional agreement both orders + no permission widening, via
  `write64_kommutiert`), `spill_stabil_bleibt_fremd` (stable footprint
  survives disjoint foreign store, via `stabilFuss_bleibt`), joint witness
  `spill_fill_kommutiert_zeuge` (all four stores reach in both orders, both
  footprints observably change `0x00`->`0x08`/`0x18`, orders agree).
- §5 TSO preservation: `spill_frisch_bleibt_bei_fremd_issue` (foreign issue
  outside the footprint keeps freshness, via `issueByte`/`issue_haengt_an`/
  `issue_anderer_kern`), `spill_bleibt_bei_fremd_flush` (foreign flush keeps
  every spill byte, via `GetrenntK` + `Fuss` membership + `flush_rahmen`).
- §6 reached TSO witness `spill_tso_zeuge`: foreign issue is a reached
  `TSOErreichbar` step preserving freshness; foreign flush keeps all spill
  bytes at start values while observably changing its own byte
  (`spill_flush_wechselt`, by decide).

## Verification

- `./lean-probe grammatik/Grammatik/X86/SpillPrivate.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (386 jobs).`
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`: 0 errors;
  `gabbro_ziel` still on exactly
  `[propext, Classical.choice, Quot.sound]`.
- Own `#print axioms`: every theorem depends on no axioms or a subset of
  `[propext, Quot.sound]` (see probe output); nothing beyond the goal's
  standard set.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no `Prop`-typed
  premise; every proof uses all its hypotheses (refusal proofs use the
  hypothesis' first projection, never `obtain` with a dropped component).

## What remains open (CUTS, also in-file)

- SCFG-side application waits for the accepted 287 interface (marked, not
  invented — no substitute IR defined here).
- No aligned multi-byte atomicity beyond byte-extensional commutation; no
  LOCK RMW; no source-to-target simulation (no source carrier mapped); no
  cost/fairness/timing claim; no new ISA form added.
- The `_zeuge` companions are target-side joint witnesses (canonical stores
  + reached TSO trace, memory changed on the foreign side / both sides);
  there is no source-syntax premise in this module, so no source-table
  witness applies — same precedent as `SpeicherKommutation`'s
  `write64_kommutiert_zeuge`.

## Notes for reviewer 381

- Plan symbol `GetrenntK` did not exist in the tree; it is defined here as
  `Disjunkt` at the spill slot vs the foreign footprint. The 287 consumer
  side is marked waiting in CUTS.
- Safety corrections honoured: refusal Bool is admission only; no new
  hardware fault or stop kind; no alignment invention (only the canonical
  `Disjunkt`/`Fuss` facts); no float/width/cost claim.
