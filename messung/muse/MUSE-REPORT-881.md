# MUSE-REPORT-881: Optimiser rule — rematerialisation (OptRematConst)

## What was done

New file `grammatik/Grammatik/X86/OptRematConst.lean` (plus one import line
in `grammatik/Grammatik.lean`): the DESIGN section 7 rematerialisation rule
lemma — recompute a cheap constant at its use site instead of spilling and
reloading it, with spill-weight accounting; rematerialising a faulting form
refuses.

- Certificate shape: `RematCert` (`billigOk`, `keinFehler`,
  `g : RematGewicht`, `einfachGerundet`, `gleicheRundung`) admitted by the
  decided Bool `rematZulassen`; `RematGewicht` (`rematKosten`,
  `spillKosten`) with decided `gewichtOk` — the local rewrite record plus
  recomputed analysis citations (literal shape via
  `InvariantenOpt.alsLitOpt`/`eval_alsLit`, recomputed spill weight, kernel
  `gleitRechne` in one rounding scope). A refused site keeps the spill:
  never a warning.
- Refusal cases proved of the Bool: `rematVerweigert_fehler` (faulting
  form above its guard), `rematVerweigert_teuer` (non-cheap constant),
  `rematVerweigert_gewicht` (spill pair cheaper), `rematVerweigert_strtod`
  (host double rounding), `rematVerweigert_mxcsr` (cross-scope float).
- Value lemmas over arbitrary `Int`: `rematAdd_wert`, `rematSub_wert`,
  `rematMul_wert`, `rematNeg_wert`, `rematDiv_wert` (under the `M102`
  premises, forwarded unchanged); generic `rematLit_wert` for any
  expression whose literal shape the validator recomputed.
- `rematWort_add`: width-exact read-back through the canonical word.
- `rematGleit_behält`: admitted float recomputation preserves value and
  `gleitPasst` outcome (single `rundeBruch`, one scope).
- Cost: `rematFolge` (one `movImm64`) vs `spillFolge` (`store64` plus
  `load64`); `rematFolge_zaehlt`, `spillFolge_zaehlt`,
  `rematFolge_spart` (`1 ≤ 2` in `targetWork`, reused `CostSummary`
  vocabulary); `gewichtOk_gilt` and `rematZulassen_gewicht` carry the
  admitted weight bound into the connection.
- TARGET `OptRematConst_verbindung`: at an `Endblock.bind` window with
  arbitrary continuation, the recomputed `x + y` preserves the bound
  value, the `execEnd` outcome (same constructor/successors: contracts
  at their place, call logs, `orte = []` concurrency, step budget
  unchanged), the word image, and the spill-weight bound. No `ensures`
  derived, no fault speculated above its guard.
- Companion `OptRematConst_verbindung_zeuge`: all premises jointly
  inhabited on non-degenerate `refD` (`einzahlen` writes its table;
  reached run `MB` changes memory, slot `0 -> 100`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptRematConst.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (511 jobs).`
- Axioms: every theorem within `propext`, `Classical.choice`,
  `Quot.sound` (subset thereof); no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched.

## What remains open (see CUTS in the file)

No block-window float rewrite (value-level only); `div`/`rem`/`sub`/`neg`
values only, `Endblock` connection for `add`; no formal level-(c)
machine-work bound (OPEN per IR-VALIDIERUNG lane 278); no silicon/TSO-GX/
ABI correspondence beyond canonical words and `gleitRechne` values.

## Task feedback

Nothing in the task appears wrong. The accepted `OptFoldConst` structure
transferred directly; the distinguishing content is the spill-weight
certificate field with its realised `1 ≤ 2` target expansion and the
faulting-form refusal above the guard.
