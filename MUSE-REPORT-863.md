# MUSE-REPORT-863: pure CSE rule (OptCsePure)

## What was done

New file `grammatik/Grammatik/X86/OptCsePure.lean` (owned) plus one import
line in `grammatik/Grammatik.lean` (owned). No other file touched: no
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files (`OptimizationRules.lean`, `OptimizationWitnesses.lean` untouched).

The optimisation is stated as a generic rule lemma over arbitrary values
(`x y : Int`) with validator-decided side conditions, following the
DESIGN section 7 row for pure CSE: identical width/mode under recomputed
availability; cross-gate range CSE refuses.

Certificate shape (exact): the LOCAL rewrite half is the `CseCert`
record — `gleicheBreite`, `gleicherModus`, `rein`, `verfuegbar`,
`keinTorBereich` (five Bools) checked by the admission Bool
`cseZulassen` (conjunction). The RECOMPUTED analysis half is cited by
premises: `hC : cseZulassen cert = true` (validator recomputed
avail/width/mode) and `hEq : cseZulassen cert = true -> bruch qf =
gleitRechne op (bruch qa) (bruch qb)` (kernel recomputation obligation,
conditional on admission).

Precise refusal case where the rule must NOT fire: reuse across a
gate/range boundary — `keinTorBereich = false` forces
`cseZulassen = false` (`cseVerweigert_tor`). Width/mode mismatch,
impurity (faulting above guard, gated, shared) and killed availability
refuse likewise. A refused optional optimisation falls back to another
certified translation, never to a warning. Nothing derives `ensures`;
no faulting form is speculated above its guard.

## Exact names of new definitions/theorems

- `CseCert` (structure), `cseZulassen` (def)
- `cseVerweigert_tor`, `cseVerweigert_breite`, `cseVerweigert_modus`,
  `cseVerweigert_rein`, `cseVerweigert_verfuegbar`
- `probe_cseZulassen_ok`, `probe_cseZulassen_tor`,
  `probe_cseZulassen_rein`
- `cseZulassen_seiten` (admission unpacks to all five side conditions)
- `cseAdd_wert`, `cseWort_add`, `probe_cseWort`
- `cseGleit_behält`, `probe_cseGleit` (IEEE: value + `gleitPasst`
  outcome under one kernel rounding scope)
- `OptCsePure_verbindung` (ZEUGE target: value preservation,
  `execEnd` outcome equality over a two-bind window with arbitrary
  continuation — covers contracts at their place, call logs,
  concurrency `orte = []`, unchanged step-budget accounting — plus
  width-exact word image and unpacked side conditions)
- `OptCsePure_verbindung_zeuge` (joint companion: `3 + 4` computed once
  and reused on non-degenerate `refD` beside reached memory-changing run
  `MB`, with `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`)

## Last `./lean-bau` result line

`Build completed successfully (511 jobs).` — `== exit 0; 0 error
line(s) in the COMPLETE output`. `./lean-probe` on the new file: 0
errors. Axiom prints: refusals/probes `propext` or none; `cseAdd_wert`,
`cseWort_add` add `Quot.sound`; `OptCsePure_verbindung` and its witness
exactly `propext, Classical.choice, Quot.sound` (the `gabbro_ziel`
standard). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every
premise is used by its proof.

## What remains open (see CUTS in the file)

No block-window float rewrite; no `sub`/`mul`/`div`/`rem`/`neg` syntax
connection (values share the `add` kernel); no cross-`bind` variable
threading (second site re-evaluates the pure expression at value
level); no formal level-(c) machine-work bound (OPEN per
IR-VALIDIERUNG); no silicon/TSO-GX/ABI correspondence (stops at
canonical words and `gleitRechne` values).

## Anything in the task believed wrong

Nothing. The task's ZEUGE names match the delivered theorems; the
"recomputed avail" premise is honoured by making the float/value
equations conditional on admission (`hEq` takes `hz`) and by unpacking
admission in the connection's fourth conjunct, rather than by
re-stating availability as an uncheckable Prop. One elaboration note:
the two-bind `execEnd` equality holds definitionally (`rfl`), exactly
as the single-bind fold connection in lane 860 — the reuse is pure, so
no world threading distinguishes the sides.
