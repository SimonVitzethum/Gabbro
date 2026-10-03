# MUSE-REPORT-894: Optimiser rule — call-argument selection rule

## What was done

New file `grammatik/Grammatik/X86/OptCallArgSel.lean` (+ import line in
`grammatik/Grammatik.lean`), built in small pieces through `./lean-probe`,
skeleton committed first, then one section at a time.

The rule (DESIGN §7 layout/allocation row + §2 "call arguments use the ABI
registers before stack slots"): the lowering places the first `regBudget`
(6) arguments in ABI registers and the rest in 8-byte stack slots, under
the per-image calling convention the validator re-decided from the image.

- **§1 Refusal:** `CallArgCert` (four decided Bools) + `callArgZulassen`
  admission; four refusal theorems prove each unchecked side condition
  (convention, budget, hidden/variadic, stack alignment) forces `false`.
  Three `decide` probes (admit / convention-refused / hidden-refused).
- **§2 Placement over arbitrary values:** `ArgPlatz` (`reg`/`stapel`),
  `platzFuer`, `platziereAux`/`platziere`, `liesWerte`. Proved:
  `platziere_liest` (placed values read back whole, any type),
  `platziere_laenge` (one location per argument, budget unchanged),
  `platzFuer_reg`/`platzFuer_stapel` (regs before stack),
  `platzFuer_buendig` (stack slots 8-aligned). Four `decide` probes
  (args 0/5 in regs, args 6/7 on stack at offsets 0/8).
- **§3 IEEE / arity gate / no new fault:** `gleitPasst_erhalt` (IEEE
  outcome is a pure function of preserved values; floats cross
  unconverted), `platzOk` + `platzOk_von_zulassen` (admitted cert +
  in-budget arity), `keinFehlerNeu` (admitted placement stays in budget,
  so no new `hardware` stop), `platzWort` (width-exact word round-trip).
- **§4 TARGET `OptCallArgSel_verbindung`:** admitted selection preserves
  values, cost, arity AND the `execStmt` `.call` outcome under equal
  `orte`/`evalArgs` (evaluated at every world, since `execStmt` evaluates
  in the post-read world) — so contracts at their place, call logs,
  concurrency and budget observations agree downstream. No `ensures`
  derived, no refusal weakened, no fault speculated above its guard.
- **§5 `OptCallArgSel_verbindung_zeuge`:** all premises jointly
  instantiated at the `lies`-call of `refD` (admitted cert, `[3, 4]`)
  beside the reached run `MB` with `refEin_schreibt`, `refB_erreicht`,
  `refB_schreibt` (slot `0 -> 100`, non-degenerate).

Exact new definition/theorem names: `CallArgCert`, `callArgZulassen`,
`ArgPlatz`, `regBudget`, `maxArgs`, `callArgVerweigert_konvention`,
`callArgVerweigert_budget`, `callArgVerweigert_versteckt`,
`callArgVerweigert_stapel`, `probe_callArgZulassen_ok`,
`probe_callArgZulassen_konv`, `probe_callArgZulassen_versteckt`,
`platzFuer`, `platziereAux`, `platziere`, `liesWerte`, `platziere_liest`,
`platziere_laenge`, `platzFuer_reg`, `platzFuer_stapel`,
`platzFuer_buendig`, `probe_platz0/5/6/7`, `gleitPasst_erhalt`,
`probe_gleitPlatz`, `platzOk`, `platzOk_von_zulassen`, `keinFehlerNeu`,
`platzWort`, `probe_platzWort`, `OptCallArgSel_verbindung`,
`OptCallArgSel_verbindung_zeuge`.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully
(511 jobs)`. `./lean-probe` on the file: `0 error(s)`. Axioms: at most
`[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. No new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved files touched.

## What remains open (see CUTS block in the file)

Byte correspondence through decoded final machine bytes, counted
per-class cost maxima, per-site spill/fence accounting, TSO/GX bridge —
all with the decoder/bridge/cost lanes, never invented here.

## Task feedback

The DESIGN §7 table has no explicit call-argument-selection row (only the
§2 line and the layout/allocation "address-taken spill via call arg"
failure case); I treated the lane task text as the authoritative row
premises. If the coordinator adds an explicit §7 row, the cert fields
map 1:1 onto it.
