# MUSE-REPORT-835: Work-transfer composition closing

## What was done

New file `grammatik/Grammatik/X86/ComposeWorkTransfer.lean` (owned) plus the
one-line import registration in `grammatik/Grammatik.lean` (owned). It closes
one named producer/consumer gap between declared source costs and actual
machine work through the separate transfer:

- PRODUCER: `DerivedWorkBound.deckung_fragment` (lane 654) derives the
  `Deckung` work coverage for the covered lowering fragment (`senkFrag` plus
  one slot store) from the generated instruction count. This is the `Deckung`
  leg that `BudgetExecution` (lane 572) leaves OPEN in its CUTS.
- CONSUMER: `BudgetExecution.budgetAusfuehrung_transfer` (lane 572) composes
  named per-form hardware costs (`laufKosten_schranke`, lane 434) with a
  `Deckung` into target-time coverage `t <= B * k`, without re-summing.
- SCHEMA (reused, never re-proved): `fragmentSummary`, `expandBound`,
  `targetWork` (CostSummary, lane 347); `zeitTransfer*` refusals
  (TimeTransfer, lane 547); `senkFrag`/`senkAssign`, `decodiertZu`,
  `Paket`/`paket_nicht_degeneriert`, `hCost_wit`, `hb_wit`,
  `witSenk628`, `witSenkAssign628` (lanes 599/628/654).

## Exact new definitions/theorems

- `ComposeWorkTransfer_verbindung` (TARGET): generic over arbitrary admitted
  inputs (any `abb`, `e`, registers, `disp`, profile `p`, `src >= 1`,
  aggregation `hCost`, per-step bound `hb`); composes the derived `Deckung`
  producer with the transfer consumer into
  `forall k, expandBound fragmentSummary src = some k -> t <= B * k`.
  Every premise is used. No internals re-proved.
- `ComposeWorkTransfer_geschlossen`: closed declared-cost corollary
  `t <= B * (src * 4)` via `fragmentSummary_expand` (uniform maximum 4,
  honest zero spill/fence). This is the declared-source-costs to
  machine-work closing step.
- `ComposeWorkTransfer_verweigert_knapp`: underestimated work bound below 2
  covers no composed assignment (reuses `arbeit_knapp_verweigert`).
- `ComposeWorkTransfer_verweigert_retry`: unbounded retry refuses summary AND
  transfer admission jointly (reuses `kein_freier_versuch_fragment`).
- `ComposeWorkTransfer_verweigert_ohneKosten`: unpriced head form admits no
  aggregation, hence no composed instance (reuses
  `zeitTransfer_verweigert_ohneKosten`).
- Joint witnesses on the non-degenerate `witD628` package (contract writes
  the table; source `execStmt` run moves slot `12 -> 42`; fetched-byte run
  observably changes memory -- reached memory-changing runs, not a
  conjunction of checks): `ComposeWorkTransfer_verbindung_zeuge`
  (TARGET companion, bound `7 <= 3 * k`),
  `ComposeWorkTransfer_geschlossen_zeuge` (`7 <= 3 * (1 * 4)`),
  `ComposeWorkTransfer_verweigert_knapp_zeuge` (bound 1 covers nothing).
  The two syntax-free refusals (`retry`, `ohneKosten`) need no `_zeuge`
  per rule 13 (no premise over program syntax).

## Build / axiom results

- `./lean-probe grammatik/Grammatik/X86/ComposeWorkTransfer.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (509 jobs)`, whole project green.
- Axioms: `verbindung`, `geschlossen`, `knapp` depend on
  `[propext, Quot.sound]`; `retry` on `[propext]`; `ohneKosten` on none;
  all three `_zeuge` on exactly `[propext, Classical.choice, Quot.sound]`
  (inherited from the reused witness infrastructure). Standard; no `sorry`,
  `admit`, `axiom`, `native_decide`, or `unsafe`.
- `gabbro_ziel` axioms: untouched by construction -- no existing file was
  modified except the one-line import append in `Grammatik.lean`; the goal
  statement, checker, emitter, Spec and friend-reserved optimiser files
  are untouched. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT
  changes.

## What remains open (explicit CUTS in the file)

- Scheduling (TSO/bridge lanes): which source step `src` counts when several
  lowered assignments share one budget (`kostenTiefF` multiplicities);
  interleavings and waiting delays untouched.
- All-source (lowering lanes 599/628): only literals, variables, one bounded
  add/sub over atoms, then one slot store; everything else refuses `none`.
- Timing fidelity (profile lane 434): `t` counts NAMED per-form bounds, never
  measured silicon latencies; `ret` stays refused.

## Plain assessment (where the result is thinner than the title)

The `forall k` form of `ComposeWorkTransfer_verbindung` coincides
propositionally with the conclusion of the already-accepted
`senkAssign_zeit_schranke` (lane 654), proved through the same two legs.
The new content of this lane is therefore the explicit named-interface
closure (572's OPEN `Deckung` leg plugged by 654's producer, stated and
checked in one place), the closed declared-cost bound `t <= B * (src * 4)`,
the three refusals propagated through the composed step, and the joint
non-degenerate witnesses. No full source-to-final-bytes validation and no
target-to-W/GX bridge is claimed; those remain OPEN as recorded.
