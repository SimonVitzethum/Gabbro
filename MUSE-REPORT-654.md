# MUSE-REPORT-654: Derived target work bound for direct source lowering

Lane 654, clone `/home/simon/Dokumente/gabbro-muse/a654`, branch `muse/654`.
Owned files only: `grammatik/Grammatik/X86/DerivedWorkBound.lean` (new),
`grammatik/Grammatik.lean` (one appended import), this report.

## What was done

Closed the missing `Deckung` producer of `BudgetExecution` for the covered
source fragment. Machine instruction count/work and the admitted cost
summary are DERIVED from the actual generated expression/assignment code
(`ExpressionLowering.senkFrag`, `SourceAssignmentLowering.senkAssign`);
no `Deckung`/`hWork` premise is assumed anywhere and no second cost
interpreter is invented (the one `targetWork`, the one `laufKosten`, the
one `senkFrag`/`senkAssign`, actual `execStmt`/`lauf`/`laufBytes` reused).

New definitions (`Gabbro.Grammatik.X86`):
- `decodiertZu` — canonical decoding of generated code (same map the
  lowering correctness theorems run through `lauf`).
- `fragmentSummary` — admitted summary derived from the formula: uniform
  maximum 4 (longest generated assignment), zero spill/fence, proved
  retry bound `some 0`, no exclusions.
- `Paket` — shared non-degenerate witness package Prop.

Main generic theorems:
- `senkAtom_laenge`, `senkFrag_laenge` (1 or 3), `senkAssign_laenge`
  (2 or 4) — generated-work formula, via `istAtom_von_senkAtom` /
  `istFrag_von_senkFrag` classification; `decodiertZu_befehl`,
  `arbeit_decodiert` (`targetWork` over decoded code = instruction count).
- `fragmentSummary_ok/max/expand` — admission, maximum, expansion
  `expandBound fragmentSummary src = some (src * 4)`.
- `deckung_fragment` — THE PRODUCER: `Deckung` derived from the fragment
  admission equation + length bound, never a premise.
- `senkAssign_zeit_schranke` — MAIN: named per-form hardware timing
  composed with the derived bound (via `budgetAusfuehrung_transfer`).
- `einheiten_getrennt` — unit pinning: `src` feeds the expansion,
  `targetWork` counts the decoded generated list, fragment length 1 or 3.
- `arbeit_nach_faltung` — the one applicable optimiser connection:
  `InvariantenOpt.foldAddLit` keeps the value (`eval_foldAddLit`) but
  shrinks work 3 -> 1, so costs must be recomputed, never inherited.
- `arbeit_ohne_versteck` — transfer success prices every generated step
  (no hidden stutter) and meets the derived bound.
- Refusals: `arbeit_knapp_verweigert` (bound below 2 covers nothing),
  `keine_arbeit_ohne_fragment` (`2 * 3` lowers to nothing),
  `kein_freier_versuch_fragment` (retry bound removed refuses admission
  AND transfer).
- Witnesses: `hb_wit` (per-step bound on the witness code),
  `hCost_wit` (aggregation `some 7`), `witQuelle_aendert` (source slot
  `12 -> 42` through actual `execStmt`), `paket_nicht_degeneriert`, one
  `_zeuge` per syntax-premise theorem (`senkAtom/Frag/Assign_laenge`,
  `deckung_fragment`, `senkAssign_zeit_schranke`, `einheiten_getrennt`,
  `arbeit_nach_faltung`, `arbeit_ohne_versteck`,
  `arbeit_knapp_verweigert`, `keine_arbeit_ohne_fragment`,
  `kein_freier_versuch_fragment`) plus `stopp_bleibt_laut_zeuge`
  (`forever`/`rufAt` loud for all continuations, over-budget foreign
  edge vs refused `ret` stop-order fact, joint with the package).

## Checks

- `./lean-probe grammatik/Grammatik/X86/DerivedWorkBound.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau` last result line: `Build completed successfully (458 jobs).`
- `#print axioms`: every theorem depends only on `propext`,
  `Classical.choice`, `Quot.sound` (subset thereof) — within the goal's
  axiom budget; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- Every premise of every theorem is used by its proof (checked by hand
  per theorem; `deckung_fragment` uses `hsenk` for the length bound and
  `hsrc` for the scaling; the main theorem uses all four premises).

## What remains open (also in CUTS)

- Scheduling: one generated assignment per `src` unit; `kostenTiefF`
  multiplicities over several assignments, interleavings and waiting
  delays are untouched (TSO/bridge lanes).
- All-source: only lit/var/one add-sub over atoms + one slot store;
  everything else refuses with `none` and carries no work bound.
- Timing-model fidelity: `t` counts named per-form bounds, never silicon;
  `ret` refused; no constant-time, CAS-progress, fairness or stutter claim.
- Next useful independent task: a `Deckung` producer for the next covered
  fragment (e.g. narrowed/compared branches or multi-assignment blocks),
  reusing `senkFrag_laenge`/`arbeit_decodiert` and extending
  `fragmentSummary` with a recomputed maximum.

## Task feedback

Nothing in the task is wrong. Two frictions worth recording: (1) the lane
file first named no owned file explicitly; the `.tmp/LANE.md` re-read
fixed this (`DerivedWorkBound.lean` + import + report). (2)
`InvariantenOpt.foldAddLit` lives one namespace deeper
(`...X86.InvariantenOpt`), and `Expr.lit` needs `(D :=)/(Γ :=)/(Λ :=)`
annotations outside the lowering modules — both resolved by reading the
actual definitions first, as instructed.
