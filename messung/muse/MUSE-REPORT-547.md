# Muse Report 547: N17 TimeTransfer

Lane 547, branch `muse/547`, clone `/home/simon/Dokumente/gabbro-muse/a547`.
Owned files only: `grammatik/Grammatik/X86/TimeTransfer.lean`,
one additive import in `grammatik/Grammatik.lean`, this report.

## What was done

New module `Gabbro.Grammatik.X86.TimeTransfer` (~265 lines): a
target-work to source-time transfer skeleton over finite executed
target prefixes. Reuses the accepted modules only:

- `HardwareAssumptions`: `HardwareProfil`, `profilGueltig`,
  `schrittKosten`, `laufKosten` and the lemmas `laufKosten_schranke`,
  `laufKosten_kopf_verweigert`, `laufKosten_rest_verweigert`,
  `laufKosten_nil`, `profilZeuge`, `laufKosten_schranke_zeuge_hbound`.
- `CostSummary`: `CostSummary`, `kostenSummeOk`, `expandBound`,
  `targetWork`, the three `kostenSummeOk_verweigert_*` refusals,
  `blattSummary`, `blattSummary_ok`, `blattSummary_schranke`,
  `blattSummary_beschraenkt`, `blattKosten_drei`, `expandBound_gilt`.
- `Ausfuehrung`: `lauf`, `zeugeProg`, `zeugeZustand`,
  `zeuge_speicher_aendert_sich` (the same decoded list is executed,
  costed and work-counted -- that shared list is the instruction/site
  connection, not a new model).
- Source side: `KostenG.kostenTiefF` (real source bound in the
  witness); `src` is documented as the `ZeitAb` right-hand side
  `kostenTief P passes (n + 1) g` (Zielsatz/Spec.lean:1896) at the use
  site. `Budget` ops units appear via `blattKosten_drei` as a
  separation exhibit, never a conversion rate.

New definitions/theorems (exact names):

- `zeitTransferZulaessig` (admission Bool: summary AND profile) +
  `zeitTransferZulaessig_braucht_ok` (splits it).
- `zeitTransfer` (core): per-step hardware bound + summary work
  coverage over the source budget give `t <= B * k` for every summary
  bound `k` of `src`. Genuine composition of two independent bounds,
  not a renamed sum. All three premises used in the proof.
- `zeitTransfer_kosten_benannt`: successful aggregation names a cost
  for every prefix step (no hidden stutter).
- Refusals/obstructions: `zeitTransfer_verweigert_retry` (unbounded
  CAS retry behind a constant bound), `zeitTransfer_verweigert_ohneQuelle`
  (waiting exclusion without source correspondence),
  `zeitTransfer_verweigert_spin` (CAS-spin exclusion, unconditional),
  `zeitTransfer_verweigert_ohneKosten` (a refused head form admits no
  successful aggregation at all -- proved non-existence).
- `zeitTransfer_zeuge` (JOINT, non-degenerate): source fixture `eP`
  writes table `konto` with a reached run carrying slot 5 from 0,
  jointly with the admitted pair, the target prefix aggregating to 7
  AND executing to register/memory 42 from 0, the transfer instance
  `7 <= 3 * k`, the ops exhibit, and the real `kostenTiefF` bound
  plugging into the schema.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/TimeTransfer.lean`:
  `0 error(s)`; axioms are standard subsets
  (`zeitTransfer_zeuge`: exactly `propext, Classical.choice, Quot.sound`).
- `./lean-bau`: `Build completed successfully (416 jobs)`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no premise of
  type `Prop` itself; every premise used; no conclusion restates a
  premise; contracts untouched (no `forall rho`/`forall v`); no new
  semantics or mini-model; no edits outside the owned paths.

## What remains open (CUTS in the file)

Full source/target scheduling and IR correspondence (`XCorr`);
hardware cycle bounds (DEFERRED -- `t` counts named per-form bounds,
`ret` refused); no constant-time and no CAS-progress promise; real
lowering multiplicities tying `kostenTiefF` steps to target
instructions (phase B). The full compiler/bridge is NOT claimed
closed.

## Task fidelity note

No TARGET statement with a `ZEUGE:` line was given beyond the N17 row;
the row's TARGET (transfer skeleton with waiting exclusions needing
exact source correspondence), WITNESS+ (bounded admitted run) and
WITNESS- (exclusion without correspondence refused) are all delivered
above. Per-form maxima stay backend-declared and admission-checked, as
the row and FLOAT-ZEIT section 8 require.
