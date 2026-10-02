# MUSE-REPORT-590: Independent exact-candidate connection review of 572

CANDIDATE: 572 6afde44208b64fe56bcf636763a5f1808af478eb
VERDICT: ACCEPT

## Scope verified

- Clone `/home/simon/Dokumente/gabbro-muse/a590`, branch `muse/590`. Clean.
- Snapshot `.tmp/review/SNAPSHOT.json`: author 572, pinned HEAD
  `6afde44208b64fe56bcf636763a5f1808af478eb`, base `9ef0afe2`, 3 files, clean.
- Candidate diff vs base: exactly `MUSE-REPORT-572.md`,
  `grammatik/Grammatik.lean` (one appended import line for
  `Grammatik.X86.BudgetExecution`), `grammatik/Grammatik/X86/BudgetExecution.lean`
  (294 lines, new). No checker/Spec/goal/emitter edits, no friend
  optimiser edits, no other files.

## What was checked

1. **Real names, all resolved.** Every external reference in the candidate
   resolves to an existing accepted definition/theorem: `foreverLauf`,
   `rufAt`, `runOps`, `runOps_cons`, `runPass`, `fremdOp`,
   `runOps_fremd_exceeds`, `kostenTiefF`, `lauf`/`laufKosten`,
   `laufKosten_schranke`, `laufKosten_kopf_verweigert`,
   `laufKosten_schranke_zeuge_hbound`, `schrittKosten`, `targetWork`,
   `expandBound`, `expandBound_gilt`, `blattSummary`,
   `blattSummary_schranke`, `blattSummary_beschraenkt`,
   `kostenSummeOk_verweigert_unbegrenzt`, `zeitTransferZulaessig`,
   `zeitTransfer_kosten_benannt`, `beobAusgang`, `byteschritt`,
   `beobAusgang_weiter_ungleich`, `casKosten`,
   `cas_schleife_unbeschraenkt`, `profilZeuge`, `zeugeProg`,
   `zeugeZustand`, `zeuge_speicher_aendert_sich`,
   `ziel_ort_einfaden_zeuge`. No guessed ISA, no forged decoded input:
   the target fixtures (`zeugeProg`, `profilZeuge`, `blattSummary`) are
   the accepted ones reused untouched.
2. **No forbidden tactics.** `rg` over the pinned file: zero hits for
   `sorry`, `admit` (as tactic), `axiom`, `native_decide`, `unsafe`;
   the only substring hits are English words (`admitted`/`admission`)
   in comments. No `Prop`-typed premise; every premise of every theorem
   is used by its proof (checked per theorem, including the two `rfl`
   stop equations whose arguments all occur in the stated equation).
3. **Reproduced.** Copied the pinned file into this clone and ran
   `./lean-probe grammatik/Grammatik/X86/BudgetExecution.lean`:
   `== 0 error(s) in the COMPLETE output; exit 0`, with per-theorem
   axioms exactly as the author claims (all within
   `propext`/`Classical.choice`/`Quot.sound`; `stoppReihenfolge`
   axiom-free). Scratch copy removed afterwards; this branch contains
   only this report. Full-build evidence in
   `.tmp/review/author-572/BUILD-EVIDENCE.json` shows `./lean-bau`
   `Build completed successfully (428 jobs)` on the pinned HEAD.
4. **CUTS and `#print axioms` present** for every main theorem at file
   end, as required.

## New connection facts (why this is not decorative)

- `forever_erschoepft_benannt` / `rufAt_tiefe_erschoepft`: actual source
  stop equations (`foreverLauf` at 0 passes, `rufAt` at 0 depth). Trivial
  by `rfl`, but they name the real semantics rather than a toy model.
- `stoppReihenfolge`: genuinely new JOINT fact — over-budget head op
  names the source `budget` breach (via `runOps_cons`) AND refused head
  form refuses the whole target aggregation (via
  `laufKosten_kopf_verweigert`), each under its own name. This is the
  stopping-order connection the task asked for.
- `totalCost_anhang`, `kein_freier_versuch`, `stutter_ohne_schranke`,
  `optimierung_darf_nichts_verstecken`, `beobachtung_stopp_sichtbar`:
  real obstructions reusing accepted refusals; `stutter_ohne_schranke`
  (`exists n, K < casKosten n`) and `totalCost_anhang` are new
  inductions/computations, the rest are thin but honest compositions
  that keep each side under its own name.
- `budgetAusfuehrung_zeuge`: JOINT non-degenerate witness — table-writing
  `eP` (slot 5 vs 0, log entry, `ReqAmEintritt` via
  `ziel_ort_einfaden_zeuge`), reached memory-changing target run
  (register and memory byte 0 -> 42 via `zeuge_speicher_aendert_sich`),
  source within (`runPass = .ok 1`) AND source exhaustion (`runOps =
  .budget`) together, transfer bound over unit budget, real
  `kostenTiefF` plugging into the schema, plus planted refusals
  (unpriced `ret`, unbounded retry). Non-vacuous: `expandBound
  blattSummary 1 = some 5` with `7 <= 3 * 5` decided.
- Honest framing: `Deckung` is carried data (an explicit open interface,
  exactly what the task prescribes while `IR.lean` is absent), and the
  transfer core is structurally the `zeitTransfer` composition with the
  coverage hypothesis named. The report and CUTS label the producer leg
  (`valX86_sound`, per-access target-to-W/GX bridge, IR lowering),
  cost recomputation, and cycle bounds as OPEN, not closure.

## Accepted bounded claim

Source budget exhaustion (forever/depth/ops) and accepted finite target
runs are connected for executed prefixes covered by an admitted summary:
per-form hardware bound plus summary work coverage give `t <= B * k`;
stopping order is head-first and fail-closed on both sides; unbounded
retry/hidden-stutter/silent-stop are refused or broken by construction;
one jointly witnessed table-writing instance ties real store,
exhaustion, transfer, and refusals together.

## Minimal repairs

None required. One note for the integrator (not a repair): the transfer
core overlaps `zeitTransfer` by construction (same two-fact composition
with the work hypothesis named `Deckung`); keep both, since consumers
`budgetAusfuehrung_transfer`/`stoppReihenfolge`/`beobAusgang` document a
stable producer/consumer interface, and a future IR-lowering lane should
discharge `Deckung` for the `blattSummary`/`zeugeProg` pair rather than
re-prove the arithmetic.

## Next integration

Prove `Deckung` for a committed IR lowering of the witness pair (owner
287's interface), then replace the carried-data hypothesis at that use
site; the per-access target-to-W/GX bridge and generic `valX86_sound`
remain with the decoder/bridge lanes.
