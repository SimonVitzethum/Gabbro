# Muse Report 434: X86 HardwareAssumptions module

## Task
Create the new reusable module `grammatik/Grammatik/X86/HardwareAssumptions.lean`
plus one additive X86 import in the umbrella: generic selected-profile
hardware-assumption records and a derived conservative target step-cost
aggregation fact over actual finite runs with explicit bounds. No assumed
simulation, LOCK latency, progress, or ignored waiting.

## What was done
New module `Grammatik.X86.HardwareAssumptions` (353 lines), imported at the
end of the X86 block of `grammatik/Grammatik.lean`. It reuses the accepted
`Ausfuehrung` (`lauf`, `zeigeProg`, `zeigeZustand`,
`zeige_speicher_aendert_sich`) and `Gleitprofil` (`MXCSR`, `mxcsrGueltig`)
definitions; no IR/executor duplicated, no checker/Spec/Rust/emitter touched.

Definitions:
- `HardwareProfil`: `{ mxcsr : MXCSR, kosten : Befehl → Option Nat }`.
  `none` is unbounded/refused, never zero. Data and admission are separate
  so a refused profile stays statable.
- `profilGueltig : HardwareProfil → Bool` (`mxcsrGueltig` of the word).
- `schrittKosten`, `laufKosten`: per-step cost and conservative aggregation
  over finite decoded sequences; `none` propagates.
- `zeigeKosten`: witness table (1 per move/jump, 2 per ALU/push/pop,
  3 per load/store/call, `ret => none` — its cost depends on stack-memory
  traffic no constant named here covers). Named bounds, never measured
  latencies.
- `profilZeuge`: reset MXCSR `0x1F80` with the witness table.

Theorems (every premise used; conclusions are genuine sums/inequalities):
- `laufKosten_nil`, `laufKosten_cons` (`rfl` unfolding equation),
  `laufKosten_kopf_verweigert`, `laufKosten_rest_verweigert`,
  `laufKosten_kopf_erfolg`.
- `laufKosten_anhang_erfolg`: cost splits over `l1 ++ l2` (induction).
- `laufKosten_schranke`: explicit per-step bound `B` gives
  `t ≤ B * prog.length` on success (induction; uses the bound hypothesis
  for every head and the success hypothesis for every outcome).
- `profilZeuge_gueltig`, `profil_nicht_global` (admitted and refused
  profiles coexist as data; validity is per selected profile, no global
  silicon claim).
- Joint witnesses: `laufKosten_zeuge_erfolg` (cost 7 AND the real
  store-changing run via `zeige_speicher_aendert_sich`: rbx = 42, byte
  8192 observably 0 → 42), `laufKosten_zeuge_verweigert` (`ret` refused),
  plus one `_zeuge` instantiating ALL premises jointly for each generic
  lemma (`kopf_erfolg`, `kopf_verweigert`, `rest_verweigert`, `anhang`,
  `schranke` incl. the proved per-step bound `hbound`).

## Verification
- `./lean-probe grammatik/Grammatik/X86/HardwareAssumptions.lean`: 0 errors.
  Axioms are standard subsets only (none / `[propext]` /
  `[propext, Quot.sound]`); no `sorry`/`admit`/`axiom`/`native_decide`.
- `./lean-bau`: `Build completed successfully (393 jobs)` (one transient
  umbrella-link crash with `failed to create thread` under load; clean on
  retry, unrelated to this module).
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `gabbro_ziel` depends on axioms `[propext, Classical.choice, Quot.sound]`.

## Findings (believed-wrong / notable)
1. `simp only [laufKosten, ...]` on success-shape cons goals sends the
   worker into a recursive-equation loop ending in
   `failed to create thread` (exit 134), deterministically, while the same
   tactic on refusal-shape goals is fine. All cons proofs therefore rewrite
   with the `rfl` equation `laufKosten_cons`; `dsimp only` (no lemmas) is
   used for iota reduction. Recorded in the file's CUTS as a
   proof-engineering note. A future `simp`-based refactor of these proofs
   will re-hit this.
2. `simp only [defName]` does not unfold a plain def in this toolchain here
   (`Unknown identifier`); an `rfl`-equation + `rw` was used instead.
3. `Option.some_injective` does not exist in this toolchain (no mathlib);
   `Option.some_inj.mp` was used.
4. No `ZEUGE:` target statement was given in the task; the `_zeuge`
   theorems above cover every new theorem with premises as joint concrete
   instances over the non-degenerate store-changing `zeigeProg` run.

## Open / CUTS (see file)
No simulation/lowering, no LOCK latency, no progress/waiting claim; timing
separate from source budget stops, physical realization and OS obligations;
TSO granularity, narrow widths, sticky/NaN discipline, code immutability,
budget stops, observation channels, and fault-vs-refusal separation all
explicitly open. `ret` and any future form without a row stay refused.
