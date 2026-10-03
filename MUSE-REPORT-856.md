# MUSE-REPORT-856: Composition closing — virtual-address closing

## What was done

New file `grammatik/Grammatik/X86/ComposeVaCheck.lean` (~460 lines) plus the
one-line import in `grammatik/Grammatik.lean`. It closes one
producer/consumer interface: every virtual-address computation is reduced to
canonical form and mapped status **before** its access executes.

**Producer/consumer interface closed (all producers reused by name, nothing
re-proved, no second model/decoder/executor):**
- Producers: `AddressEncoding.adrEff` (+ pilot bridge `adrEff_basisForm`),
  `kanonisch48`, `fussZugelassen`; `AddressedHardwareExecution.adrPruefe`
  (+ `adrPruefe_gleich_fuss`, `adrPruefe_ordnung_kanonisch/umbruch`,
  `adrPruefe_schreib_frei/verweigert`), `adrLade`/`adrSpeichere` (+
  `adrLade_erfolg`, `adrSpeichere_erfolg`, `adrLade_basisForm_pilot`);
  `HardwareFaults.istKanonisch`, `adrKlasse` (+
  `adrKlasse_kanonisch_kein_fehler`); `ExceptionPriorityHardware.SeitenInfo`,
  `seitenKlasse` (+ both resolution lemmas).
- Consumer: the actual execution/footprint sites (`schritt`,
  `byteschritt`, `zugriff`), which discharge one data-access site through
  `ComposeVaCheck_verbindung` (store), `ComposeVaCheck_verbindung_lese`
  (load) and `ComposeVaCheck_pilot` (pilot-owned shape).

**New definitions/theorems (exact names):**
- `kanonisch48_istKanonisch`: the accepted canonical check and the accepted
  fault gate decide the same predicate (`rfl`).
- `vaKlasse`: the one ordered closing classifier — `adrPruefe` order
  (canonical, no-wrap, permission) mapped to architectural classes:
  noncanonical → `adrKlasse` (#SS/#GP); permission failure →
  `seitenKlasse pg` (#GP/#PF from the caller-stated present bit); wrap edge
  and success → `none` (validator refusal / no fault, never hardware).
- `vaKlasse_kein_fehler`, `vaKlasse_unkanonisch_daten`,
  `vaKlasse_unkanonisch_stapel`, `vaKlasse_umbruch_kein_fehler`,
  `vaKlasse_schreib_verweigert_seite`, `vaKlasse_lese_verweigert_seite`,
  `vaKlasse_seite_fehlt_pf`, `vaKlasse_seite_da_gp`.
- `ComposeVaCheck_verbindung` (TARGET, store): generic over arbitrary
  admitted inputs — canonical form + wrap-free footprint + write rights +
  real `write64` effect derive checked `adrSpeichere` execution, accepted
  `fussZugelassen` admission, absence of any fault class, and preserved
  permissions.
- `ComposeVaCheck_verbindung_lese` (load twin),
  `ComposeVaCheck_pilot` (pilot bridge to `effAddr`).
- Planted cases: `vaCheck_loch_daten_gp`, `vaCheck_loch_stapel_ss`
  (noncanonical hole → #GP/#SS for every memory/page state),
  `vaCheck_rand_kein_fehler` (wrap edge → ordered refusal, no fault),
  `dunkelVaSpeicher` + `dunkelVaSeite` with `vaCheck_dunkel_verweigert`
  (dark store → `.inr .keinSchreiben`) and `vaCheck_dunkel_pf` (#PF).
- `ComposeVaCheck_verbindung_zeuge` (required companion): all four premises
  jointly on `rsp + 0 = 8192` with `witVaNach` (42 stored at 8192), plus the
  composed `adrSpeichere` execution itself, the observably changed byte, the
  no-fault class, and the accepted mov/store/load reached run
  (`zeuge_speicher_aendert_sich`: byte 42 at 8192 from zero).
- `ComposeVaCheck_verbindung_lese_zeige`: same address after the witnessed
  store reads 42 back through the composed checked load
  (`read64_nach_write64`), with the applied closing beside it.
- `witVaNach`: witness successor memory (42 at 8192).

## Check results

- `./lean-probe grammatik/Grammatik/X86/ComposeVaCheck.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, no warnings.
  Axioms: everything depends only on `[propext]` or
  `[propext, Quot.sound]` (printed per theorem) — a subset of the
  `gabbro_ziel` standard, so the goal axioms are untouched.
- `./lean-bau`: `Build completed successfully (511 jobs).`
  (`✔ [510/511] Built Grammatik (116s)`), exit 0 — whole project green,
  no axiom deviation in the log.

## What remains open

Nothing remains open for this lane: the target theorem, its companion, the
load/pilot/refusal legs and the report are committed. Deliberately NOT
claimed (see file CUTS): hardware correspondence; paging-structure truth
(`SeitenInfo` stays caller-stated per the lane-738 interface); a fault class
for the wrap edge (`umbruch` → `none`); TSO/GX bridge; source/ABI/loader/
entry/budget/cost correspondence; full source-to-byte validation. Missing
producer legs are named with owners: arbitrary-input decoder length
soundness (lane 279), wider selected-form execution (integer666/locked662/
FP668 consumers).

## Notes on the task

- The inhabitation rule's "table some function writes" vocabulary is
  Gabbro-source-specific; the x86 analogue used here (as in prior accepted
  composition lanes) is a witnessed store that observably changes a memory
  byte plus a reached multi-step run that changes memory. Both companions
  satisfy this.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched. Only the three owned files changed
  (plus the workflow-required `arbeitsprotokoll/.commitmsg`).
- One belief worth recording: `kanonisch48` (AddressEncoding) and
  `istKanonisch` (HardwareFaults) are textually the same predicate in two
  modules; the `rfl` bridge makes that explicit, but a future cleanup could
  unify them at the source.
