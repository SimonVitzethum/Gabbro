# MUSE-REPORT-838: Composition closing — atomic-ledger closing

## What was done

Created `grammatik/Grammatik/X86/ComposeAtomicLedger.lean` (new, ~410 lines)
and added its import to `grammatik/Grammatik.lean`. The module closes every
shared atomic access to its ledger entry (ordering, RMW field,
success/failure); unlogged shared access refuses. It composes ONLY
already-accepted modules and re-proves nothing:

- `LockedOps`: `lockSchritt`, `casSchritt`, `LockEreignis`, `lock_xadd_atomar`,
  `mfence_ordnung`, `cas_erfolg_schreibt`, `cas_fehlschlag_stottert`,
  `locked_add_zwei_kerne`, `cas_erfolg_zeuge`, `cas_fehlschlag_zeuge`,
  `mfence_ordnung_zeuge`.
- `WordAtomicity`: vocabulary context (guard shape; no new transition).
- `ReleaseAcquire`: `freigabe_braucht_flush`, `zaun_erwerb_liest_kanonisch`.
- `TSOHistory`: `hist_zeuge_gelenk` (reached run for the witness).
- `Speichermodell.Sicht`: `Ordnung` (`entspannt`/`freigabe`).

## New definitions/theorems (exact names)

- `AtomZugriff` (inductive: `lese`/`schreibe`/`xadd`/`cas`/`zaun`),
  `LedgerEintrag` (structure: `addr`/`ord`/`istRmw`/`erfolg`),
  `ledgerEintrag`, `ledgerCasOk`, `ledgerDeckt` (decided), `ledgerFindt`.
- Decided closings: `lese_schliesst`, `schreibe_schliesst`, `xadd_schliesst`,
  `cas_schliesst`, `zaun_schliesst`.
- Producer connections (each applies one accepted lemma, all premises used):
  `xadd_eintrag_aus_schritt`, `cas_erfolg_eintrag_aus_schritt`,
  `cas_fehlschlag_eintrag_aus_schritt`, `zaun_eintrag_aus_schritt`,
  `ordnung_eintrag_aus_schritt`.
- Refusals: `ohne_eintrag_verweigert` (empty ledger, all accesses),
  `falsche_ordnung_verweigert` (planted: relaxed entry vs acquire load),
  `kein_rmw_ohne_lock_verweigert` (planted: plain-store entry vs XADD),
  positive `xadd_eintrag_gefunden`.
- TARGET `ComposeAtomicLedger_verbindung`: six-way conjunction over
  arbitrary admitted inputs (XADD / CAS-success / CAS-failure / fence /
  release+acquire ordering / empty-ledger refusal).
- Companion `ComposeAtomicLedger_verbindung_zeuge`: reached run
  (`TSOErreichbar sbStart sbNach2` + `sb_flush_aendert_speicher`),
  two-core locked-add pair 0→12 (`locked_add_zwei_kerne`), installing and
  stuttering CAS, fence beside foreign pending store, release-invisible /
  fence-ready-acquire loads, empty-ledger refusal. Non-degenerate:
  real buffered stores, real RMW events, memory-changing steps.

## Last `./lean-bau` result

`Build completed successfully (509 jobs).` `./lean-probe` on the new file:
`== 0 error(s)`. Axioms of all new theorems are within
`[propext]` / `[propext, Quot.sound]` / none — standard, no new axiom,
no `sorry`/`admit`/`native_decide`/`unsafe`. Nothing outside the three
owned files was touched; no diagnostic/gift/example/CLI numbers, no
MARKE_EMIT, no source/checker/Spec/goal/emitter edits.

## What remains open (see CUTS in the file)

- No per-access W/GX refinement (bridge lanes 573/574, recorded OPEN there).
- No source-carrier admission link to `GeteiltV` (`AtomicPayload`): follow-up
  is the address map from ledger entries to admitted shared atomics.
- No fetch/decode linkage (consumers: lanes 776/778/779/784 paths).
- No tearing claim beyond the guarded LOCK word update; no hardware time,
  fairness or progress.

## Task assessment

Nothing in the task was found to be wrong. One elaboration note: `decide`
goals with free variables do not close by `rfl`, so the decided closings
use `unfold` + `simp` instead.
