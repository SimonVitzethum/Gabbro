# MUSE-REPORT-1287: Memory types WC, WT, WP and cache-control instructions

Lane 1287, clone `/home/simon/Dokumente/gabbro-muse/a1287`, branch `muse/1287`.
Follow-up of lane 1133 (`HwDevices.lean`), whose CUTS state NO WC/WT/WP
and no cache-control forms.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwMemTypesWC.lean` (~1290 lines,
namespace `HwMemWC1287`), plus one import line in
`grammatik/Grammatik.lean`. No other existing file touched. All work
reuses accepted definitions unchanged (`HardwareExecution`,
`MemoryTypeHardwareExecution`, `TSO`, `FenceDrain`,
`MfenceDrainOwn`, `SfenceStoreNarrow`, witness image/profile helpers);
nothing is copied or redefined.

- §0 Profile: `SpeicherTypWC` (wb/wt/wp/wc/uc), `TypProfil` as an
  explicit region list (PAT/MTRR combination reduced to a stated
  first-wins function, as 1133 does for UC), `decktTyp`,
  `speicherTyp` (WB default), lemmas `speicherTyp_leer/_kopf/
  _ueberspringe`. A first-wins `speicherTyp_mem` was stated, found
  FALSE during proof (an earlier covering region wins), and replaced
  by the correct skip lemma -- reported, not weakened around.
- §1 Ordering rules as the SDM states them: `typGepuffert`
  (WC only), `typDurchschreib` (WT/WP), table facts
  `wc_allein_gepuffert`, `wtwp_schreiben_durch`, `typPfad`.
  Named assumptions, never silicon proofs: `WcBusAnnahme` (pins
  present the drained log in order) with `wcPinsLaenge`;
  `WtWpBusAnnahme` (a retired WT/WP store is memory-visible) with
  `wtWpBus_liest`. WB rides the accepted TSO model, never restated.
- §2 Machine `HwWcMaschine1287` (coherent machine + profile +
  per-core WC second buffer + log), `WcEreignis1287` (acting core
  rides WC/CLFLUSH/fence events, as in `HwEreignis`; CLFLUSH carries
  its CPUID bit), `wcSpeicherSchreibe/wcLeere`, stated line size
  `clflushLinie` (64), `linienBasis/inLinie`, `wcLesbar` (own WC,
  then own WB forwarding, then memory), `decodePrefetch1287`
  (0F 18 memory forms; register forms and LOCK refuse) and
  `decodeClflush1287` (NP 0F AE /7 memory form; the SFENCE mod=3 row
  refuses), with pin/refusal theorems (`pin_prefetch_t0/_nta`,
  `pin_clflush`, `pin_clflush_kein_sfence`,
  `pin_prefetch_register_verweigert`, `pin_lock_praefix_verweigert`).
- §3 Six step functions (`wcStoreZugriff`, `wtStoreZugriff`,
  `wpStoreZugriff`, `clflushZugriff`, `prefetchZugriff`,
  `wcZaunZustand` reusing accepted `drainVoll`) plus the
  `HwWcSchritt` relation and `hwWcSchritt_wf` (`HwWf` preserved).
  Two fixes during proof: `cases ... with` alternatives must omit
  the leading index binder (1133 precedent), and per-core conclusions
  require the acting core to be an event index (events corrected).
- §4 Agreement: `hwWcStore_bypass`, `hwWtStore_durch`,
  `hwWpStore_durch`, `hwPrefetch_nop`, `hwWcZaun_wbLeer/_wcLeer/
  _fremdWb` (reusing `drain_voll_leer/_bereit`, `mfenceDrain_fremd`:
  no fence-everywhere), `hwWcZaun_fremdWc`.
- §5 `HwAdapter` plug: `WcZugriff1287`, `wcAdapterSchritt`,
  `adapterWc1287`, admit theorems (`wcAdapter_wc_ok`,
  `wcAdapter_wt_mem`, `wcAdapter_wp_mem`,
  `wcAdapter_prefetch_nop`), planted refusals
  (`wcAdapter_wc_falscherTyp/_nichtUc`, `wcAdapter_ohneSchreibrecht`
  covering wc/wt/wp), `adapterWc1287_wf`, exact plug agreement
  (`adapterWt/Wc_stimmt_ueberein`). CLFLUSH and the fence have no
  bare-machine plug (their effects need buffer state); documented,
  never silently admitted.
- §6 Line frame `hwClflush_rahmen`; explicit six-step witness run
  (`witW01287`..`witW61287`, `wit_schritt11287`..`wit_schritt61287`):
  WC store, store-ordered CLFLUSH line drain, second WC store, WT
  go-through, hint NOP at unreadable address 0, fence drain; decided
  facts (`wit_eigen1/fremd1/still1`, `wit_spuelung21287`,
  `wit_eigen3/fremd3`, `wit_durch41287`, `wit_null51287`,
  `wit_spuelung61287`) and profile facts (`witTyp_wc/wt/wp/wb1287`).
- §8 Connection `hwWc_verbindung1287` (20 premises, 14 conclusion
  groups: bypass pairs, two owner/foreign splits, line frame, two
  memory changes, kind refusal, go-through, NOP frame, fence frame,
  permission refusal, pins length, wf) with joint non-degenerate
  witness `hwWc_verbindung_zeuge1287` (all premises on the explicit
  run; memory changes twice on two cores; both named assumptions
  discharged with `rfl`/decided facts).
- CUTS block and `#print axioms` per main theorem: all within
  `[propext]` / `[propext, Quot.sound]` / none. No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` in the file.

## Last build result

`./lean-bau`: `Build completed successfully (659 jobs).`
`./lean-probe grammatik/Grammatik/X86/HwMemTypesWC.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.

## What remains open (see CUTS)

No CLFLUSHOPT/CLWB/non-temporal forms; WP invalidation traffic
beyond the shared memory effect; WT/WP share their memory equation
(no data cache modelled -- stated); UC-overlap stepping (1133);
memory-type aliasing reserved per SDM (WC-first read order stated);
cross-core WC same-line eviction order and WC read ordering OPEN;
no W/GX simulation; no source/checker/goal/emitter correspondence.

## Task feedback

Nothing in the task is wrong. Two readings worth recording: (1) the
task asks to "reuse `SfenceStoreNarrow.lean`" for the WC buffer
drain -- that file's CUTS explicitly leaves WC/NT stores OPEN, so
the reuse here is one-directional (its ordering vocabulary and
`MfenceDrainOwn`'s drain lemmas); the WC buffer and its fence drain
are new, proved against the accepted `drainVoll`. (2) "CLFLUSH ...
fault rules as for a byte read" was implemented as
readable-OR-executable-only, per the entry's stated execute-only
allowance, which is strictly more than a plain byte read.
