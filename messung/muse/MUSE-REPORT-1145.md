# MUSE-REPORT-1145: TSO to W bridge — LOCK/RMW steps

## What was done

New file `grammatik/Grammatik/X86/TsoRmwBridge.lean` (+ one `import
Grammatik.X86.TsoRmwBridge` line at the end of `grammatik/Grammatik.lean`).
The producer lane `HwLockRmw` IS merged in this clone, so the bridge is
stated over the accepted coherent-machine plug (`adapterLockRmw`,
`hwLockSchrittEv`) plus the accepted connection vocabulary
(`LockXaddFetch`, `LockCmpxchgSuccess`, `CasRetryBound`,
`LockedInstructionExecution`, `LockedOps`). Nothing is redefined: the old
evaluator is lifted, never copied.

Content by section:

- §1 Plug + well-formedness: `tsoRmwAdapter` (defined as `adapterLockRmw`),
  `tsoRmwAdapter_wf` (via `adapterLockRmw_wf`).
- §2 Exact agreement, each as ONE single RMW event over the full word
  footprint with `RmwForm`, read-back and kept buffers:
  `tsoRmw_xadd_einzel_rmw` (via `hwLock_xadd_stimmt`),
  `tsoRmw_cmpxchg_erfolg_einzel_rmw` (via `hwLock_cmpxchg_ok_stimmt` +
  `CmpxchgErfolgForm`), `tsoRmw_cmpxchg_fehlschlag_rmw` (via
  `hwLock_cmpxchg_nein_stimmt`; the failure write-back pins
  `schreibbar8`).
- §3 RMW atomicity: `tsoRmw_kein_split` (via `cmpxchg_erfolg_kein_split`;
  no load-then-store pair observes what one locked access does),
  `tsoRmw_kette_ohne_verlust` (two chained admitted XADDs on one target:
  `ev2.gelesen = ev1.geschrieben`; the hardware-side shape behind
  `w_kein_verlust`). Every premise feeds one guard of the two accepted
  step equations.
- §4 Refusals through the plug: `tsoRmw_ud_bleibt_verweigert`,
  `tsoRmw_puffer_bleibt_verweigert`,
  `tsoRmw_unaligned_bleibt_verweigert`,
  `tsoRmw_mfence_ohne_sse2_verweigert` (all four via the matching
  `hwLock_*` lemmas), plus `tsoRmw_mfence_kein_rmw` (the fence admits as
  fence-only with `RmwForm [ev] = false`, via `hwLock_mfence_stimmt`).
- §5 Cost shape, no retry promise: `tsoRmw_kosten_gestalt` (fetch-add is
  one unit below every CAS retry count via `xadd_kosten_eins` /
  `xadd_guenstiger_als_cas`; CAS retry unbounded via
  `cas_schleife_unbeschraenkt`; unknown contention diverges via
  `retryBoundOf_unbekannt`). No bounded-retry, fairness, progress or
  cycle claim.
- §6 Joint witness on the accepted reached run (`hwLockWitStart`):
  event projections `tsoRmwWitEv1` / `tsoRmwWitEv2` with observers
  `tsoRmwEvRmw` / `tsoRmwEvGelesen` / `tsoRmwEvGeschrieben` /
  `tsoRmwEvForm`, closed `decide` pins `tsoRmwWit_ev1_rmw`,
  `tsoRmwWit_ev1_gelesen` (= 10), `tsoRmwWit_ev1_geschrieben` (= 15),
  `tsoRmwWit_ev2_gelesen` (= 15), `tsoRmwWit_ev2_geschrieben` (= 22),
  `tsoRmwWit_ev1_form`, and the joint `tsoRmw_bruecke_zeuge` (two cores,
  memory-changing 10→15→22 chain, buffered byte forwarded to its owner
  only, `HwWf`, both planted plug refusals beside the run).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (628 jobs)`. `./lean-probe` on the new file:
0 errors. All `#print axioms` are `[propext, Quot.sound]` (or `[propext]`
for `tsoRmw_kein_split`): standard-or-fewer, no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. No premise has type `Prop` itself; every premise
is consumed by its proof (each guard feeds exactly one accepted lemma).

Two `./lean-bau` attempts before the green one failed environmentally, not
on proof content: once `failed to create thread` (exit 134, machine under
parallel-lane load) and once `failed to read .../Bitblast.olean.private`
at the import line. A retry with no file change went fully green.

## What remains open (see CUTS in the file)

- No per-access target-to-W/GX simulation is claimed: the timestamp/value
  link from LOCK event words to W history messages (`wahl`/`neu`,
  `Frisch`, the lowering certificate's value link) stays OPEN with the
  source/table-write consumer lanes. The `rmw` field of a full `SchrittW`
  is supported (single atomic read-write pairing, no intervening buffered
  store) but not discharged here.
- No hardware correspondence beyond self-consistency; aligned whole-word
  atomicity stays a selected-profile contract (`ausgerichtet8` + empty own
  buffer).
- No fetched-byte dispatch on `HwMaschine` (plug takes parsed
  `LockAnweisung`); narrower widths, other addressing modes and split-lock
  detection stay open with 662/HwLockRmw.

## Task remarks

- The task's `HwLockRmw`-merged branch applied: the producer file exists in
  this clone, so the bridge reuses `adapterLockRmw`/`hwLockSchrittEv`
  directly instead of restating over the raw locked-step API.
- The MECHANISM paragraph asks to "define your family's event type"; the
  family event type (`LockAnweisung`, `LockEreignis`) already exists as
  accepted vocabulary, so defining another one would duplicate the model
  (rule 16). The plug reuses the accepted types unchanged; this is noted
  as a deliberate deviation in letter, not in intent.
- Rule 13 (`_zeuge` inhabitation) does not trigger mechanically (no premise
  quantifies over program syntax, no `ZEUGE:` target in the task), but the
  MECHANISM's `_zeuge` witness demand is met by `tsoRmw_bruecke_zeuge` on
  the reached non-degenerate two-core run.
