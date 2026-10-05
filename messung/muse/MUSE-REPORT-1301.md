# MUSE-REPORT-1301.md

Lane 1301: WC ordering — cross-core eviction order and CLFLUSHOPT/CLWB.

## What was done

New file `grammatik/Grammatik/X86/HwWcOrdering.lean` (~1390 lines),
plus the one import line in `grammatik/Grammatik.lean` (committed with
the skeleton). Follow-up of lane 1287: closes its OPEN items
cross-core WC same-line eviction order, WC read ordering, and
CLFLUSHOPT/CLWB as a model over the LIFTED accepted 1287 machine
(`HwWcMaschine1287`), never copied or redefined.

- Lifted machine `HwWcOrdMaschine1301` (accepted 1287 machine plus an
  ordering-side log) with six step functions and the
  `HwWcOrdSchritt1301` relation. WC-store and fence cases reuse the
  accepted 1287 functions by reference; eviction drains the oldest
  pending entry of the acting core; the WC read is admitted exactly at
  the accepted `wcLesbar` value; CLFLUSHOPT/CLWB drain the acting
  core's line through the accepted `wcLinieSpuele`.
- Preservation: `hwWcOrdSchritt_wf1301` (`HwWf` survives every step).
- Agreement: `hwWcOrdStore_bypass1301` (lifted),
  `hwWcOrdLesen_nach_speichern1301` (same-core WC read after WC store,
  via `neuestens_angehaengt`), `hwWcOrdLesen_rahmen1301`,
  `hwWcOrdEvict_rahmen1301`, `hwWcOrdZaun_leer1301`,
  `hwWcOrdFlushopt_rahmen1301`, `hwWcOrdClwb_rahmen1301`.
- Refusals: `hwWcOrdEvict_leer_verweigert1301` (empty buffer),
  `hwWcOrdFlush_ohneBit1301` (no CPUID bit), `hwWcOrdFlush_ohneRecht1301`
  (no permission), `hwWcOrdStore_falscherTyp1301` (non-WC address).
- Decoders `decodeClflushopt1301` (`66 0F AE /7` memory form),
  `decodeClwb1301` (`66 0F AE /6` memory form) with pins
  (`pin_clflushopt1301`, `pin_clwb1301`, `pin_opt_nicht_wb1301`,
  `pin_flush_register_verweigert1301`,
  `pin_clflush_kein_opt_wb1301`, `pin_flush_lock_verweigert1301`).
- Named assumptions (ordering chapter not in clone, all silicon
  correspondence named): `WcEvictOrdAnnahme1301` (pins carry every
  retired drain; order NOT claimed — SDM states buffers may appear
  out of order on the bus), `ClflushoptZaunAnnahme1301` (pins honor
  the fence-separated log order), `ClwbKeepAnnahme1301` (retired CLWB
  byte reads back), with `wcEvictPinsLaenge1301`,
  `clflushoptZaunPinsLaenge1301`, `clwbKeep_liest1301`, and the proved
  program-order fact `clflushoptVorZaun1301`.
- Adapter plug `adapterWcOrd1301` (`WcOrdZugriff1301`,
  `wcOrdAdapterSchritt1301`) with `adapterWcOrd1301_wf`,
  `wcOrdAdapter_evict_mem1301`, `wcOrdAdapter_liest_ok1301`,
  `wcOrdAdapter_evict_falscherTyp1301`,
  `wcOrdAdapter_ohneRecht1301`, and exact agreement
  `adapterEvict_stimmt_ueberein1301`. CLFLUSHOPT/CLWB have no
  bare-machine plug (need buffer state), documented.
- Witness `witM0_1301`–`witM6_1301` with steps
  `wit_schritt1_1301`–`wit_schritt6_1301` and observations
  (`wit_eigen1_1301`, `wit_fremd1_1301`, `wit_still1_1301`,
  `wit_zaun2_1301`, `wit_flush3_1301`, `wit_keep4_1301`,
  `wit_eigen5_1301`, `wit_fremd5_1301`, `wit_null5_1301`,
  `wit_spuel6_1301`, `wit_leer0_1301`, `wit_nord0_1301`,
  `wit_noex0_1301`, `witM0_wf1301`): two cores, WC store drained by
  SFENCE/MFENCE, CLFLUSHOPT ordered after the fence, CLWB keeping the
  byte, second store drained by spontaneous eviction; memory changes
  twice, owner-only forwarding both times.
- Connection `hwWcOrd_verbindung1301` (all premises used) with joint
  companion `hwWcOrd_verbindung1301_zeuge` discharging all 23
  premises on the reached run.
- CUTS block and `#print axioms` for every theorem: only `propext`
  (and `Quot.sound` where the reused 1287 fence lemmas carry it);
  no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Silicon provenance (checked against
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
CLFLUSHOPT `NFx 66 0F AE /7`, CLWB `66 0F AE /6`, both ordered wrt
fences/locked RMW/older writes to the line and unordered against
other flushes and younger writes, byte-load faults with execute-only
allowed, #UD without the CPUID bit; WC buffer separate from
caches/store buffer, not snooped, implementation-dependent eviction,
weakly ordered.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwWcOrdering.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (677 jobs).`
  (last result line: `✔ [676/677] Built Grammatik (1.7s)` then
  `Build completed successfully (677 jobs).`)

## What remains open

- Cross-core WC same-line eviction ORDER beyond the named count
  assumption (intentionally not claimed: the SDM allows bus
  reordering); WC read ordering beyond same-core forwarding;
  non-temporal stores, PREFETCHW, CLDEMOTE (see CUTS).
- No per-access target-to-W/GX simulation and no source/checker/
  Spec/goal/emitter correspondence (not attempted).

## Fix after integration-gate refusal (whitespace only)

The merge gate refused the candidate on `git diff --cached --check`:
one trailing space in `HwWcOrdering.lean` (line 1043, in
`wit_schritt6_1301`). Fixed whitespace-only, no theorem touched.
`git diff --check` clean, `./lean-bau` green again (677 jobs).

## Task notes

Nothing in the task looks wrong. One reading decision worth
recording: "a CLFLUSHOPT ordered by it [the SFENCE]" is modelled as
fence-then-flush program order (log equation `zaun` before
`clflushopt`, lifted to the pins by the named assumption), i.e. the
flush retires into a post-fence state; the SDM's converse direction
(SFENCE after CLFLUSHOPT ordering older writes) is stated in the
assumption text but the run demonstrates the task's order.
