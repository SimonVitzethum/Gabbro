# MUSE-REPORT-596: TSO history preservation across actual finite traces

## Task

Connect canonical TSO issue/flush traces to an actual append-only history
projection with increasing fresh timestamps and writer views, using real
`Sicht` primitives. Reuse `TSOZustand`/`TSOSchritt`; no new TSO executor,
no new source semantics. Prove generic one-flush and finite-trace
extension preserving previous messages, memory latest value, FIFO
issuance and reachable history. Address own-buffer forwarded loads and
release views. Joint two-core trace over actual bytes with non-degenerate
timestamps. Stable consumer API for BridgeRead/Write; `histVon` preserved
as bounded legacy evidence.

## What was done

New file `grammatik/Grammatik/X86/TSOTrace.lean` (accepted, full
`./lean-bau` green: exit 0, 440 jobs), plus the umbrella import in
`grammatik/Grammatik.lean`. `TSOHistory.lean` untouched.

**Vocabulary.** `SpurKnoten` (TSO state + grown history + per-core views
+ next fresh clock), `spurStart` (only `⟨0,0,null⟩`, empty views, clock 1),
`SpurSchritt` (issue keeps history/views/clock; flush of the actual oldest
entry `e` appends `nachricht .freigabe (blick c) e.addr frisch e.wert` and
advances the clock — the value comes from the buffer entry, never from a
desired conclusion), `SpurErreichbar`.

**Theorems.**
- `SpurInv` + `spurStart_inv` + `spurSchritt_inv`: every history/view
  timestamp stays below the clock; never reset.
- `spur_schritt_hist`: one step keeps history pointwise or appends exactly
  one release message at the old clock with the flushed value.
- `spur_schritt_erhaelt`: one step never drops a message.
- `spurStart_legt_snapshot_vor`: every start-node message is in `histVon`
  (legacy link; `histVon` unchanged).
- `spur_flush_frisch_vor`: the clock is `Frisch` before every flush.
- `spur_freigabe_sicht`: the release message carries the writer view
  (`setze`), stamped with the flush clock.
- `spur_weiterleitung_ist_jüngste`: forwarded loads return the youngest
  own-buffer value with the buffer split (reuses `TSOHistory`, all premises
  kept).
- `spur_flush_schreibt`: flush writes the oldest byte to canonical memory,
  its message is in the grown history, old messages preserved.
- `spur_ein_flush`: generic one-flush extension (issue case or flush case
  with freshness + readability at the joined view + memory + invariant +
  preservation).
- `spur_verlauf_waechst`: finite-trace induction — invariant, monotone
  clock, start-history subset.
- `spur_fifo_aelteste`: two issues from empty buffer + flush deliver the
  older value to memory and history (buffer shape pins the flushed entry).
- Witness `spurW0..spurW4` (two cross-core issues, both flushes),
  `spurW_erreichbar`, `spurW_histX/Y` (histories `[init, msg@1]` /
  `[init, msg@2]`), `spurW_uhren` (clocks 1, 2), `spurW_speicher` (both
  bytes change, `decide`), `spurW_laden` (both cores read back `1`),
  `spurW_lesbarX/Y`, and `spur_zeuge_gelenk`: reached, two-core,
  memory-changing at two addresses, both messages readable at actual
  values, timestamps distinct.
- Consumer API: `traceHist`, `traceSicht`, `traceFrisch` + the stable lemma
  set named in CUTS.

**Checks.** `./lean-probe` 0 errors after every increment; `./lean-bau`
exit 0, 0 error lines, 440 jobs. `#print axioms` for all 28 theorems:
only `propext` (and `Quot.sound` where `Sicht.setze` unfolding meets
`omega` transport) — standard subset, no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. No premise is `Prop`-typed; every premise is
used (checked by construction: freshness uses both invariant halves,
FIFO uses all eight premises, Lesbar uses membership + view equations).

## What remains open (CUTS in file)

Byte layer only: no typed-carrier W/GX mapping, no multi-byte atomicity,
no LOCK RMW, no `SchrittW` construction or run induction to W runs —
consumers BridgeWrite573/BridgeRead574 own that. Clock discipline is
projection-local. Unflushed forwarded values have no message (snapshot half
is the proved `fremd_weiterleitung_unsichtbar`; grown histories carry only
flushed values by construction). No fairness/timing/device model.

## Notes on the task (all points addressed, none weakened)

- "Do not reset timestamps": clock only advances (`+1` on flush, equal on
  issue); `spur_verlauf_waechst` proves monotonicity.
- "No smuggled simulation": the flush equation is keyed to the actual
  oldest entry `e` (`he : puffer c = e :: rest`); FIFO pins `e = ⟨a,v⟩`
  from the issue history.
- "Forwarded loads and release views": `spur_weiterleitung_ist_jüngste`
  (youngest-split) + `spur_freigabe_sicht` (writer view in message). No
  obstruction found: both closed as proved facts, so no `blocked` label.
- Per-byte facts are not claimed above byte granularity (CUTS).

## Producer/consumer interfaces and next tasks

- Produces for 573/574: `traceHist/traceSicht/traceFrisch`,
  `spur_ein_flush`, `spur_verlauf_waechst`, `spur_fifo_aelteste`,
  `spur_freigabe_sicht`, `spur_weiterleitung_ist_jüngste`.
- Consumes (unchanged): `TSO.issueByte/loadByte/flushKern`,
  `neuestens_*`, `flush_schreibt_kopf`, `issue_haengt_an`, `sb*` witnesses,
  `Sicht.nachricht/Lesbar/Frisch/setze_selbst/setze_anders`.
- Useful next independent tasks: (a) BridgeWrite573: per-access W store
  bridge from `spur_fifo_aelteste` + `spur_freigabe_sicht`; (b)
  BridgeRead574: read bridge from `spur_weiterleitung_ist_jüngste` +
  `spurW_lesbarX/Y`; both need accepted 567/570 interfaces, not this
  module's internals.
