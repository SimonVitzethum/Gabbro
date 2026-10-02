# MUSE-REPORT-650 — Growing TSO history to typed carrier W transition

## What was done

Delivered the lane's core ask: **at least one actual typed-carrier
`SchrittW` transition derived from canonical TSO trace accesses and
source G read/write semantics** — not only the `Lesbar` consequent —
plus the required explicit inherited history relation with genuinely
proved initial/step preservation, and a joint non-degenerate witness
with two timestamps, foreign activity and a stale-view refusal.

Owned files only: `grammatik/Grammatik/X86/CarrierTraceBridge.lean`
(renamed from the prior turn's `TSOCarrierStep.lean`; `Grammatik.lean`
import line updated to match), plus this report.

## Exact new definitions/theorems (`Gabbro.Grammatik.X86`)

- `ErbtW` — inherited history relation: W-message timestamps below
  `traceFrisch`, source view covered by `traceSicht`. Consumes only
  the append-only `TSOTrace596` projections, never the `histVon`
  snapshot.
- `erbtW_start`, `erbtW_schritt`, `erbtW_waechst` — initial, single-step
  (needs `SpurInv`), and finite-trace preservation, all proved.
- `assignSlot_spur` — a no-read `assignSlot` step prepends exactly the
  write event (`hOrte` kills the read events).
- `schrittW_aus_gruppen_drain` — the main transition: no-read fragment
  write + exclusion-checked grouped TSO drain installing the same word
  ⇒ actual `SchrittW` ∧ cross-side value agreement ∧ `RepSlot`.
  TSO side feeds value (`wort_gruppe_liest_zurueck`) and fresh stamp
  (`traceFrisch` + `ErbtW`); source side feeds the write
  (`rep_schritt_bleibt`) and the access enumeration
  (`blattFragment_voll`: vacuous reads, slot ownership). Grouped drains
  stay observationally grouped under `WortGruppe` + per-state
  `FremdFrei`, never hardware-atomic. The `rmw` field is discharged by
  refuting the exchange head.
- Witnesses: `ctV/ctF/ctFv`, `ctS2..ctS11` (8-flush drain at the slot
  address with one foreign issue inside), `ct_step1..9`,
  `ctBuf1_*`, `ctOff01_*`, `ct_ff2..11`, `ct_hgrp/hles/spur/hend/
  hempty/hstoer/hread`, `ct_stale0/ct_stale1` (core 0 reads canonical
  zero where core 1 forwards seven), `ctNA/ctNB`, `ct_stufe1`,
  `ct_erreichbar`, `ct_uhren` (clocks 1 ≠ 2), `ctProg/ctS/ctRest/
  ctRahmen/ctFaden/ctM` + `ct_hhead/hwelt/hΛ/ct_hWg`.
- `schrittW_aus_gruppen_drain_zeuge` — joint witness on `witD`:
  written table, memory-changing source step (`0 → 42`) and target
  drain, inherited history over the drain end, two distinct timestamps
  on a reached flush step, pending foreign byte outside the footprint,
  stale-view divergence, plus the `SchrittW`/value/`RepSlot`
  conclusions.

## Checks

- `./lean-probe grammatik/Grammatik/X86/CarrierTraceBridge.lean`:
  `== 0 error(s)`.
- `./lean-bau`: `Build completed successfully (458 jobs).`
- `#print axioms`: every theorem depends at most on
  `[propext, Classical.choice, Quot.sound]` (standard goal set).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Every theorem
  premise is used by its proof (one documented vacuity: the
  `ungelesen` field's non-read hypothesis is unneeded because the
  presented memory is G memory by construction).
- Rule-13 `_zeuge` present, joint and non-degenerate.

## What remains open (see CUTS)

Read carriers (literals only via `hOrte`), LOCK/RMW steps, per-access
run induction to W runs, the GX refinement consuming these facts,
scheduling/fairness/timing, interrupts/devices/MMIO/DMA.
`HavocA`/`GeteiltV` need no use here (plain table carrier, no shared
atomic). Byte-tearing at the grouped footprint is unobservable for
single-significant-byte values (here: 42) — a measured finding, not a
claim; multi-byte tearing stays at the byte layer.

## Notes on the task

- Nothing in the task statement turned out to be wrong. Two toolchain
  facts cost time: the `set` tactic is unavailable (used `generalize`
  for the successor abbreviation) and multi-line `{ }` structure
  notation does not parse (used positional `⟨⟩`, and `simp` rather
  than `simp only` for `if`-under-application goals).
- Next useful independent task: the read-carrier leg (forwarded group
  values need the lowering certificate's value link) or the GX-side
  consumer of `ErbtW` + `schrittW_aus_gruppen_drain`.
