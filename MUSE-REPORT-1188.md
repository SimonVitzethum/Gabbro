# MUSE-REPORT-1188: Exact review of candidate 1187 (TSO traces to W runs: run induction)

## VERDICT: ACCEPT

Candidate: lane 1187, pinned HEAD `cb3384a9f97274563029b29fb8d74f9d94263c6d`
(base `4f906f555d739de5b9444364735eae29b6445ed6`, reviewed from the in-clone
snapshot `.tmp/review/author-1187`: `PATCH.diff`, `OWNER-TASK.md`,
`MUSE-REPORT-1187.md`, `BUILD-EVIDENCE.json`). Files in candidate:
`MUSE-REPORT-1187.md`, `grammatik/Grammatik.lean` (one appended import line),
`grammatik/Grammatik/X86/TsoRunInduction.lean` (new, 265 lines).

## Checks (all pass)

- **No sorry/admit/axiom/native_decide/unsafe.** Grep over the candidate
  `grammatik/` snapshot finds none; the only `axiom` matches are the required
  `#print axioms` lines. No `def` redefines an accepted evaluator.
- **`#print axioms` standard.** Recorded candidate output: `FragArt`,
  `fragArt_abgedeckt_oder_drain`, `lauf_stale_kein_globaler_wert` depend on no
  axioms; `drain_erhaelt_erbt` on `[propext, Quot.sound]`;
  `lauf_global_verweigert` on `[propext]`; all other nine definitions/theorems
  on exactly `[propext, Classical.choice, Quot.sound]`.
- **Existing files untouched except one import line.** `PATCH.diff` shows the
  `Grammatik.lean` hunk appends exactly `import Grammatik.X86.TsoRunInduction`
  after `PipelineFloat`; no other existing file is touched.
- **Every premise used.** Checked theorem by theorem: `brueckenLauf_erreichbar`
  inducts on `h` and uses each `s.lauf`; `brueckenSchritt_satz` uses `s.art`
  and `s.abgedeckt` (drain case); `brueckenSchritt_kein_drain` projects
  `s.abgedeckt`; `brueckenLauf_nur_abgedeckt` uses the run and
  `brueckenSchritt_satz`; `drain_erhaelt_erbt` applies all arguments to the
  accepted `erbtW_schritt`; `brueckenSchritt_rmw` unpacks `s.lauf` and applies
  `hSW.rmw g h`; `lauf_global_verweigert` uses `v`, `h0`, `h1` against the
  accepted stale facts. No `intro _`, no `have _ :=`, no `Prop`-typed premise,
  no restated-premise conclusion, no quantified-away contract.
- **Accepted evaluator lifted, not copied.** The file introduces only
  `FragArt`/`BrueckenSchritt`/`BrueckenLauf` and theorems; TSO vocabulary
  (`TSOTrace`, `SourceMemory`, `WordAccessGrouping`) and machine W
  (`RufSchrittW`, `RufErreichbarW`, `erbtW_schritt`, `stale_kein_globaler_wert`,
  `schrittW_aus_gruppen_drain_zeuge`, `spurW_*` witnesses) are imported and
  referenced, never redefined. The author report's claim on this point is
  accurate.
- **Planted refusals really refuse.** `brueckenSchritt_kein_drain` excludes
  drain-only progress at the type level (`art ≠ .drain` field);
  `lauf_global_verweigert` derives `False` from two agreeing core observations
  against the accepted divergent facts — a genuine validator refusal, not a
  vacuous one.
- **Witness non-degenerate.** `brueckenLauf_erreichbar_zeuge` jointly exhibits:
  written table (`ctHw` via `(vertragVon witD ()).schreibt () = true`),
  memory-changing source step (slot `0 → 42`) and target bytes
  (`witM.bytes witA ≠ witM'.bytes witA`), two-core reached trace
  (`spurW0`/`spurW4`) with observable canonical-memory change at two addresses
  (`sbX`, `sbY`), owner-only forwarding (`loadByte ctS4 0 ctF = 0` vs
  `loadByte ctS4 1 ctF = ctFv`), distinct trace clocks. Exceeds the
  memory-change + two-core bar.
- **Silicon facts.** The file states no new hardware facts (no encodings,
  fault classes, or ordering rules); stale-view facts reuse the accepted
  `sb_*` witnesses. Nothing to check against the SDM extracts, nothing
  mis-stated.
- **CUTS honest, no over-claim.** The CUTS block lists exactly the proved run
  induction, coverage, drain/RMW/stale lemmas and witness, and leaves OPEN:
  LOCK/RMW construction, shared atomics, GX refinement, `valX86_sound`,
  scheduling/fairness/timing, interrupts/devices/MMIO/DMA. It explicitly
  disclaims any `HwAdapter`/`HwSchritt` embedding. No hardware-correspondence
  or W/GX closure is claimed.

## Scope note (not a rejection reason)

The proved induction is over the candidate's own `BrueckenLauf` chains, whose
links already package a `RufSchrittW`; the per-trace-step application of the
three accepted per-step theorems (with footprint/lowering-certificate
discharging) to a raw `TSOTrace` is connected only at the witness level (one
store step via `schrittW_aus_gruppen_drain_zeuge`). The candidate's CUTS and
report disclose this boundary and claim nothing beyond it, so this is recorded
as remaining consumer work, not fake closure. The owner-task MECHANISM
paragraph (`HwAdapter`/`HwSchritt` family template) does not fit this lane's
TASK (consumer is machine W, not `HwMaschine`); the author's documented
deviation to the TASK text is correct.

## Build result

- Candidate evidence (`BUILD-EVIDENCE.json`): `./lean-probe` ends at
  `== 0 error(s) in the COMPLETE output`; `./lean-bau`:
  `Build completed successfully (618 jobs)` at the candidate commit.
- Reviewer baseline (this clone `a1188`, `muse/1188`, clean at `9b05e84a`):
  `./lean-bau` → `Build completed successfully (619 jobs).`
  (619 vs 618: master moved past the candidate base; the candidate file itself
  was verified from its pinned snapshot, not re-applied here, per report-only
  review scope. Cross-clone reads outside this clone were refused by policy.)

## What remains open

Per candidate CUTS: LOCK/RMW steps, shared atomics, GX refinement consuming
these runs, `valX86_sound`, scheduling/fairness/progress/timing,
interrupts/devices/MMIO/DMA. Nothing further for lane 1188.
