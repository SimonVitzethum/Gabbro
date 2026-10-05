# MUSE-REPORT-1187: TSO traces to W runs — run induction

## What was done

New file `grammatik/Grammatik/X86/TsoRunInduction.lean` (~270 lines) plus one
`import Grammatik.X86.TsoRunInduction` line appended to `grammatik/Grammatik.lean`.
No existing file was otherwise touched; no accepted definition was copied or
redefined — the TSO side reuses `TSOTrace`/`SourceMemory`/`WordAccessGrouping`
vocabulary unchanged.

Follow-up of lane 1143 (`TsoReadBridge.lean`) and `CarrierTraceBridge.lean`:
those prove PER-STEP bridges (one lowered store/read/drain fragment step yields
one typed-carrier `SchrittW`). This lane proves RUN induction over them.

## New definitions/theorems (all in `Gabbro.Grammatik.X86`)

- `FragArt` — step kinds: `store`, `loadCommit`, `loadFwd`, `drain`.
- `BrueckenSchritt` — one bridged fragment step: its kind, the actual
  `RufSchrittW` it yields, and `abgedeckt : art ≠ .drain` (drain-only TSO
  progress is refused a W step).
- `BrueckenLauf` — finite lowered-fragment run (snoc-chained bridged steps).
- `brueckenLauf_erreichbar` — **run induction**: a finite bridged chain yields
  `RufErreichbarW` from chain start to chain end.
- `brueckenSchritt_satz`, `brueckenLauf_nur_abgedeckt`,
  `fragArt_abgedeckt_oder_drain` — exact coverage: every bridged step is a
  no-read store, committed read, or forwarded read.
- `brueckenSchritt_kein_drain` — planted refusal: no bridge step is drain-only.
- `drain_erhaelt_erbt` — drain-only `SpurSchritt` preserves `ErbtW`
  (accepted `erbtW_schritt`, named for the run consumer).
- `brueckenSchritt_rmw` — the RMW atomicity obligation rides along each step.
- `lauf_stale_kein_globaler_wert` (reuses `stale_kein_globaler_wert`),
  `lauf_global_verweigert` — no single byte value agrees with both cores at
  `sbY` in `sbNach2`: a validator needing one global value per address refuses
  this state.
- `brueckenLauf_erreichbar_zeuge` — joint non-degenerate witness: `witD` with
  a written table (`ctHw`), one-step bridged run, source slot `0 → 42`,
  changed target bytes, inherited history + invariant over the drain end,
  reached one-flush trace with two distinct timestamps, pending foreign byte
  outside the footprint, stale-view divergence (core 0 reads 0, core 1
  forwards 7), and the reached two-core trace with observably changed memory
  at two addresses.

## Build result

- `./lean-probe grammatik/Grammatik/X86/TsoRunInduction.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (618 jobs)`.
- `#print axioms`: standard only (`propext`, `Classical.choice`,
  `Quot.sound`, or subsets). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## What remains open (see file CUTS)

LOCK/RMW steps, shared atomics (`.inr` carriers, `HavocA`/`GeteiltV`), the GX
refinement consuming these runs, `valX86_sound`, scheduling/fairness/progress/
timing, interrupts/devices/MMIO/DMA.

## Note on the task text

The MECHANISM paragraph describes a `HwAdapter`/`HwSchritt` family-connection
template (well-formedness preservation, evaluator agreement). That template
does not apply here: this lane's TASK is TSO→W run induction whose consumer is
machine W, not `HwMaschine` — there is no hardware evaluator to agree with and
nothing to refuse at the `HwSchritt` level. I followed the TASK (per-step
bridges → run induction, stale-view case as in the reads bridge, exact coverage
stated, no `valX86_sound` claim) and recorded the non-embedding in CUTS. If a
`HwMaschine` connection is wanted, that is a separate lane.
