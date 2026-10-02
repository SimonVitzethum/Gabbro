# MUSE-REPORT-653: Independent review of author 652

## Scope

Review of lane 652 (whole-word drain with real interleaved foreign accesses)
against its owner task (follow WordAccessGrouping603 report N1). Inspected the
exact pinned snapshot (`.tmp/review/SNAPSHOT.json`), the owner task, the author
report, `PATCH.diff`, and the full candidate module (806 lines). Verified
snapshot integrity by hash against the pinned commit. No source edits; this
report is the only owned output.

CANDIDATE: 652 950785b18f1e1a2fde03e15e6cc32c9baac7bb16

VERDICT: ACCEPT

## What the candidate does

New file `grammatik/Grammatik/X86/WordDrainInterleaving.lean` plus the one
import line in `grammatik/Grammatik.lean`. No other file touched (diff stat:
report + import + new file, 904 insertions, 0 deletions).

- Finite exclusion API (`eintragFrei`/`pufferFrei`, `eintragFrei_gilt`,
  `pufferFrei_gilt`, `fremdFrei_von_pruefung`, `spurFrei_von_pruefung`):
  exclusion derived from decidable per-entry/per-buffer footprint checks on
  real pending entries, never from assumed end-state equality.
- Generic consequences: `verflochten_liest_zurueck` (wraps accepted 603
  `wort_gruppe_liest_zurueck` with derived exclusion),
  `verflochten_fifo_suffix` (own FIFO as suffixes of the canonical
  eight-entry list via accepted `drain_installiert_aux`),
  `verflochten_fremd_bleibt` (own flush preserves disjoint foreign bytes
  via `flush_rahmen` + `Disjunkt`), `verflochten_fremd_installiert`
  (foreign flush installs its byte via `flush_schreibt_kopf`).
- Interleaved witness, 11 states / 10 steps: `wI0` (= accepted 603 `grpS2`)
  through own flush 1, a real foreign `issueByte` on core 1 at `vB = 8192`,
  a real foreign `flushKern` on core 1, then own flushes 2-8. Every step
  equation holds `by rfl` against the canonical operations, so the witness
  states are computed, not forged. Exclusion `wI_hstoer` is derived through
  `spurFrei_von_pruefung` from per-state list facts (`wI_h1`) and
  rest-emptiness (`wI_hRest`).
- Joint witness `wI_zeuge_gelenk` with reached run, both buffers drained,
  grouped word read-back, foreign byte/word read-back, both memories
  observably changed, and the exhibited foreign issue+flush between own
  flushes; per-claim joint inhabitants for all three generic theorems.
- Refusals: overlapping foreign entry fails the decidable check
  (`wOv_bool_verweigert`) and `FremdFrei` (`wOv_prop_verweigert`);
  alignment-only counterexample (`ausrichtung_allein_verweigert`);
  first-step tearing (`verflochten_erster_schritt_reisst`: byte 0 new,
  byte 1 old); LOCK path disjoint (`verflochten_verweigert_lock`).

## Verification performed

- Snapshot integrity: `sha256` of the snapshot module and report match the
  pinned commit blobs exactly.
- Producer vocabulary confirmed present in this clone's accepted
  `WordAccessGrouping.lean`: `drain_installiert_aux`, `wort_gruppe_liest_zurueck`,
  `drain_spur_erreichbar`, `gruppe_verweigert_lock`, `Disjunkt`; the
  candidate's call shapes match the producer signatures (checked
  `drain_installiert_aux` and `wort_gruppe_liest_zurueck` argument order).
- Banned-pattern grep over the candidate: no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` outside comments and `#print axioms` lines.
- Premise-use check by reading: every theorem uses all premises; no
  Prop-typed premises; no conclusion restates a premise; no new
  executor/IR/guessed ISA; no desired correspondence carried as a premise.
- Build evidence in the snapshot is credible: incremental `lean-probe`
  history (including two intermediate failures that were repaired, not
  hidden) ending in 0 errors, final `./lean-bau` green at 458 jobs, and
  `#print axioms` within `propext`/`Quot.sound` for all main theorems.
- Witness non-degeneracy: exact eight-entry group buffer, reached run,
  both memories changed (`wI_grp_aendert`, `wI_fremd_aendert`, both `decide`).

## Accepted bounded claim

Whole-word grouped read-back plus per-byte foreign preservation across a
drain trace containing one real foreign issue AND one real foreign flush
between own flushes, with trace exclusion derived from finite footprint
checks on actual buffer accesses. Two-core slice only (core 1 checked,
other cores empty). No hardware-atomicity claim (first flush visibly
tears), no LOCK source refinement, no source/W-GX bridge, no
fairness/timing claim. Exports `verflochten_liest_zurueck`,
`verflochten_fifo_suffix`, `verflochten_fremd_bleibt`,
`verflochten_fremd_installiert`, the `eintragFrei`/`pufferFrei` check API,
and `wI_spur`/`wI_erreichbar`/`wI_zeuge_gelenk` for CarrierTraceBridge650
and validator consumers.

## Open (not defects)

- Two-core slice; wider core counts need the same per-core checks.
- No per-access W/GX simulation or typed-carrier bridge (consumer-owned).
- Generic foreign preservation is per-byte; whole foreign-word read-back
  is proved on the witness by `decide`. The report and CUTS state this
  accurately; no inflated closure found.
