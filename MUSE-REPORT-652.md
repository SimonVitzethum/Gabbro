# MUSE-REPORT-652: Whole-word drain with real interleaved foreign accesses

## Task

Lane 652 (owned paths: `grammatik/Grammatik/X86/WordDrainInterleaving.lean`,
`grammatik/Grammatik.lean`): consume the accepted 603 vocabulary
(`WortGruppe`, `FremdFrei`, `DrainSchritt`, `DrainSpur`, canonical
`issueByte`/`flushKern`) and derive grouped read-back plus foreign-word
preservation across a drain trace containing an actual foreign issue AND
an actual foreign flush between own flushes. Trace exclusion must come
from finite footprint checks on real accesses, never from assumed
end-state equality. No hardware-atomicity claim, no LOCK source
refinement, no fairness/timing premise. Producer modules untouched.

## What was done

New file `grammatik/Grammatik/X86/WordDrainInterleaving.lean` (806 lines),
plus the one import line appended to `grammatik/Grammatik.lean`.
No existing file was modified otherwise.

**§1 Finite exclusion API (generic):** `eintragFrei` / `pufferFrei`
(decidable per-entry/per-buffer footprint checks on real pending
entries), `eintragFrei_gilt`, `pufferFrei_gilt`,
`fremdFrei_von_pruefung` (core-1 list check + other-core emptiness
implies `FremdFrei`), `spurFrei_von_pruefung` (trace lift).

**§2 Generic drain consequences:** `verflochten_liest_zurueck`
(603 read-back with exclusion derived from the finite checks),
`verflochten_fifo_suffix` (own FIFO retained as suffixes of the
canonical eight-entry list, via `drain_installiert_aux`),
`worteintrag_in_fuss` / `suffix_eintrag_in_fuss`,
`verflochten_fremd_bleibt` (own flush preserves disjoint foreign
bytes), `verflochten_fremd_installiert` (foreign flush installs).

**§§3–8 Interleaved witness (11 states, 10 steps):** `wI0` (= 603
`grpS2`, exact group on core 0) → own flush 1 → foreign issue on
core 1 at `vB = 8192` (`wI_issue`, memory-silent, `by rfl`) →
foreign flush (`wI_fflush`, `by rfl`) → own flushes 2–8 (`wI_e2`…
`wI_e8`, all `by rfl`). Exclusion `wI_hstoer` is derived through
`spurFrei_von_pruefung` from per-state list facts (`wI_h1`) and
rest-emptiness (`wI_hRest`, chained through §5 preservation lemmas).
Consequences: `wI_spur` (mixed `eigen`/`fremdAusgabe`/`fremdSpülen`
trace), `wI_erreichbar`, `wI_liest_zurueck` (grouped word back),
`wI_fremd_byte` + `wI_fremd_wort` (foreign byte/word preserved),
both buffers drained, both memories changed.

**§9 Joint witnesses:** `wI_zeuge_gelenk` (one existential with trace,
reachability, both drains, exclusion, FIFO, both read-backs, both
memory changes, and the exhibited foreign issue+flush between own
flushes) plus per-claim joint inhabitants
`verflochten_liest_zurueck_zeuge`, `verflochten_fremd_bleibt_zeuge`,
`verflochten_fifo_suffix_zeuge` (each instantiates ALL premises
jointly on the non-degenerate witness; planted negative mutations
are the §10 refusals).

**§§10–11 Refusals and disclaimers:** `wOv_bool_verweigert` /
`wOv_prop_verweigert` (overlapping foreign entry at footprint byte 3
fails the decidable check and `FremdFrei`, gating both its issue
product and any flush from it), `ausrichtung_allein_verweigert`
(aligned `vA` yet no group), `verflochten_erster_schritt_reisst`
(first flush visibly tears: byte 0 new, byte 1 old — ten visible
intermediate states, no hardware-atomic instruction claimed),
`verflochten_verweigert_lock` (LOCK path disjoint, no LOCK source
refinement).

## Verification

- `./lean-probe grammatik/Grammatik/X86/WordDrainInterleaving.lean`:
  `0 error(s)`, exit 0.
- `./lean-bau`: `Build completed successfully (458 jobs)`, whole
  project green.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (checked by grep;
  only `#print axioms` lines match).
- `#print axioms` for all main theorems: at most `propext`,
  `Quot.sound` — within the standard goal set.
- Every added theorem uses all its premises; no conclusion restates a
  premise; no Prop-typed premises; no new executor/IR/guessed ISA.

## Exported consumer interface (for CarrierTraceBridge650/validators)

`verflochten_liest_zurueck`, `verflochten_fifo_suffix`,
`verflochten_fremd_bleibt`, `verflochten_fremd_installiert`,
`eintragFrei`/`pufferFrei` + `pufferFrei_gilt` /
`fremdFrei_von_pruefung` / `spurFrei_von_pruefung`,
`wI_spur` / `wI_erreichbar` / `wI_zeuge_gelenk`, the three `_zeuge`
inhabitants. See CUTS in the file for the exact contract.

## Open / next useful task

- Two-core slice only (core 1 checked, other cores empty); wider core
  counts need the same per-core checks (mechanical follow-up).
- No W/GX per-access simulation and no typed-carrier bridge — owned
  by CarrierTraceBridge650 / BridgeWrite / BridgeRead as consumers.
- I believe the task text is correct as written; one note: the lane
  file names no NEW file, so the filename was taken from the
  coordinator registry (`WordDrainInterleaving.lean`), which is the
  owned path registered for lane 652.
