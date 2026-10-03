# Muse Report 837: Composition closing -- fence-order closing

## What was done

Closed fence placement to per-access concurrent equivalence in the new file
`grammatik/Grammatik/X86/ComposeFenceOrder.lean` (plus its import line in
`grammatik/Grammatik.lean`). The work composes four already-accepted legs
over the ONE canonical `TSOZustand`, reusing their definitions and theorems
by name without re-proving internals and without duplicating any interpreter
or executor:

- `FenceDrain.drainVoll` / `drain_fremd_puffer` / `drain_voll_leer` /
  `drain_voll_bereit` and the `fdS2`/`fdS3` witness family;
- `MfenceDrainOwn.mfenceDrain` / `mfenceSchrittAusBytes` /
  `mfenceDrain_leert` / `mfenceDrain_bereit` / `mfenceDrain_fremd` /
  `mfenceDrain_ordnung` / `mfenceDrain_erreichbar_von` /
  `mfenceAbgeschnitten15_verweigert` / `mfenceNachbarLFENCE_verweigert`;
- `SfenceStoreNarrow.sfenceOrdnet` / `sfence_ordnet_schreibe` /
  `sfence_ordnet_last_nicht`;
- `LfenceLoadNarrow.lfenceSchritt` / `mfence_verweigert_bei_vollem_puffer`.

## Exact new names

- `def fenceOrdnungGeschlossen` (composed postcondition predicate).
- `theorem ComposeFenceOrder_verbindung` (TARGET): on any reached state
  whose own-buffer MFENCE drain succeeds with a foreign entry pending, all
  three fence legs hold jointly (own drained and fence-ready, foreign
  byte-identical and pending, canonical loads on the acting core, drained
  state reached, SFENCE store-only order, LFENCE admission without drain
  and never the full barrier), while MFENCE refuses the pre-drain state.
  All four premises (`hreach`, `hdrain`, `hpend`, `hvoll`) are used.
- `theorem ComposeFenceOrder_verbindung_zeuge` (ZEUGE companion): all
  premises jointly inhabited on `fdS2`/`fdS3` (two issued stores on two
  cores, memory-changing drain, drained state reached).
- `theorem ComposeFenceOrder_keinEntfernen_ohne_zaun` (proved refusal):
  disjoint buffered bytes (`fdX != fdY`), yet fence removal observably
  changes a foreign load and canonical memory -- no removal on
  race-freedom alone.
- `theorem ComposeFenceOrder_bytes_verweigern` (planted byte refusals):
  truncated MFENCE bytes and the LFENCE-adjacent shape never run the
  byte-facing drain step.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeFenceOrder.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (full project): `Build completed successfully (509 jobs)`,
  `== exit 0; 0 error line(s) in the COMPLETE output`.
- Axioms: `fenceOrdnungGeschlossen` none; `ComposeFenceOrder_verbindung`
  `[propext, Quot.sound]`; `_zeuge` none; `_keinEntfernen_ohne_zaun` none;
  `_bytes_verweigern` `[propext]` -- all within the standard
  `propext, Classical.choice, Quot.sound` budget of `gabbro_ziel`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. No new
  diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched. Only owned files changed.

## What remains open (see CUTS in the file)

- No per-access target-to-W/GX simulation (missing producer legs:
  connection-wave owner 567 shared TSO-history projection, owner 570
  source-world byte representation; owners 573-574 W bridges build on
  them, never assumed here).
- No source-to-final-loaded-byte closing theorem (`valX86_sound` stays
  OPEN with the validator owner); no silicon correspondence beyond the
  stated canonical bytes; no timing/fairness/progress claim.
- No SFENCE over WC/NT stores, no LOCK RMW beyond accepted rows, no
  dispatch-serializing LFENCE, no fault beyond explicit refusal.

## Task assessment

Nothing in the task appears wrong. The ZEUGE target is proved with its
companion witness; the "exact theorem or refusal" demand is met with both
(a closing conjunction over arbitrary admitted inputs and two proved
refusals). The composition deliberately stops at the TSO/fence level and
names the W/GX legs it does not close.
