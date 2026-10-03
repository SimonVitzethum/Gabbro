# MUSE-REPORT-859: Composition closing: region-ceiling closing

## What was done

New file `grammatik/Grammatik/X86/ComposeRegionCeil.lean` (owned) plus the
required `import Grammatik.X86.ComposeRegionCeil` line at the end of
`grammatik/Grammatik.lean` (owned). The file composes only already-accepted
modules by name and re-proves nothing:

- Producer: `Regionen.reserviere` (checked bump allocator with declared
  ceiling / refuse-on-full) and `Regionen.freiReserviere` (opt-in
  ceiling-free model) with `ausricht`, `alleUnten`, `reserviere_voll_verweigert`,
  `freiReserviere_kann_scheitern`, `freiReserviere_ohne_statik_gebunden`.
- Consumer: `RegionSeparation.trennungOk` verdict and `RegionFresh.frisch_zwei_verdikt`
  / `frisch_schreibt_rahmen` frames over actual `Speicher` (`write64`/`read64`).
- Non-degeneracy evidence reused (not redone): `TableLayout.zeugenU_schreibt`
  (table `konto` with writer `setze`) and `Ausfuehrung.zeuge_speicher_aendert_sich`
  (reached run storing byte 42 at 8192 from zero).

Closed interface: dynamic regions close to declared ceilings with
refuse-on-full; a ceilingless region stays refused by default behind the
explicitly named opt-in gate `deckellosSchluss` (flag `optIn`).

## Exact new names

- `deckellosSchluss` (def): `if optIn then freiReserviere ... else none`.
- `deckellos_default_verweigert`: gate with `optIn = false` is `none`.
- `deckellos_benannt_offen`: gate with `optIn = true` is exactly `freiReserviere`.
- `deckel_zwei_trennung`: two successive ceiling reservations give
  `trennungOk [r1, r2] = true` (via `frisch_zwei_verdikt`).
- `deckel_voll_verweigert`: past-ceiling request is `none` (via
  `reserviere_voll_verweigert`).
- `deckel_schreibt_rahmen`: store in first handed region preserves reads in
  the second (via `frisch_schreibt_rahmen`, actual `write64` transition).
- `deckellos_optIn_kann_scheitern`: open gate with external `scheitert = true`
  is still `none` (via `freiReserviere_kann_scheitern`).
- `ComposeRegionCeil_verbindung` (TARGET): generic conjunction over arbitrary
  admitted inputs — verdict + store frame + default refusal + loud opt-in
  failure + opt-in bound-loss witness past any `B < 2 ^ 64`. Every premise is
  used (reservation premises feed verdict/frame, gate premises feed both
  refusals, `B`/`hB` feed the bound-loss existential).
- `ComposeRegionCeil_verbindung_zeuge` (companion): joint instantiation on the
  accepted witness chain (65536/65544 reservations, nonzero `write64` through
  with changed byte from zero and preserved neighbour read, default refused,
  opt-in past 4096, writer `setze`, reached 42-at-8192 run, planted
  refuse-on-full at 8192 bytes vs 4 KiB ceiling, planted overlap refusal).

## Last build result

`./lean-bau`: `Build completed successfully (511 jobs).` — whole project green,
including `Grammatik.X86.ComposeRegionCeil (5.1s)`.
`./lean-probe grammatik/Grammatik/X86/ComposeRegionCeil.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
Axioms: `deckellosSchluss` none; gate lemmas `[propext]`; composition and
witness `[propext, Quot.sound]` — subset of the `gabbro_ziel` standard
(`propext, Classical.choice, Quot.sound`).

## What remains open (CUTS in file)

No source-to-allocator correspondence (which Gabbro arena/gate lowers to which
`reserviere` call, duties/costs/templates); no int-to-ptr (capabilities only);
sequential footprints only — per-access TSO refinement stays with the TSO bridge
(accepted 567/TSOHistory owners); opt-in keeps its accepted cost (may fail, no
static bound below `2 ^ 64`); no loader/image beyond `RegionSeparation`
vocabulary; no decoder/encoder/semantics/ABI/cost/budget/entry/whole-image work;
no `Zielsatz/Spec` touched; full source-to-final-bytes validation OPEN.

## Task assessment

Nothing in the task appears wrong. The target statement needed no extra premise:
the bound-loss leg is an existential conjunct fed by `B`/`hB`, not an added
assumption. No new numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/
emitter edits, no friend-reserved optimiser files touched. Owned files only:
`grammatik/Grammatik/X86/ComposeRegionCeil.lean`, `grammatik/Grammatik.lean`,
this report.
