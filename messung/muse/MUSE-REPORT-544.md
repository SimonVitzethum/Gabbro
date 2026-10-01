# Muse Report 544 — N18 RegionFresh

## Task

Lane 544 (N18 `X86/RegionFresh.lean`): prove generic fresh/disjoint
external-region preservation over the accepted `Regionen`
`reserviere`/`initialisiere` and `RegionSeparation` interfaces, over actual
memory transitions and multiple reservations. Reuse the admitted
nonempty allocation/store witness and a refused overlapping interval.
Region extent/ownership originate in the existing source/binding model,
never from an integer-to-pointer conversion.

## What was done

New owned file `grammatik/Grammatik/X86/RegionFresh.lean` (only file owned,
plus one additive `import Grammatik.X86.RegionFresh` at the end of
`grammatik/Grammatik.lean`). No existing file, no friend path, no second
IR/executor touched. All steps reuse the canonical `Typen`/`Speicher`
vocabulary, `Regionen.reserviere`/`initialisiere`/`alleUnten`, and the
`RegionSeparation` checker/frames (`regionDisjunkt_symm`,
`trennung_schreibt_rahmen`, `trennung_schreibt_bytes`, `trennungOk`).

New definitions:

- `ausZahlVerweigert (n) (rs)`: decided refusal — a bare number lies in
  no listed region extent (admission requires `inRegion` membership).
- `frischRegionZwei`, `frischZustandEins`, `frischZustandZwei`,
  `frischSpeicher`, `frischRegionUeberlapp`: concrete witness
  region/allocator/memory/overlap values. The first reservation reuses
  the accepted `zeugenReserviere_erfolg` probe unchanged.

New theorems (every premise used by its proof; no conclusion restates a
premise; no `forall rho`/`forall v` weakening — contracts stay at their
place; interval arithmetic discharged by `omega`, frame conditions by the
actual `initialisiere`/`write64` lemmas):

- `ausZahlVerweigert_klingt`: refusal soundness (no int->ptr: a refused
  bare number is outside every listed extent).
- `disjunkt_nicht_in_region`: real interval fact — an address inside one
  of two disjoint regions is outside the other.
- `innerhalb_keinUmbruch`: containment carries the no-wrap bound.
- `frisch_zwei_disjunkt`: two successive `reserviere` calls hand disjoint
  regions (via `alleUnten` preservation + `reserviere_disjunkt_unten`).
- `frisch_zwei_verdikt`: both handed regions are accepted by
  `trennungOk` together.
- `frisch_schreibt_rahmen`: a successful `write64` inside the first
  handed region preserves reads inside the second (actual transition).
- `frisch_init_rahmen`: `initialisiere` of the second handed region
  preserves bytes inside the first (actual transition).
- `layoutOk_trennung`: SOURCE BRIDGE — an accepted computed layout
  separates as regions over `TableLayout.alsRegion` (extents originate in
  the source/binding model, never from a number).

Witnesses (WITNESS+ through the generic theorems, never parallel
`decide`-only copies where a generic path exists):

- `frisch_zeugen_zweit` (real second allocation probe, `decide`),
  `frisch_zeugen_start_unten`, `frisch_zwei_disjunkt_zeuge`,
  `frisch_zwei_verdikt_zeuge`, `frisch_schreibt_rahmen_zeuge` (nonzero
  store goes through, reads back, observably changes its byte, preserves
  the other region's read and byte), `frisch_init_rahmen_zeuge`,
  `layoutOk_trennung_zeuge` (on `layout_zeuge.1`),
  `frischLiest65544` plus decided permission/containment/no-wrap facts.
- WITNESS-: `frischUeberlapp_verweigert` (overlapping `[65540, 65548)`
  refused), `frischZahl_verweigert` (bare number 0 names no extent),
  `frischZahl_angenommen` (non-vacuity: 65536 IS admitted).
- `regionFrisch_zeuge` (JOINT, non-degenerate): source writer fact
  (`zeugenU_schreibt`: function writes table `konto`), reached
  memory-changing run (`zeuge_speicher_aendert_sich.2.1`), accepted
  two-region verdict, proved disjointness, overlap refusal, number
  refusal, and a real store with cross-region read preservation plus
  observable byte change.

## Verification

- `./lean-probe grammatik/Grammatik/X86/RegionFresh.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (416 jobs)` — whole project
  green.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` (checked with
  word-boundary grep; the only substring hit is English prose "admitted"
  in a doc comment).
- `#print axioms`: every theorem depends at most on `[propext,
  Quot.sound]` (subset of the standard `propext, Classical.choice,
  Quot.sound`); `decide` probes depend on no axioms.

## Remaining obligations / CUTS (as recorded in the file)

- Source-to-allocator correspondence (which arena/gate construct lowers
  to which `reserviere` call, duties/costs/templates) stays OPEN;
  `layoutOk_trennung` only re-reads the computed layout in region
  vocabulary.
- Sequential footprints only; per-access TSO refinement and atomicity
  stay with the TSO bridge.
- Only the ceiling-carrying `reserviere` chain is covered; the opt-in
  ceiling-free `freiReserviere` model and its external `scheitert` answer
  (user logic) are untouched.
- No loader/image integration beyond the `RegionSeparation` vocabulary;
  no decoder/ABI/cost/timing/whole-image claim; no `Zielsatz/Spec` change.
- Full source-to-final-bytes validation remains OPEN. This lane honestly
  delivers the N18 row (fresh/disjoint external-region proofs per
  allocation with planted refusals), never the closed bridge.

## Notes on the task text

- "Use an admitted nonempty allocation/store witness": read as reusing
  the accepted nonempty witnesses — done (`zeugenReserviere_erfolg`,
  `zeugenU_schreibt`, `zeuge_speicher_aendert_sich`, plus the new
  second-allocation and store probes). No new axiom was admitted in the
  Lean sense.
- "If the source binding correspondence is missing, retain it as a
  precise CUT": done — the correspondence is the first CUTS entry, and
  `layoutOk_trennung` is the proved extent-origin bridge that stops short
  of claiming the lowering.
