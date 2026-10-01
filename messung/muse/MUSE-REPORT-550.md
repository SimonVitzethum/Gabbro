# Muse Report 550 — Independent exact-candidate review of 544 RegionFresh

## Scope

Review of the exact candidate patch for lane 544 (N18 `X86/RegionFresh.lean`)
against its owner task, the actual source/target semantics in this clone,
and the promised N-row consumer. Clone verified: `/home/simon/Dokumente/gabbro-muse/a550`,
branch `muse/550`. Owns only this report.

CANDIDATE: 544 7d6ac09a30719f10e5e9251ae8d8900097982d3a
VERDICT: ACCEPT

## What was checked

- Snapshot (`.tmp/review/SNAPSHOT.json`): author 544, head
  `7d6ac09a30719f10e5e9251ae8d8900097982d3a`, base `3dce9fa2`, files
  `MUSE-REPORT-544.md`, `grammatik/Grammatik.lean` (one additive import),
  `grammatik/Grammatik/X86/RegionFresh.lean` (new, 453 lines). FETCH_HEAD
  matches the pinned HEAD; diff stat matches (3 files, +567).
- Owner task (`.tmp/review/author-544/OWNER-TASK.md`): generic fresh/disjoint
  external-region preservation over accepted `reserviere`/`initialisiere` and
  `RegionSeparation`, actual memory transitions, multiple reservations, refused
  overlap, no int->ptr, source/binding extent origin, precise CUT if the
  lowering correspondence is missing.
- N-row (`dokumente/x86/NEXT-PROOF-WAVE.md` N18): USES
  `Regionen.reserviere/initialisiere` + 432 separation, TARGET fresh-disjoint
  external-region proofs per allocation with no int->ptr, WITNESS+ two
  reservations proved disjoint with stores, WITNESS- overlapping reservation
  refused and number-derived address refused.
- All referenced interfaces resolved to real definitions in this clone:
  `Regionen.reserviere/reserviere_frisch/reserviere_disjunkt_unten/
  reserviere_haelt_alleUnten/reserviere_innerhalb/alleUnten/alleUnten_leer/
  zeugenStart/zeugenVorrat/zeugenRegion/zeugenReserviere_erfolg/inRegion/
  initialisiere/initialisiere_rahmen_bytes/natAdresse`,
  `RegionSeparation.allePaareDisjunkt/keinUmbruchR/alleOhneUmbruch/trennungOk/
  regionDisjunkt_symm/trennung_schreibt_rahmen/trennung_schreibt_bytes`,
  `TableLayout.layoutFuer/alsRegion/eintragOk/paarOk/layoutOk/zeugenU/
  zeugenU_schreibt/layout_zeuge`, `Ausfuehrung.lauf/zeugeProg/zeugeZustand/
  zeuge_speicher_aendert_sich`, `Speicher.write64/read64/
  read64_nach_write64/writeBytes/writeBytesN_hit/addrOff_null/schreibbar8/
  lesbar8/OhneUmbruch`. No self-invented semantics or second IR/executor.
- Delivered theorems: `ausZahlVerweigert`, `ausZahlVerweigert_klingt`,
  `disjunkt_nicht_in_region`, `innerhalb_keinUmbruch`, `frisch_zwei_disjunkt`,
  `frisch_zwei_verdikt`, `frisch_schreibt_rahmen`, `frisch_init_rahmen`,
  `layoutOk_trennung`, plus witness definitions and `regionFrisch_zeuge`.

## Evidence (reproduced in this clone)

- Staged only the candidate `RegionFresh.lean` from FETCH_HEAD plus one
  additive `import Grammatik.X86.RegionFresh` on current master, then restored.
- `./lean-probe grammatik/Grammatik/X86/RegionFresh.lean`: first line
  `== 0 error(s) in the COMPLETE output; exit 0`. Axioms printed per theorem:
  at most `[propext, Quot.sound]` (subset of the standard triple);
  `decide` probes depend on no axioms.
- `./lean-bau`: `Build completed successfully (421 jobs)` with the candidate
  staged on current master (author evidence was 416 jobs on its older base;
  the higher count is master advancement, not a discrepancy).
- Word-boundary grep for `sorry|admit|axiom|native_decide|unsafe`: no hits.
- No `Zielsatz/Spec`, checker, emitter, or friend-path edits; ownership is the
  one new file plus one additive import.

## Correctness assessment

- `frisch_zwei_disjunkt` is genuine: freshness triple from `reserviere_frisch`
  places `r1` in `s1.belegt`, the preserved cursor invariant feeds
  `reserviere_disjunkt_unten`, closed by `regionDisjunkt_symm`. The conclusion
  is not a restated premise; interval work is discharged, not assumed.
- `frisch_zwei_verdikt` correctly builds `trennungOk [r1, r2]`: no-wrap for
  both regions comes from `reserviere_innerhalb` via `innerhalb_keinUmbruch`
  (the third conjunct of `innerhalb` is exactly the bound), disjointness from
  freshness. `allePaareDisjunkt [r1, r2]` reduces to the single-direction
  check, so one `regionDisjunkt` fact suffices — verified against the
  definition, not assumed.
- `frisch_schreibt_rahmen` / `frisch_init_rahmen` run through the actual
  `RegionSeparation` frame lemmas over real `write64` / `initialisiere`
  transitions with proved disjointness (the init side via the real interval
  fact `disjunkt_nicht_in_region`). Every premise is used.
- `layoutOk_trennung` is a genuine induction: `layoutOk = all eintragOk &&
  paarOk`, and `paarOk` is the `regionDisjunkt`-over-`alsRegion` check, so the
  mapped `allePaareDisjunkt` follows without assuming the lowering. Extents
  originate in the computed source layout, never in a number.
- No int->ptr: `ausZahlVerweigert` decides non-membership and is proved sound;
  `natAdresse` is the existing probe-address constructor used for witness
  addresses only. No OS/kernel trust, no unsigned/signed/width/fault
  conflation, no assumed source simulation.
- Witnesses are non-vacuous and joint through the generic theorems:
  `frisch_zeugen_zweit` is a real second allocation by `decide` whose
  pre-state exactly matches `zeugenReserviere_erfolg`'s post-state;
  `frisch_schreibt_rahmen_zeuge` stores nonzero 42, reads back, shows the
  changed byte and the preserved cross-region read/byte; `regionFrisch_zeuge`
  jointly ties the source writer fact (`zeugenU_schreibt`, table `konto`), a
  reached memory-changing run (`zeuge_speicher_aendert_sich.2.1`), the accepted
  two-region verdict, proved disjointness, both refusals, and the real store
  frame. Refusals: overlapping `[65540,65548)` refused, bare `0` refused, and
  non-vacuity shown (`65536` admitted).
- Note (not a defect): the N-row WITNESS+ phrase "stores to both" is covered
  here by a `write64` into the first region plus `initialisiere` of the second
  (both actual memory-changing transitions over the two handed regions, with
  read/write permission probes at both addresses). The generic read/byte
  frames are directional through the symmetric disjointness lemma, so the row
  is honestly met; no repair warranted.

## CUTS (as recorded in the candidate file; precise and accepted)

No source-to-allocator lowering correspondence; sequential footprints only
(TSO/atomicity with the TSO bridge); only the ceiling-carrying `reserviere`
chain (ceiling-free `freiReserviere` untouched); no loader/image integration
beyond `RegionSeparation` vocabulary; no decoder/ABI/cost/timing/whole-image
claim; no `Zielsatz/Spec` change; full source-to-final-bytes validation OPEN.
The report claims only the N18 row, never the closed bridge.

## Remaining / task-text notes

Nothing in the owner task text was found to be wrong. The "admitted witness"
phrase is correctly read as reusing accepted nonempty witnesses; no Lean axiom
was admitted. No repair locations: no file or line needs changing.

## Build state

Staged candidate files were fully restored before this report commit;
`git status` is clean except this owned report. Last reproduced results:
`./lean-probe` 0 errors; `./lean-bau` `Build completed successfully
(421 jobs)`.
