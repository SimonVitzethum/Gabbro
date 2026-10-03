# MUSE-REPORT-832: Composition closing — contract-at-return closing

## What was done

New file `grammatik/Grammatik/X86/ComposeContractReturn.lean` (~293 lines)
plus one import line in `grammatik/Grammatik.lean`. It closes the
return-contract producer/consumer interface over already-accepted modules
only — nothing is re-proved, no interpreter/executor is duplicated, no
source/checker/Spec/goal/emitter file is touched.

Closing step: `rueckSchlussOk` (one checked `Bool`) conjoins the source
return leg at actual values (`EnsAmRueck P f sread sret rho v`, i.e. the
`ensures` bit for the actual `rho`/`v` between the actual entry-side and
return-side worlds) with the three accepted target admission bits
(`eintrittOk`, `valX86`, `kostenSummeOk`).

## Exact new definitions/theorems

- `rueckSchlussOk` (def): the closing Bool.
- `ComposeContractReturn_verbindung` (TARGET): generic over arbitrary
  `D/P/f/worlds/rho/v/profil/bild/art/z/summary`; four legs in, closed
  Bool out. Every premise used by the proof.
- Projections (closed step carries each leg):
  `rueckSchluss_gibt_ens`, `rueckSchluss_gibt_eintritt`,
  `rueckSchluss_gibt_val`, `rueckSchluss_gibt_kosten`.
- Generic refusals (one failing leg poisons the close):
  `rueckSchluss_verweigert_ohne_ens`,
  `rueckSchluss_verweigert_ohne_eintritt`,
  `rueckSchluss_verweigert_ohne_val`,
  `rueckSchluss_verweigert_ohne_kosten`.
- Concrete legs/refusals: `eintritt_valZeuge_hosted_ok` (`decide`),
  `laxeSummary` + `laxeSummary_verweigert` (`decide`),
  `schluss_verweigert_falsches_ergebnis` (refuting result `miniV0`),
  `schluss_verweigert_xmm_ohne_sicherung`,
  `schluss_verweigert_mutiertes_byte`,
  `schluss_verweigert_unbegrenzte_wiederholung`.
- `rueckSchluss_ohne_qensures`: place holds through the close while
  `QEnsuresB` is false on the same contract — inferred ensures never
  admitted (reuses `mini_ens_am_ort`, `mini_qensures_falsch`).
- `ComposeContractReturn_verbindung_zeuge` (ZEUGE companion): all four
  premises jointly on the real `setze` return (body outcome, sinv
  equation, `.ok` outcome from `rufAt_ok_gibt_ens_zeuge`), `schreibt`
  table proof, `0 -> 5` slot change, reached machine run from
  `vertragStandort_lauf_zeuge`, closed step derived, plus a byte-level
  `write64`/`read64` memory change from `eintritt_zeuge`. Non-degenerate.

## Last `./lean-bau` result line

`Build completed successfully (509 jobs).` — `== exit 0; 0 error
line(s) in the COMPLETE output`. `./lean-probe` on the new file: `==
0 error(s)`. `#print axioms` for every main theorem is standard
(`propext`, `Classical.choice`, `Quot.sound`; `decide` lemmas use
`propext` only).

## What remains open (see CUTS in the file)

Per-access x86-TSO refinement and full source-to-final-byte closure
(decoder/bridge lanes); caller footprint/lock floor (`InlinePflicht`
`hp`/`hr` stay with ContractSites); indirect calls; budget simulation
(`budgetSimulationOffen`); wider guard/decode sweeps with owning lanes.

## Task feedback

Nothing in the task is wrong. One observation: the producer legs compose
on a single shared `bild`, so the witness needs one image admitting both
`eintrittOk` and `valX86` — `valZeuge` with `zeugenEintrittHosted`
satisfies both (`eintritt_valZeuge_hosted_ok` by `decide`,
`valZeuge_akzeptiert` reused). No interface change was needed anywhere.
