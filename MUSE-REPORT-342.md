# MUSE-REPORT-342: OverlapRefusal (wave B2, O-align decidable half)

## What was done

New file `grammatik/Grammatik/X86/OverlapRefusal.lean` (~415 lines) plus one
additive import at the end of `grammatik/Grammatik.lean`. Nothing else touched.
Closed the O-align decidable half as specified in
`dokumente/x86/WORK-ALLOCATION.md` B2 against the reviewed direction:

1. Decided alignment/containment checker over footprints:
   `addrAusgerichtet`, `fussEnthalten` (reuses `Regionen.inRegion`),
   `zugriffBasis`, `zugriffOk` over the canonical `Zugriffe.Zugriff`.
2. Decided non-overlap with conservative three-state policy:
   `fussDisjunktB`, `UeberlappAntwort` (`disjunkt`/`gleich`/`unbekannt`),
   `klassifiziere`, `aliasZulassen` (`unknown-overlap => refuse`, and
   same-footprint sharing refused since it needs lock/atomic discipline).
   Soundness link `fussDisjunktB_klingt` (positive Bool answer means set
   disjointness).
3. Aligned-single-carrier bytes-value agreement lemma
   `einzelTraeger_wertUeberein` over `wortTraeger`: base names the carrier,
   carrier 8-aligned, no wrap, successful `write64`, readable footprint
   imply read-back, per-byte `wortByte` agreement, checker containment and
   checker alignment. Every premise is used.
4. Witness on one adjacent-carrier image (`nachbarBild`, sections at 8184
   and 8192 mirroring the real witness stack): accepted (`wohlgeformt`,
   `nachbarFund_a`, `nachbarFund_grenze`), real-extraction accepted
   accesses (`push_in_traeger_angenommen`, `store_in_traeger_angenommen`
   through `zugriff` on `zeugeZustand`), disjoint carriers
   (`nachbarTraeger_disjunkt`, `nachbarFuss_disjunkt`,
   `nachbarKlasse_disjunkt`, `nachbarPaar_zugelassen`), refused spanning
   access (`spanne_verweigert_unversetzt`, `spanne_verweigert_aussen`).
5. Refusal: counterexample-C shape as proved negative probes
   (`gegenbeispielC_unbekannt`, `gegenbeispielC_verweigert`): the misaligned
   8-byte access at 8196 overlapping two carriers classifies `unbekannt`
   and is refused. All refusals are `by decide` facts, not bare examples.
6. Joint witnesses with a real memory-changing reached run:
   `einzelTraeger_wertUeberein_zeuge` (write/read-back/byte-change at 8192
   plus the `zeugeProg` run fact) and `zugriffOk_zeuge` (accepts, disjoint,
   refusals and the run on one layout).

## Exact names of new definitions/theorems

Defs: `addrAusgerichtet`, `fussEnthalten`, `zugriffBasis`, `zugriffOk`,
`fussDisjunktB`, `UeberlappAntwort`, `klassifiziere`, `aliasZulassen`,
`wortTraeger`, `nachbarAbschnittA`, `nachbarAbschnittB`, `nachbarDatei`,
`nachbarBild`.
Theorems: `addrAusgerichtet_null_verweigert`, `probe_ausgerichtet_8192`,
`probe_unversetzt_8196`, `zugriffOk_ohne_fuss`, `fussDisjunktB_leer_links`,
`klassifiziere_disjunkt`, `klassifiziere_verweigert_unbekannt`,
`fussDisjunktB_klingt`, `einzelTraeger_wertUeberein`,
`nachbarBild_wohlgeformt`, `nachbarFund_a`, `nachbarFund_grenze`,
`nachbarTraeger_disjunkt`, `push_in_traeger_angenommen`,
`store_in_traeger_angenommen`, `spanne_verweigert_unversetzt`,
`spanne_verweigert_aussen`, `nachbarFuss_disjunkt`,
`nachbarKlasse_disjunkt`, `nachbarPaar_zugelassen`,
`gegenbeispielC_unbekannt`, `gegenbeispielC_verweigert`,
`einzelTraeger_wertUeberein_zeuge`, `zugriffOk_zeuge`.

## Last build results

- `./lean-probe grammatik/Grammatik/X86/OverlapRefusal.lean`: 0 errors.
  All `#print axioms` within standard set only (nothing, `propext`,
  `propext + Quot.sound`, or `propext + Classical.choice + Quot.sound`).
- `./lean-bau`: exit 0, 0 error lines, 386 jobs, build completed successfully.
- Axiom probe `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  0 errors; `gabbro_ziel` depends on axioms
  `[propext, Classical.choice, Quot.sound]` exactly, unchanged.

## What remains open (see CUTS in the file)

Tearing correspondence (aligned multi-byte single-copy atomicity under
concurrency) stays OPEN with the TSO bridge; refusal is validator admission,
not a hardware fault claim; same-footprint sharing needs lock/atomic
discipline owned elsewhere; no source correspondence; only the 14 pilot
forms; consumer side (shared IR 287) pending, no substitute invented.

## Task critique

The task direction is sound and I found no false premise to report. Two
readings I had to resolve and chose as follows: (a) "counterexample-C shape"
is documented in `dokumente/x86/TSO-GX-BRUECKE.md` section 2 as a misaligned
8-byte store / two-carrier overlap, which is what the negative probe pins;
(b) the INHABITATION rule as written triggers only on source-syntax
premises, but the lane task demands joint `_zeuge` with a memory-changing
run for target theorems, so both witness theorems carry `_zeuge` names and
conjoin the real `zeugeProg` run fact rather than restating it.
