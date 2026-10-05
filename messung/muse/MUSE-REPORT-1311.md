# MUSE-REPORT-1311: Capstone, second step — post-union families

## What was done

NEW FILE `grammatik/Grammatik/X86/HwKapsteinZwei.lean` (+ one import line
in `grammatik/Grammatik.lean`): the second capstone union `HwVollSchritt2`
over `HwMaschine`, extending the first union `HwVollSchritt` (lane 1149,
reused unchanged) with one arm per family merged since. All 16 families
named in the task were surveyed in the tree; all exist.

- Event type `Kap2Ereignis`: `.alt` (whole first union) + 13 new tags:
  `rot`, `carry`, `bittest`, `bitscan`, `fpstore`, `pf`, `ctx`, `wc`,
  `avx2mem`, `avx2tor`, `seiten`, `gross`, `uebersetz`.
- `HwVollSchritt2`: 14 arms. Ten flat arms lift accepted adapters /
  relations (`adapterRot`, `adapterCarry`, `adapterBitTest`,
  `adapterBitScan`, `fpStoreAdapter`, `adapterPf`, `CtxSchritt`,
  `HwMemWC1287.adapterWc1287`, `HwAvx2Schritt`, `adapterAvx2Tor`).
  Three paging arms lift the accepted refused defaults
  (`adapterSeiten/Gross/Uebersetz = verweigertAdapter`, vacuous but
  exact, not silently dropped).
- Exact embedding: `kap2_alt_embedded` (old union) + 13 per-family
  iffs (`kap2_rot/carry/bittest/bitscan/fpstore/pf/ctx/wc/avx2mem/
  avx2tor/seiten/gross/uebersetz_embedded`), each proved both
  directions by constructor/inversion.
- `HwWf` preservation: `kap2_wf` via each family's accepted lemma
  plus helper `kap2_adapterAvx2Tor_wf` (gate-premise lemma discharged
  by open/closed case split with `adapterAvx2Tor_verweigert`).
- Tag disjointness `kap2_tags_disjoint` + `kap2Tag` (mirror of
  `kap_tags_disjoint`); refusals `kap2_verweigert` (three paging
  adapters admit nothing, citing accepted lemmas).
- 15 exhibited reached union steps from the families' own witnesses:
  `kap2_step_rot/carry/bittest/bitscan/fpstore/pf/ctx/wc/avx2mem/
  avx2tor` (flat, via witness equations) and `kap2_step_seiten/gross/
  uebersetz/segtlb/avx2join` (boundary base observations on the
  extended families' own witness machines via the `.alt` arm).
- Joint witness `kap2_zeuge` joining steps, refusals, two-core value
  pins (carry 22/12, context 260/260), cited owner-only forwarding
  with memory-changing drain, and witness-machine well-formedness.
- CUTS block + `#print axioms` per main theorem (all in
  `[propext, Quot.sound]` or fewer; no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwKapsteinZwei.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (688 jobs)`, whole
  project green.

## What remains open / findings

- FINDING (task-sanctioned): `Avx2Ops` contributes no union arm —
  by its own design it defines NO `HwAdapter`, NO `HwSchritt`
  embedding and NO `HwWf` preservation (pure 256-bit evaluators;
  see its CUTS). AVX2 machine coverage comes from
  `Avx2Join`/`Avx2State`/`Avx2Mem` arms instead.
- Walk/fault legs (paging/large/translation), segment/TLB legs
  beyond observation, and YMM legs ride no closed flat-machine step
  (extended state the coherent machine does not carry — same reason
  the first union keeps async delivery out); recorded in CUTS with
  the `.alt`-composition argument.
- The three paging boundary steps share one witness machine and one
  observation; strand-distinctive content stays in the families' own
  witnesses (cited, not re-stepped).
- Decoder priority for the new rows beyond family-local pins,
  hardware correspondence beyond self-consistency, and any W/GX
  bridge stay open (CUTS). No silicon claim is made; vendor-neutral
  (undefined behaviour stays free) holds by construction since no
  new semantics was defined.

## Notes for the reviewer

- `HwMemTypesWC` nests its declarations under `HwMemWC1287` and
  `Avx2Join` under `Avx2Join`: all references are qualified.
  (`WcZugriff1287` unqualified fails with a universe error.)
- `adapterBild = adapterInteger666` by definition: the avx2tor step
  reuses `adapterBild_vereinbarung` + `inst_schritt_muldiv` through
  definitional unfolding (sibling `HwKapsteinSteps` not imported).
- No existing file was touched except the one import line in
  `grammatik/Grammatik.lean`. No reserved number ranges were needed
  (no new diagnostic codes, gifts, or examples).
