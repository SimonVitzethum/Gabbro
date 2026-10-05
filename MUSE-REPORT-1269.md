# MUSE-REPORT-1269: Cross-declaration lowering certificate for the GX refinement

## What was done

New file `grammatik/Grammatik/X86/TsoGxCrossDecl.lean` (plus the one
`import Grammatik.X86.TsoGxCrossDecl` line appended to
`grammatik/Grammatik.lean`), closing the OPEN item in lane 1253's
(`TsoGxStart.lean`) CUTS: the cross-declaration lowering certificate
needed to join the `eP` entry/call prefix run with a `witD`
`BrueckenLauf`.

- Shape agreement (`formGleich_anzahl_e/wit`, `formGleich_typ_e` with the
  fragment side reusing the accepted `witHT`, `formGleich_ungeteilt_e/wit`,
  combined `formGleich`; `ctProg_ohne_ruf`): one single-slot
  `int 0 100` table per side, unshared on both sides; the fragment
  program performs no calls, so the joint call log is the prefix's logged
  `pruefe` entry.
- Decided certificate (`CrossDeclCert`, `crossCertProp`,
  `crossCertOkB` with instance `crossCertPropDec`, `crossCertWit`,
  `crossCertWit_ok` by `decide`, `crossCertOk_gleich` via
  `of_decide_eq_true`). One repair during construction: plain-`def`
  `crossCertProp` is not unfolded by typeclass search, so `decide`
  failed to synthesize `Decidable`; fixed with the explicit instance
  (unfold + infer_instance).
- Joint composition (`crossCert_gibt_joint`): a passing check yields the
  paired joint run -- lane 1253's `startFragment_zeuge` with lane 1187's
  `brueckenLauf_erreichbar_zeuge` -- every observable stated in terms of
  the certificate fields, so the check premise is consumed, not restated.
  The certificate carries data only (no runs), so rule 4 is respected.
- Finding (`crossCert_werte_divergieren`, `5 ≠ 42` by `decide`).
- Joint non-degenerate witness (`crossCert_joint_zeuge`): passing check,
  written tables on both sides, reached runs with observable memory
  change (`0 → 5` at the logged entry world, `0 → 42` at the fragment
  step plus a memory-changing target drain).

## Exact names of new definitions/theorems

`CrossDeclCert`, `formGleich_anzahl_e`, `formGleich_anzahl_wit`,
`formGleich_typ_e`, `formGleich_ungeteilt_e`,
`formGleich_ungeteilt_wit`, `formGleich`, `ctProg_ohne_ruf`,
`crossCertProp`, `crossCertPropDec`, `crossCertOkB`, `crossCertWit`,
`crossCertWit_ok`, `crossCertOk_gleich`, `crossCert_gibt_joint`,
`crossCert_werte_divergieren`, `crossCert_joint_zeuge`.

## Last `./lean-bau` result line

`Build completed successfully (658 jobs).`

`./lean-probe` on the new file: `== 0 error(s) in the COMPLETE output`.
Axioms: small facts `propext` or none; `crossCert_gibt_joint` and
`crossCert_joint_zeuge` on exactly `propext, Classical.choice,
Quot.sound` (inherited from the reused accepted witnesses). No `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe`; no new `Prop`-typed
premises; every premise is used.

## What remains open / findings

1. FINDING (exact obstruction, in the file's CUTS): no
   single-declaration joint run. `eD` and `witD` differ definitionally
   (`Fn` four constructors vs `Unit`, `Lock` `Unit` vs `Empty`,
   different programs/oracles, values `5` vs `42`), so no `BrueckenLauf`
   can start at `RufStartG` over `eP` and end over `ctProg` without a
   declaration morphism -- and any such morphism would need a
   desired-correctness premise (which function/table/value maps where).
   The certificate therefore certifies shape agreement plus paired runs,
   never a transported single run. This is reported, not weakened.
2. No per-access TSO-to-W/GX simulation beyond the reused accepted
   lemmas; no `valX86_sound`; no byte-level entry linkage; no hardware,
   timing, fairness or progress claim.
3. No `HwAdapter` by design (consumer is G/W/GX, not `HwMaschine` -- the
   same reading lanes 1215/1251 stand on); the generic hardware-family
   MECHANISM boilerplate does not apply to this checker-side composition.

## What I believe is wrong in the task

Nothing blocking. One note: the CONTEXT/MECHANISM paragraphs describe a
hardware-family connection (`HwAdapter`, `verweigertAdapter`, silicon
checks), but the TASK paragraph asks for the GX-refinement certificate
whose consumer is machines G/W/GX. I followed the TASK paragraph and the
`TsoGxRefine`/`TsoGxChecker` precedent (documented in CUTS); a
`HwAdapter` here would have been a second register over nothing.
