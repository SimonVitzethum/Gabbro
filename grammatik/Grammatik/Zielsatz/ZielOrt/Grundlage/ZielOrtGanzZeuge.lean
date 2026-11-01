/-
  File:      Grammatik/ZielOrtGanzZeuge.lean
  Subject:   WITNESSES AND THE PROBE for the goal theorem `ziel_ort_ganz`.

  * `ziel_ort_ganz_ref104`: the corpus program `beispiele/104-referenz.gab`
    (hand translation `r4P`) meets EVERY premise of `ziel_ort_ganz` jointly
    -- the new clause `KeineLogik` by the syntactic check -- and on its
    reached run (memory `0 -> 100`, the return of `einzahlen` logged) the
    `ensures` holds at the logged return and no thread is stopped at a
    `logik` check.
  * `ziel_ort_ganz_zeuge`: the concurrent program `zP` (`ZielOrtZeuge.lean`):
    every premise jointly, and thread 0's `lies` returns the value `100`
    thread 1 wrote, with its `ensures` at that return, from `ziel_ort_ganz`.
  * `ziel_ort_ganz_schleife`: a program WITH a loop whose invariant reads
    the shared table (`konto[0] <= 100`): `KeineLogik` proved against every
    handler and oracle, all premises jointly, and a reached machine whose
    head stands at the `traverse` boundary -- where the goal theorem says
    the invariant holds.
  * `ziel_ort_ganz_ax_zeuge`: the axiom program `axP` (`AxiomVertrag.lean`)
    with the declared ensures of its axiom: callee frames, axiom ensures
    and the check conjunct in the one theorem, on a contract no frame-only
    obligation proves.
  * PROBE A of the verdict (`messung/URTEIL-OPUS-2026-09-13.md` §2),
    reconstructed: `paP` gives every function `ensures false` and the body
    `traverse () invariant false {}; return`. `ziel_ort_rahmen` certifies
    it (`paP_rahmen_zertifiziert`); the new obligation fails on it
    (`paP_nicht_ganz`), and so does the new conclusion on a reachable machine
    (`paP_halt`): the stuck state is now a refutation, not a certificate.
-/
module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge.Teil2
