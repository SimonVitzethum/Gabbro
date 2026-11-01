module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Korpus.Referenz.Referenz104Rahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem ziel_ort_ganz_vertrag_zeuge :
    (∀ f : axD.Fn, KoerperGutRQ axP 0 axQ f) ∧
    ∀ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M →
      VertragAmOrtG axP M :=
  ⟨fun f => (axP_koerperZ f).1,
    ziel_ort_ganz_vertrag axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_lokal axO_vertrag
      axQ_lokal axFs_voll (programmImFragmentG_of_V axP axFs axP_fragment)
      (fussOrtGB_of_V axP axFs axP_fragment axP_fuss) (fun f => (axP_koerperZ f).1) axP_start
      axInit_exklusiv⟩

/-- **`ziel_ort_voll_ax_lokal_aus_ganz_zeuge`** -- the premises of
    `ziel_ort_voll_ax` (plus `RegLokal`) jointly on `axP`, through the new
    derivation. -/
theorem ziel_ort_voll_ax_lokal_aus_ganz_zeuge :
    ∀ M : RufMaschineG axD, RufErreichbarG axP axO 0 (RufStartG axP axSp axInit) M →
      VertragAmOrtG axP M :=
  ziel_ort_voll_ax_lokal_aus_ganz axP axO 0 axQ axFs axSp axInit axE0 axO_gut axO_lokal axO_vertrag
    axQ_lokal axFs_voll axP_fragment axP_fuss axP_koerperA axP_start axInit_exklusiv

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_ganz` jointly on four programs
  -- the corpus program 104 (`ziel_ort_ganz_ref104`: memory `0 -> 100`,
  `ensures` of `einzahlen` at its logged return), the concurrent `zP`
  (`ziel_ort_ganz_zeuge`: a cross-thread return of `100` with its
  `ensures`), the axiom program `axP` with a declared axiom ensures
  (`ziel_ort_ganz_ax_zeuge`), and a loop program `lP` whose invariant reads
  the shared table (`ziel_ort_ganz_schleife`, `ziel_ort_ganz_fortschritt_zeuge`:
  a reached machine at the `traverse` boundary, the invariant from the
  theorem, and a step from the progress conjunct). Probe A of the verdict:
  certified by `ziel_ort_rahmen` (`paP_rahmen_zertifiziert`), refuted by
  the new obligation (`paP_nicht_ganz`) and by the new conclusion on a
  reachable machine (`paP_halt`).

  What is NOT covered: every contract of `lP` is `true` (the loop fixture
  shows the check, the other three the contracts); no witness reaches a
  `state` transition (`zD` declares no transition); the non-existence of a
  step at probe A's stuck machine is shown through the conclusion
  (`KeinLogikHaltG` fails there), not by inverting the step relation.
-/

#print axioms Gabbro.Grammatik.lP_koerperZ
#print axioms Gabbro.Grammatik.ziel_ort_ganz_schleife
#print axioms Gabbro.Grammatik.ziel_ort_ganz_fortschritt_zeuge

#print axioms Gabbro.Grammatik.ziel_ort_ganz_ref104
#print axioms Gabbro.Grammatik.ziel_ort_ganz_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_ganz_ax_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_ganz_vertrag_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_lokal_aus_ganz_zeuge
#print axioms Gabbro.Grammatik.paP_rahmen_zertifiziert
#print axioms Gabbro.Grammatik.paP_nicht_ganz
#print axioms Gabbro.Grammatik.paP_halt

end Gabbro.Grammatik
