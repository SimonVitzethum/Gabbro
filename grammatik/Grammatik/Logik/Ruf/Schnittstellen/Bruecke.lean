module

public import Grammatik.Logik.Ruf.Schnittstellen.Pruefung
public import Grammatik.Zielsatz.Kern.Spec.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Akzeptiert wiring for pointer-interface conformance (C06, O43)

  The footprint and call-graph legs live in `Pruefung` (`ptr_vertrag_darf`,
  `ptr_vertrag_stabil`, `ptrVertragsFreiB_ok`, `abgK_indirekt_schliesst`):
  interface pre/post orte already ride every indirect site
  (`blockOrteP`/`endblockOrteP`), and `rufM`/`AbgK` already close over
  admitted targets. These bridges instantiate those legs at the checker's
  fields (`AkzeptiertSpec.fuss`, `AkzeptiertSpec.abg`), so the goal legs
  (`ZielOrtAx`, `ZielOrtRahmen`, `ZielOrtSperre`, atomic replay) read them
  off the accepted unit. The universal refinement itself stays user proof
  in `LogikPflicht`/`LogikPflichtA`, never a Bool. `gabbro_ziel` is
  untouched: it quantifies over every program, so nontrivial `ptrVertrag`
  needed no new case. -/

variable {D : Deklaration} [DecidableEq D.Fn]

/-- From the checker's footprint field: a pointer contract's carriers are
    stable at an indirect call whose interface orte lie in the widened
    footprint. -/
theorem ptr_stabil_aus_akzeptiert {P : Programm D} {S : SperrInv D}
    {fs ws : List D.Fn} {A : List (Kernzelle.AccumulatorDecl D)}
    (h : Zielsatz.AkzeptiertSpec P S fs ws A) {f : D.Fn}
    {V : Vertrag D} {Λ : List (Res D)} {n : Nat}
    (hp : RufPasst D V (D.sigNr n) Λ)
    (hsub : (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte ⊆ fussOrteG P f) :
    (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte ⊆
      stabilS P S (Zielsatz.lokW P fs ws) f Λ :=
  ptr_vertrag_stabil (h.fuss f) hp hsub

/-- From the checker's closure field: an admitted target of an indirect
    site in the closed set is itself in the set. -/
theorem abgK_ptr_aus_akzeptiert {P : Programm D} {S : SperrInv D}
    {fs ws : List D.Fn} {A : List (Kernzelle.AccumulatorDecl D)}
    (h : Zielsatz.AkzeptiertSpec P S fs ws A)
    {w f : D.Fn} (hf : (reachB P fs w) f = true) {n : Nat}
    (hsite : (rufM fs (reachB P fs w)).ind n = true) {g : D.Fn}
    (hg : D.passt g n = true) (hvoll : ∀ g : D.Fn, g ∈ fs) :
    (reachB P fs w) g = true :=
  abgK_indirekt_schliesst (h.abg w) hf hsite hg hvoll

/-- The decided freeness check discharges the pointer half of
    `VertragsFrei`: no shared atomic hides in an interface contract. -/
theorem ptr_frei_aus_bool {P : Programm D} {ns : List Nat} {c : D.Tab ⊕ D.Glob}
    (htriv : ∀ n, n ∉ ns →
      (P.ptrVertrag n).pre.orte = [] ∧ (P.ptrVertrag n).post.orte = [])
    (h : ptrVertragsFreiB P ns c = true) : PtrVertragsFrei P c :=
  ptrVertragsFreiB_ok htriv h

end Gabbro.Grammatik
