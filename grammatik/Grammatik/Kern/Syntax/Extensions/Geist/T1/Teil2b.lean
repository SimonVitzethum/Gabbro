module

public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindAxiomOpt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_e}
    (a)
    (args)
    (he)
    (hp)
    (hd)
    (hgd)
    (rest)
    (zr_h : g001 (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001 rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001_korrekt_rest h1.2 o ho'

end Gabbro.Grammatik.Geist
