module

public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindAxiomOptElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_e}
    (a)
    (args)
    (he)
    (hr)
    (hp)
    (hd)
    (hgd)
    (err)
    (rest)
    (zr_h : g001End (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End err && g001End rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte && g001End err) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_err h2.2 o ho'
  · exact ih_g001End_korrekt_rest h1.2 o ho'

end Gabbro.Grammatik.Geist
