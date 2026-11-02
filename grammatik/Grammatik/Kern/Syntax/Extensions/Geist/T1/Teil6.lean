module

public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindCallIndElse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_n}
    {zi_τ}
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (zr_h : g001 (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001End err && g001 rest) = true := h
  have ho2 : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) (p.orte ++ args.orte) && g001End err) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  have ho' : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.blockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr (Or.inl ho2)
    · exact Or.inr (Or.inr ho2)
  rcases ho' with ho' | ho' | ho'
  · have ho3 : o ∈ p.orte ++ args.orte := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho3)
  · exact ih_g001End_korrekt_err h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

end Gabbro.Grammatik.Geist
