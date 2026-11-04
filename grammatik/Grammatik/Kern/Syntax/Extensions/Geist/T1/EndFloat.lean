module
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil3
@[expose] public section
namespace Gabbro.Grammatik.Geist
variable {D : Deklaration} {V : Vertrag D}

theorem g001End_korrekt_float {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (zr_h : g001End (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (a.orte ++ b.orte) && g001End rest) = true := h
  have ho2 : o ∈ a.orte ∨ o ∈ b.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have ho' : (o ∈ a.orte ∨ o ∈ b.orte) ∨ o ∈ Extraktion.endblockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) (a.orte ++ b.orte)) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ a.orte ++ b.orte := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001End_korrekt_rest h1.2 o ho'

theorem g001End_korrekt_floatLit {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (zr_h : g001End (.floatLit q lo hi rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.floatLit q lo hi rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001End rest) = true := h
  have ho' : o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  exact ih_g001End_korrekt_rest h0 o ho'

theorem g001End_korrekt_floatOf {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (zr_h : g001End (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001End rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001End_korrekt_rest h1.2 o ho'

theorem g001End_korrekt_floatNarrow {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (zr_h : g001End (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001End sonst && g001End rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte && g001End sonst) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001End_korrekt_rest h1.2 o ho'

end Gabbro.Grammatik.Geist
