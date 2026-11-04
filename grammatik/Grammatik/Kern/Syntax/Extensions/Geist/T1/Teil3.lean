module
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil2
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil2b

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindAxiomElse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hw)
    (hg)
    (hd)
    (hgd)
    (err)
    (rest)
    (zr_h : g001 (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End err && g001 rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte && g001End err) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_err h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_narrowRequired {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (zr_h : g001 (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001 rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindAxiomOptElse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
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
    (zr_h : g001 (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End err && g001 rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte && g001End err) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_err h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_regRead {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (zr_h : g001 (.regRead r hk rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.regRead r hk rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 rest) = true := h
  have ho' : o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  exact ih_g001_korrekt_rest h0 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_regReadElse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (zr_h : g001 (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) zusage.orte && g001End sonst && g001 rest) = true := h
  have ho' : o ∈ zusage.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) zusage.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) zusage.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_awaits {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (zr_h : g001 (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) [Sum.inr g] && g001 rest) = true := h
  have ho' : o = Sum.inr g ∨ o ∈ ([] : List (D.Tab ⊕ D.Glob)) ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) [Sum.inr g]) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with rfl | ho' | ho'
  · simp only [orteOk, List.all_eq_true, List.mem_singleton] at h1
    have hg' := h1.1 _ rfl
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hg'
    exact nge_of_eq_false hg'
  · exact (List.not_mem_nil ho').elim
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_exchange {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (zr_h : g001 (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.exchange g neu hw hL rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) ([Sum.inr g] ++ neu.orte) && g001 rest) = true := h
  have ho2 : o = Sum.inr g ∨ o ∈ neu.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have ho' : (o = Sum.inr g ∨ o ∈ neu.orte) ∨ o ∈ Extraktion.blockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) ([Sum.inr g] ++ neu.orte)) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ ([Sum.inr g] ++ neu.orte) := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_narrow {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (zr_h : g001 (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001End sonst && g001 rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_check {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (zr_h : g001 (.check c sonst rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.check c sonst rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) c.orte && g001End sonst && g001 rest) = true := h
  have ho' : o ∈ c.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) c.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) c.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_float {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
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
    (zr_h : g001 (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (a.orte ++ b.orte) && g001 rest) = true := h
  have ho2 : o ∈ a.orte ∨ o ∈ b.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have ho' : (o ∈ a.orte ∨ o ∈ b.orte) ∨ o ∈ Extraktion.blockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) (a.orte ++ b.orte)) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ a.orte ++ b.orte := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_floatLit {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (zr_h : g001 (.floatLit q lo hi rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.floatLit q lo hi rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 rest) = true := h
  have ho' : o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  exact ih_g001_korrekt_rest h0 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_floatOf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (zr_h : g001 (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001 rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_floatNarrow {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (zr_h : g001 (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte && g001End sonst && g001 rest) = true := h
  have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((orteOk (D := D) e.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Arms_korrekt_nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zr_h : g001Arms (.nil : Arms D V l Γ Λ (Λ) ([])) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.armsOrte (.nil : Arms D V l Γ Λ (Λ) ([])))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.armsOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001Arms_korrekt_cons {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b)
    (rest)
    (zr_h : g001Arms (.cons b rest : Arms D V l Γ Λ Λ' (c :: cs)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.armsOrte (.cons b rest : Arms D V l Γ Λ Λ' (c :: cs)))
    (ih_g001_korrekt_b : ∀ (h : g001 b = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte b), ¬ istGeist (D := D) o)
    (ih_g001Arms_korrekt_rest : ∀ (h : g001Arms rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.armsOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 b && g001Arms rest) = true := h
  have ho0 : o ∈ Extraktion.blockOrte b ++ Extraktion.armsOrte rest := by
    simpa [Extraktion.armsOrte] using ho
  have h1 : ((g001 b) = true) ∧ ((g001Arms rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have ho' : o ∈ Extraktion.blockOrte b ∨ o ∈ Extraktion.armsOrte rest :=
    List.mem_append.mp ho0
  rcases ho' with ho' | ho'
  · exact ih_g001_korrekt_b h1.1 o ho'
  · exact ih_g001Arms_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Grund_korrekt_nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zr_h : g001Grund (.nil : GrundArms D V l Γ Λ (Λ) (0)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.grundArmsOrte (.nil : GrundArms D V l Γ Λ (Λ) (0)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.grundArmsOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001Grund_korrekt_cons {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b)
    (rest)
    (zr_h : g001Grund (.cons b rest : GrundArms D V l Γ Λ Λ' (n + 1)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.grundArmsOrte (.cons b rest : GrundArms D V l Γ Λ Λ' (n + 1)))
    (ih_g001_korrekt_b : ∀ (h : g001 b = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte b), ¬ istGeist (D := D) o)
    (ih_g001Grund_korrekt_rest : ∀ (h : g001Grund rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.grundArmsOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 b && g001Grund rest) = true := h
  have ho0 : o ∈ Extraktion.blockOrte b ++ Extraktion.grundArmsOrte rest := by
    simpa [Extraktion.grundArmsOrte] using ho
  have h1 : ((g001 b) = true) ∧ ((g001Grund rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have ho' : o ∈ Extraktion.blockOrte b ∨ o ∈ Extraktion.grundArmsOrte rest :=
    List.mem_append.mp ho0
  rcases ho' with ho' | ho'
  · exact ih_g001_korrekt_b h1.1 o ho'
  · exact ih_g001Grund_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (zz1)
    (zr_h : g001End (.ret e zz1 : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.ret e zz1 : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.endblockOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zz1)
    (zz2)
    (zr_h : g001End (.retWhy zz1 zz2 : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.retWhy zz1 zz2 : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_retScoped {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (R)
    (zr_h : g001End (.retScoped e R : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.retScoped e R : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.endblockOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')



end Gabbro.Grammatik.Geist
