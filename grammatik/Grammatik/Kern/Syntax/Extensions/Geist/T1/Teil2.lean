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
theorem g001Stmt_korrekt_publish {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (e)
    (payload)
    (hp)
    (hw)
    (hL)
    (zr_h : g001Stmt (.publish g e payload hp hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.publish g e payload hp hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (hΛ)
    (zr_h : g001Stmt (.ret e hΛ : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.ret e hΛ : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_transition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (m)
    (hm)
    (hl)
    (maske)
    (bits)
    (zr_h : g001Stmt (.transition r hk m hm hl maske bits : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.transition r hk m hm hl maske bits : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hΛ)
    (zr_h : g001Stmt (.retWhy r hΛ : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.retWhy r hΛ : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_retScoped {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (R)
    (zr_h : g001Stmt (.retScoped e R : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.retScoped e R : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_retWhyScoped {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (R)
    (zr_h : g001Stmt (.retWhyScoped r R : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.retWhyScoped r R : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_onOption {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_n}
    (opt)
    (p)
    (a)
    (zr_h : g001Stmt (.onOption (n := zi_n) opt p a : Stmt D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.onOption (n := zi_n) opt p a : Stmt D V l Γ Λ Λ'))
    (ih_g001_korrekt_p : ∀ (h : g001 p = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte p), ¬ istGeist (D := D) o)
    (ih_g001_korrekt_a : ∀ (h : g001 a = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte a), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) opt.orte && g001 p && g001 a) = true := h
  have ho' : o ∈ opt.orte ∨ o ∈ Extraktion.blockOrte p ∨ o ∈ Extraktion.blockOrte a := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) opt.orte && g001 p) = true) ∧ ((g001 a) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) opt.orte) = true) ∧ ((g001 p) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001_korrekt_p h2.2 o ho'
  · exact ih_g001_korrekt_a h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_onTag {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (zr_h : g001Stmt (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ'))
    (ih_g001Arms_korrekt_arms : ∀ (h : g001Arms arms = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.armsOrte arms), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) v.orte && g001Arms arms) = true := h
  have ho' : o ∈ v.orte ∨ o ∈ Extraktion.armsOrte arms := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) v.orte) = true) ∧ ((g001Arms arms) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001Arms_korrekt_arms h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_onWhy {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (zr_h : g001Stmt (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ'))
    (ih_g001Grund_korrekt_arms : ∀ (h : g001Grund arms = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.grundArmsOrte arms), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) r.orte && g001Grund arms) = true := h
  have ho' : o ∈ r.orte ∨ o ∈ Extraktion.grundArmsOrte arms := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) r.orte) = true) ∧ ((g001Grund arms) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001Grund_korrekt_arms h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_locks {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (hr)
    (body)
    (zr_h : g001Stmt (.locks L hr body : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.locks L hr body : Stmt D V l Γ Λ (Λ)))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 body) = true := h
  have ho' : o ∈ Extraktion.blockOrte body := by
    simpa [Extraktion.stmtOrte] using ho
  exact ih_g001_korrekt_body h0 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_breaking {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (i)
    (body)
    (zr_h : g001Stmt (.breaking i body : Stmt D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.breaking i body : Stmt D V l Γ Λ Λ'))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001 body) = true := h
  have ho' : o ∈ Extraktion.blockOrte body := by
    simpa [Extraktion.stmtOrte] using ho
  exact ih_g001_korrekt_body h0 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_traverse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (zr_h : g001Stmt (.traverse t inv body : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.traverse t inv body : Stmt D V l Γ Λ (Λ)))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) inv.orte && g001 body) = true := h
  have ho' : o ∈ inv.orte ∨ o ∈ Extraktion.blockOrte body := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) inv.orte) = true) ∧ ((g001 body) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001_korrekt_body h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_consumeTraverse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t)
    (member)
    (edge)
    (inv)
    (bound)
    (mass)
    (body)
    (zr_h : g001Stmt (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ (Λ)))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (member.orte ++ edge.orte ++ inv.orte ++ mass.orte) && g001 body) = true := h
  have ho' : o ∈ member.orte ∨ o ∈ edge.orte ∨ o ∈ inv.orte ∨ o ∈ mass.orte ∨ o ∈ Extraktion.blockOrte body := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) (member.orte ++ edge.orte ++ inv.orte ++ mass.orte)) = true) ∧ ((g001 body) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho' | ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o (by simpa using Or.inl ho'))
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o (by simpa using Or.inr (Or.inl ho')))
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o (by simpa using Or.inr (Or.inr (Or.inl ho'))))
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o (by simpa using Or.inr (Or.inr (Or.inr ho'))))
  · exact ih_g001_korrekt_body h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_retry {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (zr_h : g001Stmt (.retry n bis body ueber : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.retry n bis body ueber : Stmt D V l Γ Λ (Λ)))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    (ih_g001_korrekt_ueber : ∀ (h : g001 ueber = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte ueber), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) bis.orte && g001 body && g001 ueber) = true := h
  have ho' : o ∈ bis.orte ∨ o ∈ Extraktion.blockOrte body ∨ o ∈ Extraktion.blockOrte ueber := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) bis.orte && g001 body) = true) ∧ ((g001 ueber) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) bis.orte) = true) ∧ ((g001 body) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001_korrekt_body h2.2 o ho'
  · exact ih_g001_korrekt_ueber h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_forever {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (zr_h : g001Stmt (.forever a inv body : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.forever a inv body : Stmt D V l Γ Λ (Λ)))
    (ih_g001_korrekt_body : ∀ (h : g001 body = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte body), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) inv.orte && g001 body) = true := h
  have ho' : o ∈ inv.orte ∨ o ∈ Extraktion.blockOrte body := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) inv.orte) = true) ∧ ((g001 body) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001_korrekt_body h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zr_h : g001 (.nil : Block D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.nil : Block D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.blockOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001_korrekt_cons {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (zr_h : g001 (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ'))
    (ih_g001Stmt_korrekt_s : ∀ (h : g001Stmt s = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.stmtOrte s), ¬ istGeist (D := D) o)
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001Stmt s && g001 rest) = true := h
  have ho' : o ∈ Extraktion.stmtOrte s ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have h1 : ((g001Stmt s) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact ih_g001Stmt_korrekt_s h1.1 o ho'
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (zr_h : g001 (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ'))
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
theorem g001_korrekt_bindCall {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (zr_h : g001 (.bindCall (τ := zi_τ) f args he hp hr rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindCall (τ := zi_τ) f args he hp hr rest : Block D V l Γ Λ Λ'))
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

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindCallInd {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_n}
    {zi_τ}
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (zr_h : g001 (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Block D V l Γ Λ Λ'))
    (ih_g001_korrekt_rest : ∀ (h : g001 rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001 rest) = true := h
  have ho2 : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.blockOrte rest := by
    simpa [Extraktion.blockOrte] using ho
  have ho' : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.blockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001 rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ p.orte ++ args.orte := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001_korrekt_bindCallElse {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (zr_h : g001 (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Block D V l Γ Λ Λ'))
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
theorem g001_korrekt_bindAxiom {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (zr_h : g001 (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.blockOrte (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ'))
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
