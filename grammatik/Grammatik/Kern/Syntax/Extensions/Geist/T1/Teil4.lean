module

public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Geist
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_next {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (zz1)
    (zr_h : g001End (.next zz1 : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.next zz1 : Endblock D V l Γ Λ))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
  exact (List.not_mem_nil ho').elim

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_cons {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (zr_h : g001End (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ))
    (ih_g001Stmt_korrekt_s : ∀ (h : g001Stmt s = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.stmtOrte s), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001Stmt s && g001End rest) = true := h
  have ho' : o ∈ Extraktion.stmtOrte s ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((g001Stmt s) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact ih_g001Stmt_korrekt_s h1.1 o ho'
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bind {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (zr_h : g001End (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ))
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

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindCall {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (zz1)
    (zz2)
    (rest)
    (zr_h : g001End (.bindCall (τ := zi_τ) a args he zz1 zz2 rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindCall (τ := zi_τ) a args he zz1 zz2 rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindCallElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (zr_h : g001End (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Endblock D V l Γ Λ))
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

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindCallIndElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    {zi_τ}
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (zr_h : g001End (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001End err && g001End rest) = true := h
  have ho2 : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) (p.orte ++ args.orte) && g001End err) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  have ho' : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.endblockOrte rest := by
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
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindAxiom {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (zr_h : g001End (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindAxiomElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
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
    (zr_h : g001End (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ))
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

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_regRead {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (zr_h : g001End (.regRead r hk rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.regRead r hk rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (g001End rest) = true := h
  have ho' : o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  exact ih_g001End_korrekt_rest h0 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_regReadElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (zr_h : g001End (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) zusage.orte && g001End sonst && g001End rest) = true := h
  have ho' : o ∈ zusage.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) zusage.orte && g001End sonst) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) zusage.orte) = true) ∧ ((g001End sonst) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_sonst h2.2 o ho'
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_awaits {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (zr_h : g001End (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) [Sum.inr g] && g001End rest) = true := h
  have ho' : o = Sum.inr g ∨ o ∈ ([] : List (D.Tab ⊕ D.Glob)) ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) [Sum.inr g]) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with rfl | ho' | ho'
  · simp only [orteOk, List.all_eq_true, List.mem_singleton] at h1
    have hg' := h1.1 _ rfl
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hg'
    exact nge_of_eq_false hg'
  · exact (List.not_mem_nil ho').elim
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindCallInd {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    {zi_τ}
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (zr_h : g001End (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001End rest) = true := h
  have ho2 : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have ho' : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.endblockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ p.orte ++ args.orte := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_narrow {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (zr_h : g001End (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_sonst : ∀ (h : g001End sonst = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte sonst), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
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

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_narrowRequired {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (zr_h : g001End (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ))
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

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_exchange {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (zr_h : g001End (.exchange g neu hw hL rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.exchange g neu hw hL rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) ([Sum.inr g] ++ neu.orte) && g001End rest) = true := h
  have ho2 : o = Sum.inr g ∨ o ∈ neu.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have ho' : (o = Sum.inr g ∨ o ∈ neu.orte) ∨ o ∈ Extraktion.endblockOrte rest := by
    rcases ho2 with ho2 | ho2 | ho2
    · exact Or.inl (Or.inl ho2)
    · exact Or.inl (Or.inr ho2)
    · exact Or.inr ho2
  have h1 : ((orteOk (D := D) ([Sum.inr g] ++ neu.orte)) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · have ho2 : o ∈ ([Sum.inr g] ++ neu.orte) := by
      simpa [List.mem_append] using ho'
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
  · exact ih_g001End_korrekt_rest h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_ite {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (zr_h : g001End (.ite c t e : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.ite c t e : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_e : ∀ (h : g001End e = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte e), ¬ istGeist (D := D) o)
    (ih_g001End_korrekt_t : ∀ (h : g001End t = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte t), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) c.orte && g001End t && g001End e) = true := h
  have ho' : o ∈ c.orte ∨ o ∈ Extraktion.endblockOrte e ∨ o ∈ Extraktion.endblockOrte t := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) c.orte && g001End t) = true) ∧ ((g001End e) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) c.orte) = true) ∧ ((g001End t) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001End_korrekt_e h1.2 o ho'
  · exact ih_g001End_korrekt_t h2.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001End_korrekt_bindAxiomOpt {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_e}
    (a)
    (args)
    (he)
    (hp)
    (hd)
    (hgd)
    (rest)
    (zr_h : g001End (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.endblockOrte (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ))
    (ih_g001End_korrekt_rest : ∀ (h : g001End rest = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte rest), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte && g001End rest) = true := h
  have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte rest := by
    simpa [Extraktion.endblockOrte] using ho
  have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End rest) = true) :=
    Bool.and_eq_true_iff.mp h0
  rcases ho' with ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
  · exact ih_g001End_korrekt_rest h1.2 o ho'

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
