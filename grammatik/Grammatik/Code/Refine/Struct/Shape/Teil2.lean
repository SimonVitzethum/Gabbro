module

public import Grammatik.Code.Refine.Struct.Mono
public import Grammatik.Code.Refine.Struct.Shape.Teil1

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}
variable {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerS_shape_call (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (f)
    (args)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.call f args zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  have m1 := lowerArgs_mono lay cenv args st.r _ hla
  simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], ?_⟩
  simp only at m1 ⊢
  omega

set_option linter.unusedSectionVars false in
theorem lowerB_shape_nil (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.nil : Gabbro.Grammatik.Block D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerB] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩

set_option linter.unusedSectionVars false in
theorem lowerB_shape_cons (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerS_shape_s : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerS lay cenv lv s lb k st = some (blks, st') → Shape lb st st' blks)
    (ih_lowerB_shape_rest : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv rest lb k st = some (blks, st') → Shape lb st st' blks)
    : Shape lb st st' blks :=
  by
  simp only [lowerB] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  have S1 := ih_lowerS_shape_s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
  simp only [hs] at h
  rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  have S2 := ih_lowerB_shape_rest st.l k s1 s2 b2 hr
  simp only [hr] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨⟨hd, tl, hdt, hl⟩, hp, hm⟩ := S1
  refine ⟨⟨hd, tl ++ b2, by rw [hdt]; rfl, hl⟩, ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hp b hb
    · exact S2.2.1 b hb
  · have a2 := S2.2.2
    simp only at hm a2 ⊢
    omega

set_option linter.unusedSectionVars false in
theorem lowerB_shape_check (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.check c sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_shape_rest : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv rest lb k st = some (blks, st') → Shape lb st st' blks)
    (ih_lowerEnd_shape_sonst : ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv sonst lb st = some (blks, st') → Shape lb st st' blks)
    : Shape lb st st' blks :=
  by
  simp only [lowerB] at h
  rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  have m1 := lowerE_mono lay cenv c st.r _ hc
  simp only [hc] at h
  rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  have S1 := ih_lowerEnd_shape_sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  have S2 := ih_lowerB_shape_rest (st.l + 1) k s1 s2 br hb2
  simp only [hb2] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | hb | hb
    · rfl
    · exact S1.2.1 b hb
    · exact S2.2.1 b hb
  · have a1 := S1.2.2
    have a2 := S2.2.2
    simp only at m1 a1 a2 ⊢
    omega

set_option linter.unusedSectionVars false in
theorem lowerEnd_shape_cons (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (ih_lowerS_shape_s : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerS lay cenv lv s lb k st = some (blks, st') → Shape lb st st' blks)
    (ih_lowerEnd_shape_rest : ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv rest lb st = some (blks, st') → Shape lb st st' blks)
    : Shape lb st st' blks :=
  by
  simp only [lowerEnd] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  have S1 := ih_lowerS_shape_s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
  simp only [hs] at h
  rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  have S2 := ih_lowerEnd_shape_rest st.l s1 s2 b2 hr
  simp only [hr] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨⟨hd, tl, hdt, hl⟩, hp, hm⟩ := S1
  refine ⟨⟨hd, tl ++ b2, by rw [hdt]; rfl, hl⟩, ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hp b hb
    · exact S2.2.1 b hb
  · have a2 := S2.2.2
    simp only at hm a2 ⊢
    omega

set_option linter.unusedSectionVars false in
theorem lowerAr_shape_nil (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat) (ov : Opd)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerAr lay cenv lv top W L ov (.nil : Gabbro.Grammatik.Arms D V l Γ Λ _ _) lb k st = some (blks, st'))
    : (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r :=
  by
  simp only [lowerAr, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by simp only [List.not_mem_nil, false_implies, implies_true], Nat.le_refl _⟩

set_option linter.unusedSectionVars false in
theorem lowerGA_shape_nil (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerGA lay cenv lv (.nil : Gabbro.Grammatik.GrundArms D V l Γ Λ _ _) lb k st = some (blks, st'))
    : (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r :=
  by
  simp only [lowerGA, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by simp only [List.not_mem_nil, false_implies, implies_true], Nat.le_refl _⟩

end Gabbro.Code.Lower
