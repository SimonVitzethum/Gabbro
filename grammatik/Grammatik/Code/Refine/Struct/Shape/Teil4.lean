module

public import Grammatik.Code.Refine.Struct.Mono
public import Grammatik.Code.Refine.Struct.Shape.Teil1
public import Grammatik.Code.Refine.Struct.Shape.Teil2

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}
variable {V : Vertrag D}

set_option linter.unusedSectionVars false in
/-- The shape of a `traverse` lowering, given the shape of the lowered body: the entry block, the
    three counter blocks and the body. -/
theorem lowerS_shape_traverse (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.traverse (Λ := Λ) t inv body : Gabbro.Grammatik.Stmt D V l Γ Λ Λ) lb k st = some (blks, st'))
    (ih_lowerB_shape_body : ∀ (a : Reg) (st1 st1' : St) (bb : List Block), lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) st1 = some (bb, st1') → Shape (st.l + 3) st1 st1' bb)
    : Shape lb st st' blks := by
  simp only [lowerS] at h
  by_cases hc : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
  · simp only [hc, and_self, if_true] at h
    rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
      _ | ⟨cv, ov, r1⟩
    · simp only [hv, reduceCtorEq] at h
    have m1 := cvtG_mono hv
    simp only [hv] at h
    rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
    · simp only [hb, reduceCtorEq] at h
    have m2 := bindCode_mono hb
    simp only [hb] at h
    rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
      _ | ⟨bb, s1⟩
    · simp only [hb2, reduceCtorEq] at h
    have S2 := ih_lowerB_shape_body a ⟨r2, st.l + 4⟩ s1 bb hb2
    simp only [hb2] at h
    have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | rfl | rfl | hb
      · rfl
      · rfl
      · rfl
      · rfl
      · exact S2.2.1 b hb
    · have a2 := S2.2.2
      simp only at m1 m2 a2 ⊢
      omega
  · simp only [hc, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
/-- The shape of a C11 consuming traversal: the same four counter blocks and body as `traverse`
    (re-selection is OPEN; the placeholder runs the same fixed sweep). -/
theorem lowerS_shape_consumeTraverse (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (member)
    (edge)
    (inv)
    (bound)
    (mass)
    (body)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.consumeTraverse (Λ := Λ) t member edge inv bound mass body : Gabbro.Grammatik.Stmt D V l Γ Λ Λ) lb k st = some (blks, st'))
    (ih_lowerB_shape_body : ∀ (a : Reg) (st1 st1' : St) (bb : List Block), lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) st1 = some (bb, st1') → Shape (st.l + 3) st1 st1' bb)
    : Shape lb st st' blks := by
  simp only [lowerS, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
/-- The shape of a C11 required narrowing in a block: the `narrow` test and bind blocks, an
    unreachable trap for the failure leg, and the rest. -/
theorem lowerB_shape_narrowRequired (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (lo)
    (hi)
    (e)
    (lo')
    (hi')
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_shape_rest : ∀ (a : Reg) (st1 st1' : St) (br : List Block), lowerB lay (a :: cenv) lv rest (st.l + 2) k st1 = some (br, st1') → Shape (st.l + 2) st1 st1' br)
    : Shape lb st st' blks := by
  simp only [lowerB] at h
  rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
    _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  have m1 := lowerE_mono lay cenv _ st.r _ hc
  simp only [hc] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  have m2 := lowerE_mono lay cenv e r1 _ he
  simp only [he] at h
  rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
  · simp only [hv, reduceCtorEq] at h
  have m3 := cvtG_mono hv
  simp only [hv] at h
  rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
  · simp only [hb, reduceCtorEq] at h
  have m4 := bindCode_mono hb
  simp only [hb] at h
  rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  have S1 : Shape st.l ⟨r4, st.l + 3⟩ ⟨r4, st.l + 3⟩ ([⟨st.l, [], [], .dead⟩] : List Block) := by
    refine ⟨⟨_, _, rfl, rfl⟩, ?_, Nat.le_refl _⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    rfl
  have S2 := ih_lowerB_shape_rest a ⟨r4, st.l + 3⟩ s2 br hb2
  simp only [hb2] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | rfl | hb | hb
    · rfl
    · rfl
    · exact S1.2.1 b (List.mem_singleton.mpr hb)
    · exact S2.2.1 b hb
  · have a1 := S1.2.2
    have a2 := S2.2.2
    simp only at m1 m2 m3 m4 a1 a2 ⊢
    omega

set_option linter.unusedSectionVars false in
/-- The shape of a C11 required narrowing at the top level of a body: the same test, bind and
    trap blocks, with an end-block rest. -/
theorem lowerEnd_shape_narrowRequired (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (e)
    (lo')
    (hi')
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (Gabbro.Grammatik.Endblock.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (ih_lowerEnd_shape_rest : ∀ (a : Reg) (st1 st1' : St) (br : List Block), lowerEnd lay (a :: cenv) lv rest (st.l + 2) st1 = some (br, st1') → Shape (st.l + 2) st1 st1' br)
    : Shape lb st st' blks := by
  simp only [lowerEnd] at h
  rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
    _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  have m1 := lowerE_mono lay cenv _ st.r _ hc
  simp only [hc] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  have m2 := lowerE_mono lay cenv e r1 _ he
  simp only [he] at h
  rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
  · simp only [hv, reduceCtorEq] at h
  have m3 := cvtG_mono hv
  simp only [hv] at h
  rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
  · simp only [hb, reduceCtorEq] at h
  have m4 := bindCode_mono hb
  simp only [hb] at h
  rcases hb2 : lowerEnd lay (a :: cenv) lv rest (st.l + 2) ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  have S1 : Shape st.l ⟨r4, st.l + 3⟩ ⟨r4, st.l + 3⟩ ([⟨st.l, [], [], .dead⟩] : List Block) := by
    refine ⟨⟨_, _, rfl, rfl⟩, ?_, Nat.le_refl _⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    rfl
  have S2 := ih_lowerEnd_shape_rest a ⟨r4, st.l + 3⟩ s2 br hb2
  simp only [hb2] at h
  have := Option.some.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | rfl | hb | hb
    · rfl
    · rfl
    · exact S1.2.1 b (List.mem_singleton.mpr hb)
    · exact S2.2.1 b hb
  · have a1 := S1.2.2
    have a2 := S2.2.2
    simp only at m1 m2 m3 m4 a1 a2 ⊢
    omega

end Gabbro.Code.Lower
