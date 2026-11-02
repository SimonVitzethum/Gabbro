module

public import Grammatik.Code.Refine.Struct.Mono
public import Grammatik.Code.Refine.Struct.LblWf

@[expose] public section


/-
  File:      Grammatik/Code/Refine/Struct/Labels/Teil3.lean
  Subject:   TRACK L, PHASE L1 -- THE LABELS OF THE C11 REQUIRED NARROWING.

  `Block/Endblock.narrowRequired` lowers like `narrow`, with the failure leg replaced by a single
  unreachable trap block at `st.l` (out of range is `Logik.kapazitaet`, excluded by the caller's
  capacity duty). The two helpers below assemble `LblWf` for that shape from the label facts of
  the rest; the continuation induction is an explicit hypothesis, as in `Labels.Teil1`.
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)

variable [Conf] {D : Deklaration}

variable {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerB_lbl_narrowRequired (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (lo)
    (hi)
    (Λ)
    (e)
    (lo')
    (hi')
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (hlt : (lb : Nat) < st.l)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_lbl_rest : ∀ (cenv' : List Reg) (lb : Lbl) (k : Lbl) (st : St) (st' : St) (blks : List Block), (lb : Nat) < st.l → lowerB lay cenv' lv rest lb k st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks := by
  simp only [lowerB] at h
  rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
    _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  simp only [hc] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
  · simp only [hv, reduceCtorEq] at h
  simp only [hv] at h
  rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have W1 : (([(⟨st.l, [], [], .dead⟩ : Block)] : List Block).map Block.lbl).Nodup ∧
      ∀ x ∈ ([(⟨st.l, [], [], .dead⟩ : Block)] : List Block), x.nl = st.l ∨ (st.l + 3 ≤ x.nl ∧ x.nl < (⟨r4, st.l + 3⟩ : St).l) := by
    refine ⟨by simp only [List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self], ?_⟩
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact Or.inl rfl
  obtain ⟨m2, n2, a2⟩ := ih_lowerB_lbl_rest (a :: cenv) (st.l + 2) k ⟨r4, st.l + 3⟩ s2 br
    (by show (st.l + 2 : Nat) < st.l + 3; omega) hb2
  exact lw_narrow (b0 := ⟨lb, [], cc, .br oc (st.l + 1) st.l⟩) (b1 := ⟨st.l + 1, [], ce ++ cv ++ cb, .jmp (st.l + 2)⟩)
    rfl rfl hlt (Nat.le_refl _) m2 ⟨W1.1, W1.2⟩ ⟨n2, a2⟩

set_option linter.unusedSectionVars false in
theorem lowerEnd_lbl_narrowRequired (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (Λ)
    (e)
    (lo')
    (hi')
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (hlt : (lb : Nat) < st.l)
    (h : lowerEnd lay cenv lv (Gabbro.Grammatik.Endblock.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (ih_lowerEnd_lbl_rest : ∀ (cenv' : List Reg) (lb : Lbl) (st : St) (st' : St) (blks : List Block), (lb : Nat) < st.l → lowerEnd lay cenv' lv rest lb st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks := by
  simp only [lowerEnd] at h
  rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
    _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  simp only [hc] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
  · simp only [hv, reduceCtorEq] at h
  simp only [hv] at h
  rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hb2 : lowerEnd lay (a :: cenv) lv rest (st.l + 2) ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have W1 : (([(⟨st.l, [], [], .dead⟩ : Block)] : List Block).map Block.lbl).Nodup ∧
      ∀ x ∈ ([(⟨st.l, [], [], .dead⟩ : Block)] : List Block), x.nl = st.l ∨ (st.l + 3 ≤ x.nl ∧ x.nl < (⟨r4, st.l + 3⟩ : St).l) := by
    refine ⟨by simp only [List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self], ?_⟩
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact Or.inl rfl
  obtain ⟨m2, n2, a2⟩ := ih_lowerEnd_lbl_rest (a :: cenv) (st.l + 2) ⟨r4, st.l + 3⟩ s2 br
    (by show (st.l + 2 : Nat) < st.l + 3; omega) hb2
  exact lw_narrow (b0 := ⟨lb, [], cc, .br oc (st.l + 1) st.l⟩) (b1 := ⟨st.l + 1, [], ce ++ cv ++ cb, .jmp (st.l + 2)⟩)
    rfl rfl hlt (Nat.le_refl _) m2 ⟨W1.1, W1.2⟩ ⟨n2, a2⟩

end Gabbro.Code.Lower
