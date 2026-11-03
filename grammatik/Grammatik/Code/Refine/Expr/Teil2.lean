module

public import Grammatik.Code.Refine.Env
public import Grammatik.Code.Refine.Match.Opt
public import Grammatik.Code.Refine.Match.Case
public import Grammatik.Code.Refine.Bits.Forms
public import Grammatik.Code.Refine.Expr.Teil1Pointer

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Env Wert Ctx Var World Res eval Zahl)
variable {D : Deklaration}

set_option linter.unusedSectionVars false in
theorem lowerE_ok_sub (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (l1 - h2) (h1 - l2))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int (l1 - h2) (h1 - l2)) (eval σ₀ (.sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (l1 - h2) (h1 - l2))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int (l1 - h2) (h1 - l2)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : binRest .sub (ety (Expr.sub a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (binRest_fits hbr)⟩
  exact binRest_frag .sub (fun a b => a - b) val_bin_sub (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_mul (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.mul (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int   (Gabbro.Grammatik.imin (Gabbro.Grammatik.imin (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imin (h1 * l2) (h1 * h2)))   (Gabbro.Grammatik.imax (Gabbro.Grammatik.imax (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imax (h1 * l2) (h1 * h2))))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int   (Gabbro.Grammatik.imin (Gabbro.Grammatik.imin (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imin (h1 * l2) (h1 * h2)))   (Gabbro.Grammatik.imax (Gabbro.Grammatik.imax (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imax (h1 * l2) (h1 * h2)))) (eval σ₀ (.mul (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int   (Gabbro.Grammatik.imin (Gabbro.Grammatik.imin (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imin (h1 * l2) (h1 * h2)))   (Gabbro.Grammatik.imax (Gabbro.Grammatik.imax (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imax (h1 * l2) (h1 * h2))))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int   (Gabbro.Grammatik.imin (Gabbro.Grammatik.imin (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imin (h1 * l2) (h1 * h2)))   (Gabbro.Grammatik.imax (Gabbro.Grammatik.imax (l1 * l2) (l1 * h2)) (Gabbro.Grammatik.imax (h1 * l2) (h1 * h2)))) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : binRest .mul (ety (Expr.mul a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (binRest_fits hbr)⟩
  exact binRest_frag .mul (fun a b => a * b) val_bin_mul (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_neg (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (a)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.neg (lo := lo) (hi := hi) a : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-hi) (-lo))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int lo hi) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int lo hi))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int (-hi) (-lo)) (eval σ₀ (.neg (lo := lo) (hi := hi) a : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-hi) (-lo))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int (-hi) (-lo)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hbr : binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1
    with _ | ⟨ct, ot, r2⟩
  · simp only [hbr, reduceCtorEq] at h
  simp only [hbr] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  refine ⟨frag_two (ct := (ct, ot, r2)) Ia (fun rsA hag hoa hlta => ?_), fitsT_of (binRest_fits hbr)⟩
  have T := binRest_frag .sub (fun a b => a - b) val_bin_sub (la := 0) (ha := 0) (lb := lo)
    (hb := hi) 0 (eval σ₀ a σ ρ).n (by decide) (Ifa lo hi rfl) (Int.le_refl _) (Int.le_refl _)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (.int (twid (.int 0 0)) 0) oa r1 m rsA rfl hoa
    (fun x hx => nomatch hx) hlta (ct, ot, r2) hbr
  rw [Int.zero_sub] at T
  exact T

set_option linter.unusedSectionVars false in
theorem lowerE_ok_lt (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : cmpRest .ult .slt (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  exact cmpRest_frag .ult .slt (fun a b => a < b) (fun sg W a b hW ha hb => val_icmp_lt sg W a b hW ha hb)
    (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_le (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : cmpRest .ule .sle (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  exact cmpRest_frag .ule .sle (fun a b => a ≤ b) (fun sg W a b hW ha hb => val_icmp_le sg W a b hW ha hb)
    (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_eq (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : cmpRest .eq .eq (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  exact cmpRest_frag .eq .eq (fun a b => a = b) (fun sg W a b hW ha hb => val_icmp_eq sg W a b hW ha hb)
    (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_and (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.and a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.and a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, _⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  refine ⟨frag_three (ct := ([.bin r2 .and 1 oa ob], .reg r2, r2 + 1)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  have hoa' : oa.ev rsB = some (Val.bool (eval σ₀ a σ ρ)) := hoa
  have hob' : ob.ev rsB = some (Val.bool (eval σ₀ b σ ρ)) := hob
  have hv := val_bin_and (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  exact frag_one m rsB r2 (.bin r2 .and 1 oa ob) (Val.bool (eval σ₀ a σ ρ && eval σ₀ b σ ρ)) (by
    simp only [stepI, hoa', hob', hv]
    rfl)

set_option linter.unusedSectionVars false in
theorem lowerE_ok_or (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.or a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.or a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, _⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  refine ⟨frag_three (ct := ([.bin r2 .or 1 oa ob], .reg r2, r2 + 1)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  have hoa' : oa.ev rsB = some (Val.bool (eval σ₀ a σ ρ)) := hoa
  have hob' : ob.ev rsB = some (Val.bool (eval σ₀ b σ ρ)) := hob
  have hv := val_bin_or (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  exact frag_one m rsB r2 (.bin r2 .or 1 oa ob) (Val.bool (eval σ₀ a σ ρ || eval σ₀ b σ ρ)) (by
    simp only [stepI, hoa', hob', hv]
    rfl)

set_option linter.unusedSectionVars false in
theorem lowerE_ok_not (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.not a : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.not a : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, _⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  refine ⟨frag_two (ct := ([.bin r1 .xor 1 oa (.int 1 1)], .reg r1, r1 + 1)) Ia (fun rsA hag hoa hlta => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
  have hoa' : oa.ev rsA = some (Val.bool (eval σ₀ a σ ρ)) := hoa
  have hv := val_bin_not (eval σ₀ a σ ρ)
  exact frag_one m rsA r1 (.bin r1 .xor 1 oa (.int 1 1)) (Val.bool (!eval σ₀ a σ ρ)) (by
    have e1 : (Opd.int 1 1).ev rsA = some (Val.ofInt 1 1) := rfl
    simp only [stepI, hoa', e1, hv]
    rfl)

end Gabbro.Code.Lower
