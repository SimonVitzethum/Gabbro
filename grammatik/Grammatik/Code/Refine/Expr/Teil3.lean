module

public import Grammatik.Code.Refine.Env
public import Grammatik.Code.Refine.Match.Opt
public import Grammatik.Code.Refine.Match.Case
public import Grammatik.Code.Refine.Bits.Forms
public import Grammatik.Code.Refine.Expr.Teil2

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Env Wert Ctx Var World Res eval Zahl)
variable {D : Deklaration}

set_option linter.unusedSectionVars false in
theorem lowerE_ok_div (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (h0)
    (h1')
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 h1) (eval σ₀ (.div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 h1) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : divRest .udiv (ety (Expr.div h0 h1' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
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
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (divRest_fits hbr)⟩
  have hza : 0 ≤ (eval σ₀ a σ ρ).n := by have := (eval σ₀ a σ ρ).lo_le; omega
  have hzb : 1 ≤ (eval σ₀ b σ ρ).n := by have := (eval σ₀ b σ ρ).lo_le; omega
  exact divRest_frag .udiv Int.tdiv (fun W a b h0 h1 h2 h3 => val_bin_udiv W a b h0 h1 h2 h3)
    (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n h0 h1' (Ifa l1 h1 rfl) (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le
    (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
    (by rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg hza]; exact Int.ediv_nonneg hza (by omega))
    (by
      rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg hza]
      have := Int.ediv_le_self (eval σ₀ b σ ρ).n hza
      have := (eval σ₀ a σ ρ).le_hi
      exact Int.le_trans (by omega) (Int.le_max_left h1 h2))
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_rem (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (h0)
    (h1')
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (h2 - 1))) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 (h2 - 1)) (eval σ₀ (.rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (h2 - 1))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 (h2 - 1)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : divRest .urem (ety (Expr.rem h0 h1' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
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
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (divRest_fits hbr)⟩
  have hza : 0 ≤ (eval σ₀ a σ ρ).n := by have := (eval σ₀ a σ ρ).lo_le; omega
  have hzb : 1 ≤ (eval σ₀ b σ ρ).n := by have := (eval σ₀ b σ ρ).lo_le; omega
  exact divRest_frag .urem Int.tmod (fun W a b h0 h1 h2 h3 => val_bin_urem W a b h0 h1 h2 h3)
    (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n h0 h1' (Ifa l1 h1 rfl) (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le
    (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
    (by rw [Int.tmod_eq_emod_of_nonneg hza]; exact Int.emod_nonneg _ (by omega))
    (by
      rw [Int.tmod_eq_emod_of_nonneg hza]
      have := Int.emod_lt_of_pos (eval σ₀ a σ ρ).n (show 0 < (eval σ₀ b σ ρ).n by omega)
      have := (eval σ₀ b σ ρ).le_hi
      exact Int.le_trans (by omega) (Int.le_max_right h1 h2))
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_sdiv (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (hb)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-Gabbro.Grammatik.betragMax l1 h1) (Gabbro.Grammatik.betragMax l1 h1))) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int (-Gabbro.Grammatik.betragMax l1 h1) (Gabbro.Grammatik.betragMax l1 h1)) (eval σ₀ (.sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-Gabbro.Grammatik.betragMax l1 h1) (Gabbro.Grammatik.betragMax l1 h1))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int (-Gabbro.Grammatik.betragMax l1 h1) (Gabbro.Grammatik.betragMax l1 h1)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .sdiv (jsdiv l1 h1 l2 h2) (ety (Expr.sdiv hb a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := sdiv_hop l1 h1 l2 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hb hfJ
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .sdiv (Int.tdiv) (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_srem (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (l1)
    (h1)
    (l2)
    (h2)
    (hb)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-(Gabbro.Grammatik.betragMax l2 h2 - 1)) (Gabbro.Grammatik.betragMax l2 h2 - 1))) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int (-(Gabbro.Grammatik.betragMax l2 h2 - 1)) (Gabbro.Grammatik.betragMax l2 h2 - 1)) (eval σ₀ (.srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (-(Gabbro.Grammatik.betragMax l2 h2 - 1)) (Gabbro.Grammatik.betragMax l2 h2 - 1))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int (-(Gabbro.Grammatik.betragMax l2 h2 - 1)) (Gabbro.Grammatik.betragMax l2 h2 - 1)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .srem (jsrem l1 h1 l2 h2) (ety (Expr.srem hb a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := srem_hop l1 h1 l2 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hb hfJ
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .srem (Int.tmod) (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_band (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_l2}
    (h1)
    (h2)
    (h0)
    (h0')
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.band (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 h1) (eval σ₀ (.band (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 h1) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .and (jbit h1 h2 h1) (ety (Expr.band h0 h0' a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jbit h1 h2 h1).1 (jbit h1 h2 h1).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := band_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
    (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
    (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .and (fun a b => ((a.toNat &&& b.toNat : Nat) : Int)) (jbit h1 h2 h1).1 (jbit h1 h2 h1).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_bor (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_l2}
    (h1)
    (h2)
    (w)
    (h0)
    (h0')
    (hw1)
    (hw2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.bor (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1)) (eval σ₀ (.bor (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .or (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := bor_hop w h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hw1 hw2 hfJ
    (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
    (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .or (fun a b => ((a.toNat ||| b.toNat : Nat) : Int)) (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_bxor (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_l2}
    (h1)
    (h2)
    (w)
    (h0)
    (h0')
    (hw1)
    (hw2)
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.bxor (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv a r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l1 h1) (eval σ₀ a σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l1 h1))
    (ih_lowerE_ok_b : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv b r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int zi_l2 h2) (eval σ₀ b σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int zi_l2 h2))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1)) (eval σ₀ (.bxor (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 (2 ^ w - 1)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .xor (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bxor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := bxor_hop w h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hw1 hw2 hfJ
    (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
    (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .xor (fun a b => ((a.toNat ^^^ b.toNat : Nat) : Int)) (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

end Gabbro.Code.Lower
