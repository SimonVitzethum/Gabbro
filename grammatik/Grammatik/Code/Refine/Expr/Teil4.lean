module

public import Grammatik.Code.Refine.Env
public import Grammatik.Code.Refine.Match.Opt
public import Grammatik.Code.Refine.Match.Case
public import Grammatik.Code.Refine.Bits.Forms
public import Grammatik.Code.Refine.Expr.Teil3

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Env Wert Ctx Var World Res eval Zahl)
variable {D : Deklaration}

set_option linter.unusedSectionVars false in
theorem lowerE_ok_shl (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_l2}
    (h1)
    (h2)
    (w)
    (hw1)
    (hw2)
    (h0)
    (h0')
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.shl (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (h1 * 2 ^ h2.toNat))) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 (h1 * 2 ^ h2.toNat)) (eval σ₀ (.shl (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 (h1 * 2 ^ h2.toNat))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 (h1 * 2 ^ h2.toNat)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .shl (jshl h1 h2) (ety (Expr.shl w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jshl h1 h2).1 (jshl h1 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := shl_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
    (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
    (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .shl (fun a b => a * 2 ^ b.toNat) (jshl h1 h2).1 (jshl h1 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_shr (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_l2}
    (h1)
    (h2)
    (w)
    (hw1)
    (hw2)
    (h0)
    (h0')
    (a)
    (b)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.shr (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int 0 h1) (eval σ₀ (.shr (l1 := zi_l1) (l2 := zi_l2) (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int 0 h1)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int 0 h1) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb', reduceCtorEq] at h
  simp only [hb'] at h
  rcases hbr : opRest .lshr (jshr h1 h2) (ety (Expr.shr w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with
    _ | ⟨ct, ot, r3⟩
  · simp only [List.append_assoc, hbr, Option.map_none, reduceCtorEq] at h
  simp only [hbr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  obtain ⟨Ia, Ifa⟩ := ih_lowerE_ok_a lay hL cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
  have hra := Frag.le Ia
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
  obtain ⟨_, Ifb⟩ := ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
  have hfJ : Ar.Fits (jshr h1 h2).1 (jshr h1 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
  refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
      (ih_lowerE_ok_b lay hL cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
        (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
    (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
  obtain ⟨hop, hz1, hz2⟩ := shr_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
    (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
    (eval σ₀ b σ ρ).le_hi
  exact opRest_frag .lshr (fun a b => a / 2 ^ b.toNat) (jshr h1 h2).1 (jshr h1 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
    (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
    oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

set_option linter.unusedSectionVars false in
theorem lowerE_ok_none (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.none n : Expr D Γ Λ (Gabbro.Grammatik.Ty.opt n)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.opt n) (eval σ₀ (.none n : Expr D Γ Λ (Gabbro.Grammatik.Ty.opt n)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.opt n) :=
  by
  simp only [lowerE] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨frag_intc m rs r _ _, fitsT_nonint (fun lo hi e => nomatch e)⟩
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_some (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (e)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.some (n := n) e : Expr D Γ Λ (Gabbro.Grammatik.Ty.opt n)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_e : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv e r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.index n) (eval σ₀ e σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.index n))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.opt n) (eval σ₀ (.some (n := n) e : Expr D Γ Λ (Gabbro.Grammatik.Ty.opt n)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.opt n) :=
  by
  simp only [lowerE] at h
  rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  split at h
  · rename_i hfit
    rcases hcv : cvtG (.int 0 (n - 1)) (.int (-1) (n - 1)) oe r1 with _ | ⟨c2, o2, r2⟩
    · simp only [Int.reduceNeg, hcv, Option.map_none, reduceCtorEq] at h
    simp only [hcv, Option.map_some] at h
    obtain rfl := Option.some.inj h
    obtain ⟨Ie, _⟩ := ih_lowerE_ok_e lay hL cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
    refine ⟨frag_two (ct := (c2, o2, r2)) Ie (fun rsA hag hoe hlte => ?_),
      fitsT_nonint (fun lo hi e => nomatch e)⟩
    obtain ⟨c', hc', F⟩ := cvtG_frag (lb := -1) (hb := n - 1) hfit.2
      (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi hoe hlte
    rw [hcv] at hc'
    obtain rfl := Option.some.inj hc'
    exact F
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_istSome (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (e)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.istSome (n := n) e : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_e : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv e r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.opt n) (eval σ₀ e σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.opt n))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.istSome (n := n) e : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  split at h
  · rename_i hfit
    obtain rfl := Option.some.inj h
    obtain ⟨Ie, _⟩ := ih_lowerE_ok_e lay hL cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
    refine ⟨frag_two (ct := ([.icmp r1 .sge (Ar.wid (-1) (n - 1)) oe (.int (Ar.wid (-1) (n - 1)) 0)], .reg r1, r1 + 1)) Ie (fun rsA hag hoe hlte => ?_),
      fitsT_nonint (fun lo hi e => nomatch e)⟩
    show Frag m rsA r1 _ (Val.bool (eval σ₀ e σ ρ).isSome)
    generalize eval σ₀ e σ ρ = v at hoe ⊢
    cases v with
    | none => exact istSome_frag hfit (-1) (Or.inl rfl) oe r1 m rsA hoe hlte
    | some k =>
        have := istSome_frag hfit k.n (Or.inr ⟨k.lo_le, k.le_hi⟩) oe r1 m rsA hoe hlte
        rw [decide_eq_true k.lo_le] at this
        exact this
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_why (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (i)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.why n i : Expr D Γ Λ (Gabbro.Grammatik.Ty.why n)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.why n) (eval σ₀ (.why n i : Expr D Γ Λ (Gabbro.Grammatik.Ty.why n)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.why n) :=
  by
  simp only [lowerE] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨frag_intc m rs r _ _, fitsT_nonint (fun lo hi e => nomatch e)⟩
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerNutz_ok_empty (lay : Layout D) (hL : LayoutOk lay) (W L i : Nat)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (cenv : List Reg)
    (r : Nat)
    (c0 : LR)
    (h : lowerNutz lay cenv W L i (.empty : Gabbro.Grammatik.NutzlastExpr D Γ Λ (Option.none)) r = some c0)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c0 (Val.ofInt W ((i : Int) + L * payOff (Option.none) (Gabbro.Grammatik.evalNutz σ₀ (.empty : Gabbro.Grammatik.NutzlastExpr D Γ Λ (Option.none)) σ ρ))) :=
  by
  rw [lowerNutz_empty, Option.some.injEq] at h
  subst h
  have e : ∀ u : Gabbro.Grammatik.Nutzlast D.Fn D.passt none, (i : Int) + L * payOff none u = i := fun u => by simp only [payOff, Int.mul_zero, Int.add_zero]
  rw [e]
  exact frag_intc m rs r W (i : Int)

set_option linter.unusedSectionVars false in
theorem lowerNutz_ok_num (lay : Layout D) (hL : LayoutOk lay) (W L i : Nat)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (e)
    (cenv : List Reg)
    (r : Nat)
    (c0 : LR)
    (h : lowerNutz lay cenv W L i (.val (τ := .int lo hi) e : Gabbro.Grammatik.NutzlastExpr D Γ Λ (Option.some (.int lo hi))) r = some c0)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_e : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv e r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int lo hi) (eval σ₀ e σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int lo hi))
    : Frag m rs r c0 (Val.ofInt W ((i : Int) + L * payOff (Option.some (.int lo hi)) (Gabbro.Grammatik.evalNutz σ₀ (.val (τ := .int lo hi) e : Gabbro.Grammatik.NutzlastExpr D Γ Λ (Option.some (.int lo hi))) σ ρ))) :=
  by
  rw [lowerNutz_int] at h
  rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hn : numCode lo hi W L i oe r1 with ⟨cn, on, r2⟩
  rw [hn] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨Ie, Ife⟩ := ih_lowerE_ok_e lay hL cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
  refine frag_two (ct := (cn, on, r2)) Ie (fun rsA hag hoe hlte => ?_)
  have F := numCode_frag (lo := lo) (hi := hi) W L i (eval σ₀ e σ ρ).n (Ife lo hi rfl)
    (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi oe r1 m rsA hoe hlte
  rw [hn] at F
  exact F

set_option maxHeartbeats 1600000 in
mutual

/-- **Every lowered expression computes what `eval` computes.** -/
theorem lowerE_ok (lay : Layout D) (hL : LayoutOk lay) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : GTy} (e : Expr D Γ Λ τ) (cenv : List Reg) (r : Nat) (c : LR),
      lowerE lay cenv e r = some c →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs),
        Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) →
        Frag m rs r c (encR lay τ (eval σ₀ e σ ρ)) ∧ FitsT τ
  | _, _, _, .lit n, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_lit (lay := lay) (hL := hL) (n := n) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .tru, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_tru (lay := lay) (hL := hL) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .fls, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_fls (lay := lay) (hL := hL) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, τ, .var x, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_var (lay := lay) (hL := hL) (x := x) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .glob g hgl, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_glob (lay := lay) (hL := hL) (g := g) (hgl := hgl) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .ptrOf t n ht rw, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_ptrOf (lay := lay) (hL := hL) (t := t) (n := n) (ht := ht) (rw := rw) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .slot t f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_slot (lay := lay) (hL := hL) (t := t) (f := f) (i := i) (hL' := hL') (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_i := fun lay hL => lowerE_ok lay hL i)
  | _, _, _, .thru p t ht f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_thru (lay := lay) (hL := hL) (p := p) (t := t) (ht := ht) (f := f) (i := i) (hL' := hL') (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_p := fun lay hL => lowerE_ok lay hL p) (ih_lowerE_ok_i := fun lay hL => lowerE_ok lay hL i)
  | _, _, _, .thruOwn p t ht f i mo s ho he hg hm hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_thruOwn (lay := lay) (hL := hL) (p := p) (t := t) (ht := ht) (f := f) (i := i) (mo := mo) (s := s) (ho := ho) (he := he) (hg := hg) (hm := hm) (hL' := hL') (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_p := fun lay hL => lowerE_ok lay hL p) (ih_lowerE_ok_i := fun lay hL => lowerE_ok lay hL i)
  | _, _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') h1 h2 e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_widen (lay := lay) (hL := hL) (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (h1 := h1) (h2 := h2) (e := e) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_e := fun lay hL => lowerE_ok lay hL e)
  | _, _, _, .add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_add (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_sub (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .mul (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_mul (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .neg (lo := lo) (hi := hi) a, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_neg (lay := lay) (hL := hL) (lo := lo) (hi := hi) (a := a) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a)
  | _, _, _, .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_lt (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_le (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_eq (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .and a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_and (lay := lay) (hL := hL) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .or a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_or (lay := lay) (hL := hL) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .not a, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_not (lay := lay) (hL := hL) (a := a) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a)
  | _, _, _, .fnref .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldG .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldS .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_div (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (h0 := h0) (h1' := h1') (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_rem (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (h0 := h0) (h1' := h1') (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_sdiv (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (hb := hb) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_srem (lay := lay) (hL := hL) (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) (hb := hb) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .getBytes .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .band (h1 := h1) (h2 := h2) h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_band (lay := lay) (hL := hL) (h1 := h1) (h2 := h2) (h0 := h0) (h0' := h0') (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .bor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_bor (lay := lay) (hL := hL) (h1 := h1) (h2 := h2) (w := w) (h0 := h0) (h0' := h0') (hw1 := hw1) (hw2 := hw2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .bxor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_bxor (lay := lay) (hL := hL) (h1 := h1) (h2 := h2) (w := w) (h0 := h0) (h0' := h0') (hw1 := hw1) (hw2 := hw2) (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .shl (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_shl (lay := lay) (hL := hL) (h1 := h1) (h2 := h2) (w := w) (hw1 := hw1) (hw2 := hw2) (h0 := h0) (h0' := h0') (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .shr (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_shr (lay := lay) (hL := hL) (h1 := h1) (h2 := h2) (w := w) (hw1 := hw1) (hw2 := hw2) (h0 := h0) (h0' := h0') (a := a) (b := b) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_a := fun lay hL => lowerE_ok lay hL a) (ih_lowerE_ok_b := fun lay hL => lowerE_ok lay hL b)
  | _, _, _, .fllt .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .flle .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .none n, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_none (lay := lay) (hL := hL) (n := n) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .some (n := n) e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_some (lay := lay) (hL := hL) (n := n) (e := e) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_e := fun lay hL => lowerE_ok lay hL e)
  | _, _, _, .istSome (n := n) e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_istSome (lay := lay) (hL := hL) (n := n) (e := e) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_e := fun lay hL => lowerE_ok lay hL e)
  | _, _, _, .case cs i nutz, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      split at h
      · have hk := lowerNutz_ok lay hL _ _ _ nutz cenv r c h σ₀ σ ρ m rs hR hE hc
        refine ⟨?_, fitsT_nonint (fun lo hi e => nomatch e)⟩
        show Frag m rs r c (Val.ofInt _ (packZ (⟨i, Gabbro.Grammatik.Fall.ofNutzlast _ _ _ _
          (Gabbro.Grammatik.evalNutz σ₀ nutz σ ρ)⟩ : Σ i : Fin cs.length, Gabbro.Grammatik.Fall D.Fn D.passt cs i)))
        simp only [packZ, Gabbro.Grammatik.Fall.to_of]
        exact hk
      · simp only [reduceCtorEq] at h
  | _, _, _, .why n i, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerE_ok_why (lay := lay) (hL := hL) (n := n) (i := i) (cenv := cenv) (r := r) (c := c) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .forallSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .existsSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .reaches .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h

/-- The payload of a `case` expression: the code computes the word of the value. -/
theorem lowerNutz_ok (lay : Layout D) (hL : LayoutOk lay) (W L i : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Gabbro.Grammatik.Ty}
      (nutz : Gabbro.Grammatik.NutzlastExpr D Γ Λ c) (cenv : List Reg) (r : Nat) (c0 : LR),
      lowerNutz lay cenv W L i nutz r = some c0 →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs),
        Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) →
        Frag m rs r c0 (Val.ofInt W ((i : Int) + L * payOff c (Gabbro.Grammatik.evalNutz σ₀ nutz σ ρ)))
  | _, _, _, .empty, cenv, r, c0, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerNutz_ok_empty (lay := lay) (hL := hL) (W := W) (L := L) (i := i) (cenv := cenv) (r := r) (c0 := c0) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc)
  | _, _, _, .val (τ := .int lo hi) e, cenv, r, c0, h, σ₀, σ, ρ, m, rs, hR, hE, hc =>
      lowerNutz_ok_num (lay := lay) (hL := hL) (W := W) (L := L) (i := i) (lo := lo) (hi := hi) (e := e) (cenv := cenv) (r := r) (c0 := c0) (h := h) (σ₀ := σ₀) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (hR := hR) (hE := hE) (hc := hc) (ih_lowerE_ok_e := fun lay hL => lowerE_ok lay hL e)
  | _, _, _, .val (τ := .bool) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .opt _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .sum _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .why _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .never) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .fl _ _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .fnptr _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .ptr _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .ref _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .arr _ _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
  | _, _, _, .val (τ := .str _) _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
end

end Gabbro.Code.Lower
