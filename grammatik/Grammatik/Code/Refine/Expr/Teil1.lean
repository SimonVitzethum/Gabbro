module
public import Grammatik.Code.Refine.Env
public import Grammatik.Code.Refine.Match.Opt
public import Grammatik.Code.Refine.Match.Case
public import Grammatik.Code.Refine.Bits.Forms
@[expose] public section


/-
  File:      Grammatik/Code/Refine/Expr.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT THEOREM FOR EXPRESSIONS.

  `lowerE_ok`: if the lowering of an expression `e` succeeds, then, in any memory that represents
  the world (`Rep`) with the environment in its cells (`EnvRep`) and the free registers above
  every variable's, the lowered code runs (`seqI`) to registers in which the operand holds the
  image `encR` of what `eval` computes -- the memory untouched.

  Hypotheses, none an axiom: `LayoutOk lay` (the layout assumptions of `Rep.lean`) and the
  success of the lowering itself (which carries the range assumptions: every integer type met
  fits 128 bits).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Env Wert Ctx Var World Res eval Zahl)

variable {D : Deklaration}

theorem ofInt_true : Val.ofInt 1 1 = Val.bool true := by decide
theorem ofInt_false : Val.ofInt 1 0 = Val.bool false := by decide

theorem Frag.le {m : Mem} {rs : Regs} {r : Nat} {c : LR} {v : Val} (h : Frag m rs r c v) :
    r ≤ c.2.2 := by
  obtain ⟨_, _, h, _⟩ := h; exact h

/-- Every integer type met fits 128 bits. -/
def FitsT (τ : GTy) : Prop := ∀ lo hi, τ = .int lo hi → Ar.Fits lo hi 128

theorem fitsT_of {τ : GTy} (h : fitsT τ = true) : FitsT τ := by
  intro lo hi e; subst e; simpa [fitsT] using h

theorem fitsT_supp {τ : GTy} (h : supp τ = true) : FitsT τ := by
  intro lo hi e; subst e; simpa [supp] using h

theorem fitsT_nonint {τ : GTy} (h : ∀ lo hi, τ ≠ .int lo hi) : FitsT τ := fun lo hi e => absurd e (h lo hi)

set_option linter.unusedSectionVars false in
theorem lowerE_ok_lit (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.lit n : Expr D Γ Λ (Gabbro.Grammatik.Ty.int n n)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int n n) (eval σ₀ (.lit n : Expr D Γ Λ (Gabbro.Grammatik.Ty.int n n)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int n n) :=
  by
  simp only [lowerE] at h
  split at h
  · rename_i hf
    obtain rfl := Option.some.inj h
    refine ⟨frag_const m rs r _ _ rfl (fun x hx => nomatch hx), ?_⟩
    intro lo hi e
    cases e
    exact hf
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_tru (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.tru : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.tru : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  obtain rfl := Option.some.inj h
  exact ⟨frag_const m rs r _ (Val.bool true) (congrArg some ofInt_true) (fun x hx => nomatch hx),
    fitsT_nonint (fun lo hi e => nomatch e)⟩

set_option linter.unusedSectionVars false in
theorem lowerE_ok_fls (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.fls : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.bool) (eval σ₀ (.fls : Expr D Γ Λ (Gabbro.Grammatik.Ty.bool)) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.bool) :=
  by
  simp only [lowerE] at h
  obtain rfl := Option.some.inj h
  exact ⟨frag_const m rs r _ (Val.bool false) (congrArg some ofInt_false) (fun x hx => nomatch hx),
    fitsT_nonint (fun lo hi e => nomatch e)⟩

set_option linter.unusedSectionVars false in
theorem lowerE_ok_var (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {τ : GTy}
    (x)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.var x : Expr D Γ Λ τ) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay τ (eval σ₀ (.var x : Expr D Γ Λ τ) σ ρ)) ∧ FitsT τ :=
  by
  obtain ⟨a, b, ha, hs, hr, _, hl⟩ := envRep_get x cenv ρ hE
  simp only [lowerE, ha, hs, if_true] at h
  obtain ⟨c', hc', F⟩ := loadG_frag lay τ (ρ.get x) hs (.reg a) b 0 m rs r
    (by simpa [Opd.ev] using hr) hl
  rw [hc'] at h
  obtain rfl := Option.some.inj h
  exact ⟨F, fitsT_supp hs⟩

set_option linter.unusedSectionVars false in
theorem lowerE_ok_glob (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (hgl)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.glob g hgl : Expr D Γ Λ (D.gtyp g)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (D.gtyp g) (eval σ₀ (.glob g hgl : Expr D Γ Λ (D.gtyp g)) σ ρ)) ∧ FitsT (D.gtyp g) :=
  by
  by_cases hs : (supp (D.gtyp g) && !lay.shared g) = true
  · have hs0 : supp (D.gtyp g) = true := (Bool.and_eq_true_iff.mp hs).1
    have hsh : lay.shared g = false := by simpa using (Bool.and_eq_true_iff.mp hs).2
    simp only [lowerE, hs, if_true] at h
    obtain ⟨c', hc', F⟩ := loadG_frag lay (D.gtyp g) (σ.globs g) hs0 (.glob (lay.ggblk g))
      (lay.ggblk g) 0 m rs r rfl ((hR.2 g hs0).2 hsh)
    rw [hc'] at h
    obtain rfl := Option.some.inj h
    exact ⟨F, fitsT_supp hs0⟩
  · simp only [lowerE, hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_ptrOf (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {space : Nat}
    (t)
    (n)
    (ht)
    (rw)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.ptrOf t n ht rw : Expr D Γ Λ (Gabbro.Grammatik.Ty.ptr (.table n rw space))) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.ptr (.table n rw space)) (eval σ₀ (.ptrOf t n ht rw : Expr D Γ Λ (Gabbro.Grammatik.Ty.ptr (.table n rw space))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.ptr (.table n rw space)) :=
  by
  have htab := (Deklaration.capTab_sound ht).1
  simp only [lowerE] at h
  obtain rfl := Option.some.inj h
  exact ⟨frag_const m rs r _ _ (by simp only [Opd.ev, encR, htab]) (fun x hx => nomatch hx),
    fitsT_nonint (fun lo hi e => nomatch e)⟩

set_option linter.unusedSectionVars false in
theorem lowerE_ok_slot (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (hL')
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.slot t f i hL' : Expr D Γ Λ (D.typ t f)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_i : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv i r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.index (D.count t)) (eval σ₀ i σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.index (D.count t)))
    : Frag m rs r c (encR lay (D.typ t f) (eval σ₀ (.slot t f i hL' : Expr D Γ Λ (D.typ t f)) σ ρ)) ∧ FitsT (D.typ t f) :=
  by
  simp only [lowerE] at h
  rcases hi : lowerE lay cenv i r with _ | ⟨ci, oi, r1⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r1 with
    _ | ⟨ca, oa, r2⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  by_cases hs : supp (D.typ t f) = true
  · simp only [hs, if_true] at h
    rcases hld : loadG (D.typ t f) oa r2 with _ | ⟨cl, ol, r3⟩
    · simp only [hld, reduceCtorEq] at h
    simp only [hld] at h
    obtain rfl := Option.some.inj h
    obtain ⟨Fi, _⟩ := ih_lowerE_ok_i lay hL cenv r (ci, oi, r1) hi σ₀ σ ρ m rs hR hE hc
    let z : Zahl 0 (D.count t - 1) := eval σ₀ i σ ρ
    have hk0 : 0 ≤ z.n := z.lo_le
    have hk1 : z.n < D.count t := by have := z.le_hi; omega
    refine ⟨?_, fitsT_supp hs⟩
    have T := frag_two Fi (fun rsA hag hoi hlti => frag_two (ct := (cl, ol, r3))
      (slotAddr_frag lay hL t f hs z.n hk0 hk1 (.glob (lay.gblk t)) oi r1 m rsA rfl
        (fun x hx => nomatch hx) hoi hlti ⟨_, hR.1 t z.n f hs hk0 hk1⟩ (ca, oa, r2) hsa)
      (fun rsB hagB hoa hlta => by
        obtain ⟨c', hc', F⟩ := loadG_frag lay (D.typ t f) (σ.slots t z.n f) hs oa (lay.gblk t)
          (lay.off t z.n f) m rsB r2 hoa (hR.1 t z.n f hs hk0 hk1)
        rw [hld] at hc'
        obtain rfl := Option.some.inj hc'
        exact F))
    rw [List.append_assoc]
    exact T
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

end Gabbro.Code.Lower
