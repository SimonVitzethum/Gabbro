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

set_option linter.unusedSectionVars false in
theorem lowerE_ok_thruOwn (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    {zi_rw}
    {zi_space : Nat}
    {zi_eig}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (mo)
    (s)
    (ho)
    (he)
    (hg)
    (hL')
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.thruOwn (n := zi_n) (rw := zi_rw) (space := zi_space) (o := zi_eig) p t ht f i mo s ho he hg hL' : Expr D Γ Λ (D.typ t f)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_p : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv p r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.ptr ⟨zi_space, ⟨true, zi_rw, some zi_eig⟩, .table zi_n⟩) (eval σ₀ p σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.ptr ⟨zi_space, ⟨true, zi_rw, some zi_eig⟩, .table zi_n⟩))
    (ih_lowerE_ok_i : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv i r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.index (D.count t)) (eval σ₀ i σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.index (D.count t)))
    : Frag m rs r c (encR lay (D.typ t f) (eval σ₀ (.thruOwn (n := zi_n) (rw := zi_rw) (space := zi_space) (o := zi_eig) p t ht f i mo s ho he hg hL' : Expr D Γ Λ (D.typ t f)) σ ρ)) ∧ FitsT (D.typ t f) :=
  by
  have htab := (Deklaration.capTab_sound ht).1
  simp only [lowerE] at h
  rcases hp : lowerE lay cenv p r with _ | ⟨cp, op, r1⟩
  · simp only [hp, reduceCtorEq] at h
  simp only [hp] at h
  rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with _ | ⟨ca, oa, r3⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  by_cases hs : supp (D.typ t f) = true
  · simp only [hs, if_true] at h
    rcases hld : loadG (D.typ t f) oa r3 with _ | ⟨cl, ol, r4⟩
    · simp only [hld, reduceCtorEq] at h
    simp only [hld] at h
    obtain rfl := Option.some.inj h
    obtain ⟨Ip, _⟩ := ih_lowerE_ok_p lay hL cenv r (cp, op, r1) hp σ₀ σ ρ m rs hR hE hc
    have hrp := Frag.le Ip
    let z : Zahl 0 (D.count t - 1) := eval σ₀ i σ ρ
    have hk0 : 0 ≤ z.n := z.lo_le
    have hk1 : z.n < D.count t := by have := z.le_hi; omega
    refine ⟨?_, fitsT_supp hs⟩
    have T := frag_three Ip (fun rsA hag =>
        (ih_lowerE_ok_i lay hL cenv r1 (ci, oi, r2) hi σ₀ σ ρ m rsA hR
          (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE)
          (fun x hx => Nat.lt_of_lt_of_le (hc x hx) hrp)).1)
      (fun rsB hagB hoa hob hla hlb => frag_two (ct := (cl, ol, r4))
        (slotAddr_frag lay hL t f hs z.n hk0 hk1 op oi r2 m rsB
          (by rw [hoa]; simp only [encR, htab]) hla hob hlb ⟨_, hR.1 t z.n f hs hk0 hk1⟩ (ca, oa, r3) hsa)
        (fun rsC hagC hoa' hlta => by
          obtain ⟨c', hc', F⟩ := loadG_frag lay (D.typ t f) (σ.slots t z.n f) hs oa (lay.gblk t)
            (lay.off t z.n f) m rsC r3 hoa' (hR.1 t z.n f hs hk0 hk1)
          rw [hld] at hc'
          obtain rfl := Option.some.inj hc'
          exact F))
    rw [List.append_assoc (cp ++ ci) ca cl]
    exact T
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_thru (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    {zi_rw}
    {zi_space : Nat}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (hL')
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.thru (n := zi_n) (rw := zi_rw) (space := zi_space) p t ht f i hL' : Expr D Γ Λ (D.typ t f)) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_p : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv p r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.ptr (.table zi_n (true, zi_rw) zi_space)) (eval σ₀ p σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.ptr (.table zi_n (true, zi_rw) zi_space)))
    (ih_lowerE_ok_i : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv i r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.index (D.count t)) (eval σ₀ i σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.index (D.count t)))
    : Frag m rs r c (encR lay (D.typ t f) (eval σ₀ (.thru (n := zi_n) (rw := zi_rw) (space := zi_space) p t ht f i hL' : Expr D Γ Λ (D.typ t f)) σ ρ)) ∧ FitsT (D.typ t f) :=
  by
  have htab := (Deklaration.capTab_sound ht).1
  simp only [lowerE] at h
  rcases hp : lowerE lay cenv p r with _ | ⟨cp, op, r1⟩
  · simp only [hp, reduceCtorEq] at h
  simp only [hp] at h
  rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with _ | ⟨ca, oa, r3⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  by_cases hs : supp (D.typ t f) = true
  · simp only [hs, if_true] at h
    rcases hld : loadG (D.typ t f) oa r3 with _ | ⟨cl, ol, r4⟩
    · simp only [hld, reduceCtorEq] at h
    simp only [hld] at h
    obtain rfl := Option.some.inj h
    obtain ⟨Ip, _⟩ := ih_lowerE_ok_p lay hL cenv r (cp, op, r1) hp σ₀ σ ρ m rs hR hE hc
    have hrp := Frag.le Ip
    let z : Zahl 0 (D.count t - 1) := eval σ₀ i σ ρ
    have hk0 : 0 ≤ z.n := z.lo_le
    have hk1 : z.n < D.count t := by have := z.le_hi; omega
    refine ⟨?_, fitsT_supp hs⟩
    have T := frag_three Ip (fun rsA hag =>
        (ih_lowerE_ok_i lay hL cenv r1 (ci, oi, r2) hi σ₀ σ ρ m rsA hR
          (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE)
          (fun x hx => Nat.lt_of_lt_of_le (hc x hx) hrp)).1)
      (fun rsB hagB hoa hob hla hlb => frag_two (ct := (cl, ol, r4))
        (slotAddr_frag lay hL t f hs z.n hk0 hk1 op oi r2 m rsB
          (by rw [hoa]; simp only [encR, htab]) hla hob hlb ⟨_, hR.1 t z.n f hs hk0 hk1⟩ (ca, oa, r3) hsa)
        (fun rsC hagC hoa' hlta => by
          obtain ⟨c', hc', F⟩ := loadG_frag lay (D.typ t f) (σ.slots t z.n f) hs oa (lay.gblk t)
            (lay.off t z.n f) m rsC r3 hoa' (hR.1 t z.n f hs hk0 hk1)
          rw [hld] at hc'
          obtain rfl := Option.some.inj hc'
          exact F))
    rw [List.append_assoc (cp ++ ci) ca cl]
    exact T
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_widen (lay : Layout D) (hL : LayoutOk lay)
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (lo')
    (hi')
    (h1)
    (h2)
    (e)
    (cenv : List Reg)
    (r : Nat)
    (c : LR)
    (h : lowerE lay cenv (.widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') h1 h2 e : Expr D Γ Λ (Gabbro.Grammatik.Ty.int lo' hi')) r = some c)
    (σ₀ : World D)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hc : (∀ x ∈ cenv, x < r))
    (ih_lowerE_ok_e : ∀ (lay : Layout D) (hL : LayoutOk lay), ∀ (cenv : List Reg), ∀ (r : Nat), ∀ (c : LR), lowerE lay cenv e r = some c → ∀ (σ₀ : World D), ∀ (σ : World D), ∀ (ρ : Env D Γ), ∀ (m : Mem), ∀ (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) → Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int lo hi) (eval σ₀ e σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int lo hi))
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int lo' hi') (eval σ₀ (.widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') h1 h2 e : Expr D Γ Λ (Gabbro.Grammatik.Ty.int lo' hi')) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int lo' hi') :=
  by
  simp only [lowerE] at h
  rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hcv : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 with _ | ⟨c2, o2, r2⟩
  · simp only [hcv, reduceCtorEq] at h
  simp only [hcv] at h
  split at h
  · rename_i hfit
    obtain rfl := Option.some.inj h
    obtain ⟨Ie, Ife⟩ := ih_lowerE_ok_e lay hL cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
    have hfe : Ar.Fits lo hi 128 := Ife lo hi rfl
    refine ⟨frag_two (ct := (c2, o2, r2)) Ie (fun rsA hag hoe hlte => ?_), fitsT_of hfit.2⟩
    obtain ⟨c', hc', F⟩ := cvtG_frag (lb := lo') (hb := hi') hfe
      (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi hoe hlte
    have hc'' : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 = some c' := hc'
    rw [hcv] at hc''
    obtain rfl := Option.some.inj hc''
    exact F
  · simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerE_ok_add (lay : Layout D) (hL : LayoutOk lay)
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
    (h : lowerE lay cenv (.add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (l1 + l2) (h1 + h2))) r = some c)
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
    : Frag m rs r c (encR lay (Gabbro.Grammatik.Ty.int (l1 + l2) (h1 + h2)) (eval σ₀ (.add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b : Expr D Γ Λ (Gabbro.Grammatik.Ty.int (l1 + l2) (h1 + h2))) σ ρ)) ∧ FitsT (Gabbro.Grammatik.Ty.int (l1 + l2) (h1 + h2)) :=
  by
  simp only [lowerE] at h
  rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
  · simp only [ha, reduceCtorEq] at h
  simp only [ha] at h
  rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hbr : binRest .add (ety (Expr.add a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
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
  exact binRest_frag .add (fun a b => a + b) val_bin_add (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
    (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
    (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr

end Gabbro.Code.Lower
