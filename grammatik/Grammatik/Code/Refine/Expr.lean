import Grammatik.Code.Refine.Env
import Grammatik.Code.Refine.Match.Opt
import Grammatik.Code.Refine.Match.Case
import Grammatik.Code.Refine.Bits.Forms

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

mutual

/-- **Every lowered expression computes what `eval` computes.** -/
theorem lowerE_ok (lay : Layout D) (hL : LayoutOk lay) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : GTy} (e : Expr D Γ Λ τ) (cenv : List Reg) (r : Nat) (c : LR),
      lowerE lay cenv e r = some c →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs),
        Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) →
        Frag m rs r c (encR lay τ (eval σ₀ e σ ρ)) ∧ FitsT τ
  | _, _, _, .lit n, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      split at h
      · rename_i hf
        obtain rfl := Option.some.inj h
        refine ⟨frag_const m rs r _ _ rfl (fun x hx => nomatch hx), ?_⟩
        intro lo hi e
        cases e
        exact hf
      · simp only [reduceCtorEq] at h
  | _, _, _, .tru, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h
      exact ⟨frag_const m rs r _ (Val.bool true) (congrArg some ofInt_true) (fun x hx => nomatch hx),
        fitsT_nonint (fun lo hi e => nomatch e)⟩
  | _, _, _, .fls, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h
      exact ⟨frag_const m rs r _ (Val.bool false) (congrArg some ofInt_false) (fun x hx => nomatch hx),
        fitsT_nonint (fun lo hi e => nomatch e)⟩
  | _, _, τ, .var x, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      obtain ⟨a, b, ha, hs, hr, _, hl⟩ := envRep_get x cenv ρ hE
      simp only [lowerE, ha, hs, if_true] at h
      obtain ⟨c', hc', F⟩ := loadG_frag lay τ (ρ.get x) hs (.reg a) b 0 m rs r
        (by simpa [Opd.ev] using hr) hl
      rw [hc'] at h
      obtain rfl := Option.some.inj h
      exact ⟨F, fitsT_supp hs⟩
  | _, _, _, .glob g hgl, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
  | _, _, _, .ptrOf t n ht rw, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h
      exact ⟨frag_const m rs r _ _ (by simp only [Opd.ev, encR, ht]) (fun x hx => nomatch hx),
        fitsT_nonint (fun lo hi e => nomatch e)⟩
  | _, _, _, .slot t f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
        obtain ⟨Fi, _⟩ := lowerE_ok lay hL i cenv r (ci, oi, r1) hi σ₀ σ ρ m rs hR hE hc
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
  | _, _, _, .thru p t ht f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
        obtain ⟨Ip, _⟩ := lowerE_ok lay hL p cenv r (cp, op, r1) hp σ₀ σ ρ m rs hR hE hc
        have hrp := Frag.le Ip
        let z : Zahl 0 (D.count t - 1) := eval σ₀ i σ ρ
        have hk0 : 0 ≤ z.n := z.lo_le
        have hk1 : z.n < D.count t := by have := z.le_hi; omega
        refine ⟨?_, fitsT_supp hs⟩
        have T := frag_three Ip (fun rsA hag =>
            (lowerE_ok lay hL i cenv r1 (ci, oi, r2) hi σ₀ σ ρ m rsA hR
              (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE)
              (fun x hx => Nat.lt_of_lt_of_le (hc x hx) hrp)).1)
          (fun rsB hagB hoa hob hla hlb => frag_two (ct := (cl, ol, r4))
            (slotAddr_frag lay hL t f hs z.n hk0 hk1 op oi r2 m rsB
              (by rw [hoa]; simp only [encR, ht]) hla hob hlb ⟨_, hR.1 t z.n f hs hk0 hk1⟩ (ca, oa, r3) hsa)
            (fun rsC hagC hoa' hlta => by
              obtain ⟨c', hc', F⟩ := loadG_frag lay (D.typ t f) (σ.slots t z.n f) hs oa (lay.gblk t)
                (lay.off t z.n f) m rsC r3 hoa' (hR.1 t z.n f hs hk0 hk1)
              rw [hld] at hc'
              obtain rfl := Option.some.inj hc'
              exact F))
        rw [List.append_assoc (cp ++ ci) ca cl]
        exact T
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | _, _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') h1 h2 e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
        obtain ⟨Ie, Ife⟩ := lowerE_ok lay hL e cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
        have hfe : Ar.Fits lo hi 128 := Ife lo hi rfl
        refine ⟨frag_two (ct := (c2, o2, r2)) Ie (fun rsA hag hoe hlte => ?_), fitsT_of hfit.2⟩
        obtain ⟨c', hc', F⟩ := cvtG_frag (lb := lo') (hb := hi') hfe
          (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi hoe hlte
        have hc'' : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 = some c' := hc'
        rw [hcv] at hc''
        obtain rfl := Option.some.inj hc''
        exact F
      · simp only [reduceCtorEq] at h
  | _, _, _, .add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (binRest_fits hbr)⟩
      exact binRest_frag .add (fun a b => a + b) val_bin_add (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (binRest_fits hbr)⟩
      exact binRest_frag .sub (fun a b => a - b) val_bin_sub (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .mul (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (binRest_fits hbr)⟩
      exact binRest_frag .mul (fun a b => a * b) val_bin_mul (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .neg (lo := lo) (hi := hi) a, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      simp only [ha] at h
      rcases hbr : binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1
        with _ | ⟨ct, ot, r2⟩
      · simp only [hbr, reduceCtorEq] at h
      simp only [hbr] at h
      obtain rfl := Option.some.inj h
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      refine ⟨frag_two (ct := (ct, ot, r2)) Ia (fun rsA hag hoa hlta => ?_), fitsT_of (binRest_fits hbr)⟩
      have T := binRest_frag .sub (fun a b => a - b) val_bin_sub (la := 0) (ha := 0) (lb := lo)
        (hb := hi) 0 (eval σ₀ a σ ρ).n (by decide) (Ifa lo hi rfl) (Int.le_refl _) (Int.le_refl _)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (.int (twid (.int 0 0)) 0) oa r1 m rsA rfl hoa
        (fun x hx => nomatch hx) hlta (ct, ot, r2) hbr
      rw [Int.zero_sub] at T
      exact T
  | _, _, _, .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      exact cmpRest_frag .ult .slt (fun a b => a < b) (fun sg W a b hW ha hb => val_icmp_lt sg W a b hW ha hb)
        (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      exact cmpRest_frag .ule .sle (fun a b => a ≤ b) (fun sg W a b hW ha hb => val_icmp_le sg W a b hW ha hb)
        (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      exact cmpRest_frag .eq .eq (fun a b => a = b) (fun sg W a b hW ha hb => val_icmp_eq sg W a b hW ha hb)
        (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa l1 h1 rfl)
        (Ifb l2 h2 rfl) (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le
        (eval σ₀ b σ ρ).le_hi oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .and a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      obtain ⟨Ia, _⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      refine ⟨frag_three (ct := ([.bin r2 .and 1 oa ob], .reg r2, r2 + 1)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      have hoa' : oa.ev rsB = some (Val.bool (eval σ₀ a σ ρ)) := hoa
      have hob' : ob.ev rsB = some (Val.bool (eval σ₀ b σ ρ)) := hob
      have hv := val_bin_and (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
      exact frag_one m rsB r2 (.bin r2 .and 1 oa ob) (Val.bool (eval σ₀ a σ ρ && eval σ₀ b σ ρ)) (by
        simp only [stepI, hoa', hob', hv]
        rfl)
  | _, _, _, .or a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      obtain ⟨Ia, _⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      refine ⟨frag_three (ct := ([.bin r2 .or 1 oa ob], .reg r2, r2 + 1)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      have hoa' : oa.ev rsB = some (Val.bool (eval σ₀ a σ ρ)) := hoa
      have hob' : ob.ev rsB = some (Val.bool (eval σ₀ b σ ρ)) := hob
      have hv := val_bin_or (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
      exact frag_one m rsB r2 (.bin r2 .or 1 oa ob) (Val.bool (eval σ₀ a σ ρ || eval σ₀ b σ ρ)) (by
        simp only [stepI, hoa', hob', hv]
        rfl)
  | _, _, _, .not a, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      simp only [ha] at h
      obtain rfl := Option.some.inj h
      obtain ⟨Ia, _⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      refine ⟨frag_two (ct := ([.bin r1 .xor 1 oa (.int 1 1)], .reg r1, r1 + 1)) Ia (fun rsA hag hoa hlta => ?_), fitsT_nonint (fun lo hi e => nomatch e)⟩
      have hoa' : oa.ev rsA = some (Val.bool (eval σ₀ a σ ρ)) := hoa
      have hv := val_bin_not (eval σ₀ a σ ρ)
      exact frag_one m rsA r1 (.bin r1 .xor 1 oa (.int 1 1)) (Val.bool (!eval σ₀ a σ ρ)) (by
        have e1 : (Opd.int 1 1).ev rsA = some (Val.ofInt 1 1) := rfl
        simp only [stepI, hoa', e1, hv]
        rfl)
  | _, _, _, .fnref .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldG .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldS .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE,
      hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
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
  | _, _, _, .rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) h0 h1' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE,
      hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rs hR hE hc1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb σ₀ σ ρ m rsA hR
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
  | _, _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := sdiv_hop l1 h1 l2 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hb hfJ
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .sdiv (Int.tdiv) (jsdiv l1 h1 l2 h2).1 (jsdiv l1 h1 l2 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := srem_hop l1 h1 l2 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hb hfJ
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .srem (Int.tmod) (jsrem l1 h1 l2 h2).1 (jsrem l1 h1 l2 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .getBytes .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .band (h1 := h1) (h2 := h2) h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jbit h1 h2 h1).1 (jbit h1 h2 h1).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := band_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
        (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
        (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .and (fun a b => ((a.toNat &&& b.toNat : Nat) : Int)) (jbit h1 h2 h1).1 (jbit h1 h2 h1).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .bor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := bor_hop w h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hw1 hw2 hfJ
        (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
        (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .or (fun a b => ((a.toNat ||| b.toNat : Nat) : Int)) (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .bxor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := bxor_hop w h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hw1 hw2 hfJ
        (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
        (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .xor (fun a b => ((a.toNat ^^^ b.toNat : Nat) : Int)) (jbit h1 h2 (2 ^ w - 1)).1 (jbit h1 h2 (2 ^ w - 1)).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .shl (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jshl h1 h2).1 (jshl h1 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := shl_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
        (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
        (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .shl (fun a b => a * 2 ^ b.toNat) (jshl h1 h2).1 (jshl h1 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .shr (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
      obtain ⟨Ia, Ifa⟩ := lowerE_ok lay hL a cenv r (ca, oa, r1) ha σ₀ σ ρ m rs hR hE hc
      have hra := Frag.le Ia
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hra
      obtain ⟨_, Ifb⟩ := lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rs hR hE hc1
      have hfJ : Ar.Fits (jshr h1 h2).1 (jshr h1 h2).2 128 := by simpa [fitsT] using (opRest_fits hbr).1
      refine ⟨frag_three (ct := (ct, ot, r3)) Ia (fun rsA hag =>
          (lowerE_ok lay hL b cenv r1 (cb, ob, r2) hb' σ₀ σ ρ m rsA hR
            (envRep_regs cenv ρ (fun x hx => hag x (hc x hx)) hE) hc1).1)
        (fun rsB hagB hoa hob hla hlb => ?_), fitsT_of (opRest_fits hbr).2⟩
      obtain ⟨hop, hz1, hz2⟩ := shr_hop h1 h2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n hfJ
        (Int.le_trans h0 (eval σ₀ a σ ρ).lo_le) (eval σ₀ a σ ρ).le_hi (Int.le_trans h0' (eval σ₀ b σ ρ).lo_le)
        (eval σ₀ b σ ρ).le_hi
      exact opRest_frag .lshr (fun a b => a / 2 ^ b.toNat) (jshr h1 h2).1 (jshr h1 h2).2 (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n (Ifa _ _ rfl) (Ifb _ _ rfl)
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi hop hz1 hz2
        oa ob r2 m rsB hoa hob hla hlb (ct, ot, r3) hbr
  | _, _, _, .fllt .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .flle .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .none n, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨frag_intc m rs r _ _, fitsT_nonint (fun lo hi e => nomatch e)⟩
      · simp only [reduceCtorEq] at h
  | _, _, _, .some (n := n) e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
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
        obtain ⟨Ie, _⟩ := lowerE_ok lay hL e cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
        refine ⟨frag_two (ct := (c2, o2, r2)) Ie (fun rsA hag hoe hlte => ?_),
          fitsT_nonint (fun lo hi e => nomatch e)⟩
        obtain ⟨c', hc', F⟩ := cvtG_frag (lb := -1) (hb := n - 1) hfit.2
          (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi hoe hlte
        rw [hcv] at hc'
        obtain rfl := Option.some.inj hc'
        exact F
      · simp only [reduceCtorEq] at h
  | _, _, _, .istSome (n := n) e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      simp only [he] at h
      split at h
      · rename_i hfit
        obtain rfl := Option.some.inj h
        obtain ⟨Ie, _⟩ := lowerE_ok lay hL e cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
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
  | _, _, _, .case cs i nutz, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      split at h
      · exact ⟨lowerNutz_ok lay hL _ _ _ nutz cenv r c h σ₀ σ ρ m rs hR hE hc,
          fitsT_nonint (fun lo hi e => nomatch e)⟩
      · simp only [reduceCtorEq] at h
  | _, _, _, .why n i, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨frag_intc m rs r _ _, fitsT_nonint (fun lo hi e => nomatch e)⟩
      · simp only [reduceCtorEq] at h
  | _, _, _, .forallSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .existsSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .reaches .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE, reduceCtorEq] at h

/-- The payload of a `case` expression: the code computes the word of the value. -/
theorem lowerNutz_ok (lay : Layout D) (hL : LayoutOk lay) (W L i : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
      (nutz : Gabbro.Grammatik.NutzlastExpr D Γ Λ c) (cenv : List Reg) (r : Nat) (c0 : LR),
      lowerNutz lay cenv W L i nutz r = some c0 →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs),
        Rep lay σ m → EnvRep lay rs m cenv ρ → (∀ x ∈ cenv, x < r) →
        Frag m rs r c0 (Val.ofInt W ((i : Int) + L * payOff c (Gabbro.Grammatik.evalNutz σ₀ nutz σ ρ)))
  | _, _, _, .empty, cenv, r, c0, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerNutz, Option.some.injEq] at h
      subst h
      have e : ∀ u : Gabbro.Grammatik.Nutzlast none, (i : Int) + L * payOff none u = i := fun u => by simp only [payOff, Int.mul_zero, Int.add_zero]
      rw [e]
      exact frag_intc m rs r W (i : Int)
  | _, _, _, .num (lo := lo) (hi := hi) e, cenv, r, c0, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerNutz] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      simp only [he] at h
      rcases hn : numCode lo hi W L i oe r1 with ⟨cn, on, r2⟩
      rw [hn] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨Ie, Ife⟩ := lowerE_ok lay hL e cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
      refine frag_two (ct := (cn, on, r2)) Ie (fun rsA hag hoe hlte => ?_)
      have F := numCode_frag (lo := lo) (hi := hi) W L i (eval σ₀ e σ ρ).n (Ife lo hi rfl)
        (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi oe r1 m rsA hoe hlte
      rw [hn] at F
      exact F

end

end Gabbro.Code.Lower
