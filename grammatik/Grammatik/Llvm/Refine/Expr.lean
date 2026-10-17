import Grammatik.Llvm.Refine.Env

/-
  File:      Grammatik/Llvm/Refine/Expr.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT THEOREM FOR EXPRESSIONS.

  `lowerE_ok`: if the lowering of an expression `e` succeeds, then, in any memory that represents
  the world (`Rep`) with the environment in its cells (`EnvRep`) and the free registers above
  every variable's, the lowered code runs (`seqI`) to registers in which the operand holds the
  image `encR` of what `eval` computes -- the memory untouched.

  Hypotheses, none an axiom: `LayoutOk lay` (the layout assumptions of `Rep.lean`) and the
  success of the lowering itself (which carries the range assumptions: every integer type met
  fits 128 bits).
-/

namespace Gabbro.Llvm.Lower

open Gabbro.Grammatik (Deklaration Expr Env Wert Ctx Var World Res eval Zahl)

variable {D : Deklaration}

/-- A fragment, then one that reads its result. -/
theorem frag_two {m : Mem} {rs : Regs} {r : Nat} {ca : List Instr} {oa : Opd} {r1 : Nat}
    {va : Val} {ct : LR} {vt : Val}
    (Fa : Frag m rs r (ca, oa, r1) va)
    (Ft : ∀ rsA, (∀ x, x < r → rsA x = rs x) → oa.ev rsA = some va → OpdLt oa r1 →
      Frag m rsA r1 ct vt) :
    Frag m rs r (ca ++ ct.1, ct.2.1, ct.2.2) vt := by
  obtain ⟨rsA, hs, hr, hag, hlt, hev⟩ := Fa
  exact frag_trans (c1 := (ca, oa, r1)) hs hr hag (Ft rsA hag hev hlt)

/-- Two fragments, then one that reads both results. -/
theorem frag_three {m : Mem} {rs : Regs} {r : Nat} {ca cb : List Instr} {oa ob : Opd}
    {r1 r2 : Nat} {va vb : Val} {ct : LR} {vt : Val}
    (Fa : Frag m rs r (ca, oa, r1) va)
    (Fb : ∀ rsA, (∀ x, x < r → rsA x = rs x) → Frag m rsA r1 (cb, ob, r2) vb)
    (Ft : ∀ rsB, (∀ x, x < r → rsB x = rs x) → oa.ev rsB = some va → ob.ev rsB = some vb →
        OpdLt oa r2 → OpdLt ob r2 → Frag m rsB r2 ct vt) :
    Frag m rs r (ca ++ cb ++ ct.1, ct.2.1, ct.2.2) vt := by
  obtain ⟨rsA, hs, hr, hag, hlt, hev⟩ := Fa
  obtain ⟨rsB, hsB, hrB, hagB, hltB, hevB⟩ := Fb rsA hag
  have e1 : r ≤ r1 := hr
  have hagAB : ∀ x, x < r → rsB x = rs x := fun x hx => by
    rw [hagB x (Nat.lt_of_lt_of_le hx e1), hag x hx]
  have hlt2 : OpdLt oa r2 := fun x hx => by
    have h5 : (x : Nat) < r1 := hlt x hx
    have h6 : r1 ≤ r2 := hrB
    exact Nat.lt_of_lt_of_le h5 h6
  have hoa : oa.ev rsB = some va := by
    rw [ev_agree hagB hlt]; exact hev
  have T := frag_trans (c1 := (cb, ob, r2)) (rs := rsA) (r := r1) hsB hrB hagB
    (Ft rsB hagAB hoa hevB hlt2 hltB)
  have T2 := frag_trans (c1 := (ca, oa, r1)) (rs := rs) (r := r) hs hr hag (by simpa using T)
  simpa [List.append_assoc] using T2

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
      · simp at h
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
      by_cases hs : supp (D.gtyp g) = true
      · simp only [lowerE, hs, if_true] at h
        obtain ⟨c', hc', F⟩ := loadG_frag lay (D.gtyp g) (σ.globs g) hs (.glob (lay.ggblk g))
          (lay.ggblk g) 0 m rs r rfl (hR.2 g hs)
        rw [hc'] at h
        obtain rfl := Option.some.inj h
        exact ⟨F, fitsT_supp hs⟩
      · simp [lowerE, hs] at h
  | _, _, _, .ptrOf t n ht rw, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h
      exact ⟨frag_const m rs r _ _ (by simp [Opd.ev, encR, ht]) (fun x hx => nomatch hx),
        fitsT_nonint (fun lo hi e => nomatch e)⟩
  | _, _, _, .slot t f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases hi : lowerE lay cenv i r with _ | ⟨ci, oi, r1⟩
      · simp [hi] at h
      simp only [hi] at h
      rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r1 with
        _ | ⟨ca, oa, r2⟩
      · simp [hsa] at h
      simp only [hsa] at h
      by_cases hs : supp (D.typ t f) = true
      · simp only [hs, if_true] at h
        rcases hld : loadG (D.typ t f) oa r2 with _ | ⟨cl, ol, r3⟩
        · simp [hld] at h
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
      · simp [hs] at h
  | _, _, _, .thru p t ht f i hL', cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases hp : lowerE lay cenv p r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      simp only [hp] at h
      rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
      · simp [hi] at h
      simp only [hi] at h
      rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with _ | ⟨ca, oa, r3⟩
      · simp [hsa] at h
      simp only [hsa] at h
      by_cases hs : supp (D.typ t f) = true
      · simp only [hs, if_true] at h
        rcases hld : loadG (D.typ t f) oa r3 with _ | ⟨cl, ol, r4⟩
        · simp [hld] at h
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
              (by rw [hoa]; simp [encR, ht]) hla hob hlb ⟨_, hR.1 t z.n f hs hk0 hk1⟩ (ca, oa, r3) hsa)
            (fun rsC hagC hoa' hlta => by
              obtain ⟨c', hc', F⟩ := loadG_frag lay (D.typ t f) (σ.slots t z.n f) hs oa (lay.gblk t)
                (lay.off t z.n f) m rsC r3 hoa' (hR.1 t z.n f hs hk0 hk1)
              rw [hld] at hc'
              obtain rfl := Option.some.inj hc'
              exact F))
        rw [List.append_assoc (cp ++ ci) ca cl]
        exact T
      · simp [hs] at h
  | _, _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') h1 h2 e, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hcv : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 with _ | ⟨c2, o2, r2⟩
      · simp [hcv] at h
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
      · simp at h
  | _, _, _, .add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : binRest .add (ety (Expr.add a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : binRest .sub (ety (Expr.sub a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : binRest .mul (ety (Expr.mul a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hbr : binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1
        with _ | ⟨ct, ot, r2⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : cmpRest .ult .slt (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : cmpRest .ule .sle (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hbr : cmpRest .eq .eq (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hbr] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
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
      · simp [ha] at h
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
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
      · simp [ha] at h
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
      simp [lowerE] at h
  | _, _, _, .oldG .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .oldS .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .div .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .rem .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .sdiv .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .srem .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .getBytes .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .band .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .bor .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .bxor .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .shl .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .shr .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .fllt .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .flle .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .none .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .some .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .istSome .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .case .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .why .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .forallSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .existsSlots .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h
  | _, _, _, .reaches .., cenv, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp [lowerE] at h

end Gabbro.Llvm.Lower
