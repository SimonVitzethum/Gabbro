/-
  File:      stage0/Stage0/Senke/AusdruckSatz.lean
  Subject:   `lowE_ok`: every expression the lowering accepts computes, in IR, the word of its value in G.
-/
import Stage0.Senke.AusdruckSim

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-! ## Words of values -/

theorem toInt_ofInt_in {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

theorem slt_in {x y : Int} (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : -2 ^ 63 ≤ y ∧ y < 2 ^ 63) :
    (BitVec.ofInt 64 x).slt (BitVec.ofInt 64 y) = decide (x < y) := by
  rw [BitVec.slt_eq_decide, toInt_ofInt_in hx.1 hx.2, toInt_ofInt_in hy.1 hy.2]

theorem beq_in {x y : Int} (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : -2 ^ 63 ≤ y ∧ y < 2 ^ 63) :
    (BitVec.ofInt 64 x == BitVec.ofInt 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.ofInt 64 x ≠ BitVec.ofInt 64 y := fun he => h (by
      have := congrArg BitVec.toInt he
      rwa [toInt_ofInt_in hx.1 hx.2, toInt_ofInt_in hy.1 hy.2] at this)
    simp [h, this]

theorem inW_spec {lo hi : Int} (h : inW lo hi = true) {x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem ofInt_sub' (x y : Int) : BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem and_word (x y : Bool) : ((if x = true then (1 : Runner.W) else 0) &&& (if y = true then 1 else 0)) =
    if (x && y) = true then 1 else 0 := by cases x <;> cases y <;> decide

theorem or_word (x y : Bool) : ((if x = true then (1 : Runner.W) else 0) ||| (if y = true then 1 else 0)) =
    if (x || y) = true then 1 else 0 := by cases x <;> cases y <;> decide

theorem not_word (x : Bool) : ((if x = true then (1 : Runner.W) else 0) ^^^ BitVec.ofInt 64 1) =
    if (!x) = true then 1 else 0 := by cases x <;> decide

theorem bool_word (b : Bool) : Runner.IR.bool b = (if b = true then 1 else 0) := by cases b <;> rfl

/-! ## The slot the lowering stops at -/

theorem lowE_top {Λ : List (Res D)} : {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) →
    (top : Nat) → lowE L e d = some (c, top) → d < top
  | _, _, .widen _ _ e, d, c, top, h => lowE_top e d c top h
  | _, _, .add a b, d, c, top, h | _, _, .sub a b, d, c, top, h | _, _, .mul a b, d, c, top, h
  | _, _, .and a b, d, c, top, h | _, _, .or a b, d, c, top, h => by
    simp only [lowE, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, he⟩ := h
    simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
    have := lowE_top a d ca ta ha
    omega
  | _, _, .lt a b, d, c, top, h | _, _, .eq a b, d, c, top, h => by
    simp only [lowE] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, he⟩ := h
      simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
      have := lowE_top a d ca ta ha
      omega
    · cases h
  | _, _, .neg a, d, c, top, h => by
    simp only [lowE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, _, .not a, d, c, top, h => by
    simp only [lowE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, _, .le a b, d, c, top, h => by
    simp only [lowE] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cb, tb⟩, _, ⟨ca, ta⟩, _, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · cases h
  | _, _, .lit n, d, c, top, h => by
    simp only [lowE] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  | _, _, .tru, d, c, top, h | _, _, .fls, d, c, top, h | _, _, .var _, d, c, top, h => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, _, .glob .., _, _, _, h
  | _, _, .slot .., _, _, _, h
  | _, _, .thru .., _, _, _, h
  | _, _, .ptrOf .., _, _, _, h
  | _, _, .fnref .., _, _, _, h
  | _, _, .oldG .., _, _, _, h
  | _, _, .oldS .., _, _, _, h
  | _, _, .div .., _, _, _, h
  | _, _, .rem .., _, _, _, h
  | _, _, .sdiv .., _, _, _, h
  | _, _, .srem .., _, _, _, h
  | _, _, .getBytes .., _, _, _, h
  | _, _, .band .., _, _, _, h
  | _, _, .bor .., _, _, _, h
  | _, _, .bxor .., _, _, _, h
  | _, _, .shl .., _, _, _, h
  | _, _, .shr .., _, _, _, h
  | _, _, .fllt .., _, _, _, h
  | _, _, .flle .., _, _, _, h
  | _, _, .none .., _, _, _, h
  | _, _, .some .., _, _, _, h
  | _, _, .istSome .., _, _, _, h
  | _, _, .case .., _, _, _, h
  | _, _, .why .., _, _, _, h
  | _, _, .forallSlots .., _, _, _, h
  | _, _, .existsSlots .., _, _, _, h
  | _, _, .reaches .., _, _, _, h
  | _, _, .refEq .., _, _, _, h
  | _, _, .slotRef .., _, _, _, h
  | _, _, .arrNil .., _, _, _, h
  | _, _, .arrCons .., _, _, _, h
  | _, _, .arrGet .., _, _, _, h
  | _, _, .arrSet .., _, _, _, h
  | _, _, .strLit .., _, _, _, h
  | _, _, .strLen .., _, _, _, h
  | _, _, .strCat .., _, _, _, h
  | _, _, .strGet .., _, _, _, h
  | _, _, .strEq .., _, _, _, h
  | _, _, .strLt .., _, _, _, h
  | _, _, .strWeit .., _, _, _, h
  | _, _, .wenn .., _, _, _, h
  | _, _, .eng .., _, _, _, h => by simp [lowE] at h

theorem Ok.mono {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {c : List II} {P Q : Runner.W → Prop}
    (h : Ok m pc fp K d c P) (hq : ∀ w, P w → Q w) : Ok m pc fp K d c Q := by
  obtain ⟨m', s, a, w, r, p⟩ := h
  exact ⟨m', s, a, w, r, hq w p⟩

/-- Destructure the code of a binary operation. -/
theorem bin_some {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top : Nat}
    (h : (do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 o d ca cb)) = some (c, top)) :
    ∃ ca ta cb tb, lowE L a d = some (ca, ta) ∧ lowE L b (d + 1) = some (cb, tb) ∧
      c = ca ++ cb ++ [ci o d d (d + 1)] ∧ top = max ta tb := by
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
  simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨ca, ta, cb, tb, ha, hb, he.1.symm, he.2.symm⟩

theorem lowE_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D) :
    {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowE L e d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre m pc fp K d c ρ W → Ok m pc fp K d c (Enc τ (eval σ₀ e σ ρ))
  | _, _, .widen _ _ e, d, c, top, h, hK, m, pc, ρ, hp => lowE_ok σ₀ σ e d c top h hK m pc ρ hp
  | _, _, .lit n, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (const_ok hp hn (by omega)).mono fun w hw => hw
    · cases h
  | _, _, .tru, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [Enc, eval, wahr?, hw]
  | _, _, .fls, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [Enc, eval, wahr?, hw]
  | _, τ, .var x, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, hw, he⟩ := hp.env τ x
    have := vslot_lt x
    have := hp.ctx
    exact (mov_ok hp (by omega) (by omega) hw).mono fun w' hw' => by subst hw'; exact he
  | _, _, .add a b, d, c, top, h, hK, m, pc, ρ, hp => by
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
      (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_add]; rfl⟩
  | _, _, .sub a b, d, c, top, h, hK, m, pc, ρ, hp => by
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
      (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← ofInt_sub']; rfl⟩
  | _, _, .mul a b, d, c, top, h, hK, m, pc, ρ, hp => by
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
      (g := fun x y => some (x * y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_mul]; rfl⟩
  | _, _, .and a b, d, c, top, h, hK, m, pc, ρ, hp => by
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
      (g := fun x y => some (x &&& y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact and_word _ _
  | _, _, .or a b, d, c, top, h, hK, m, pc, ρ, hp => by
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
      (g := fun x y => some (x ||| y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact or_word _ _
  | _, _, .neg a, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowE_top a (d + 1) ca ta ha
    refine bin_ok (ca := [ci 1 d 0 0]) (fun m pc hp => const_ok hp (by decide) (by omega))
      (fun m pc hp => lowE_ok σ₀ σ a (d + 1) ca ta ha (by omega) m pc ρ hp)
      (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc] at pb ⊢
    rw [pa, pb]
    simp [eval, Zahl.neg, BitVec.ofInt_neg]
  | _, _, .not a, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowE_top a d ca ta ha
    refine bin_ok (cb := [ci 1 (d + 1) 1 0]) (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact not_word _
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true] at hw
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cb, tb⟩, hb, ⟨ca, ta⟩, ha, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowE_top b d cb tb hb
      have := lowE_top a (d + 1) ca ta ha
      have ra := inW_spec hw.1 (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi
      have rb := inW_spec hw.2 (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
      refine bin_ok (cb := [ci 1 (d + 1) 1 0])
        (Pa := fun w => w = if decide ((eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n) = true then 1 else 0)
        (fun m pc hp => bin_ok (fun m pc hp => lowE_ok σ₀ σ b d cb tb hb (by omega) m pc ρ hp)
          (fun m pc hp => lowE_ok σ₀ σ a (d + 1) ca ta ha (by omega) m pc ρ hp)
          (g := fun x y => some (Runner.IR.bool (x.slt y))) (fun wb wa pb pa => ⟨_, rfl, by
            simp only [Enc] at pa pb
            rw [pa, pb, slt_in rb ra, bool_word]⟩) rfl (by decide) (by omega) hp)
        (fun m pc hp => const_ok hp (by decide) (by omega))
        (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at ⊢
      rw [pa, pb]
      by_cases hl : (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n
      · have : ¬ (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n := by omega
        simp [hl, this, wahr?]
      · have : (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n := by omega
        simp [hl, this, wahr?]
    · cases h
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true] at hw
      obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
      have := lowE_top b (d + 1) cb tb hb
      refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
        (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
        (g := fun x y => some (Runner.IR.bool (x.slt y))) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at pa pb ⊢
      rw [pa, pb, slt_in (inW_spec hw.1 (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi)
        (inW_spec hw.2 (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi), bool_word]
      rfl
    · cases h
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true] at hw
      obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
      have := lowE_top b (d + 1) cb tb hb
      refine bin_ok (fun m pc hp => lowE_ok σ₀ σ a d ca ta ha (by omega) m pc ρ hp)
        (fun m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb (by omega) m pc ρ hp)
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at pa pb ⊢
      rw [pa, pb, beq_in (inW_spec hw.1 (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi)
        (inW_spec hw.2 (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi), bool_word]
      rfl
    · cases h
  | _, _, .glob .., _, _, _, h, _, _, _, _, _
  | _, _, .slot .., _, _, _, h, _, _, _, _, _
  | _, _, .thru .., _, _, _, h, _, _, _, _, _
  | _, _, .ptrOf .., _, _, _, h, _, _, _, _, _
  | _, _, .fnref .., _, _, _, h, _, _, _, _, _
  | _, _, .oldG .., _, _, _, h, _, _, _, _, _
  | _, _, .oldS .., _, _, _, h, _, _, _, _, _
  | _, _, .div .., _, _, _, h, _, _, _, _, _
  | _, _, .rem .., _, _, _, h, _, _, _, _, _
  | _, _, .sdiv .., _, _, _, h, _, _, _, _, _
  | _, _, .srem .., _, _, _, h, _, _, _, _, _
  | _, _, .getBytes .., _, _, _, h, _, _, _, _, _
  | _, _, .band .., _, _, _, h, _, _, _, _, _
  | _, _, .bor .., _, _, _, h, _, _, _, _, _
  | _, _, .bxor .., _, _, _, h, _, _, _, _, _
  | _, _, .shl .., _, _, _, h, _, _, _, _, _
  | _, _, .shr .., _, _, _, h, _, _, _, _, _
  | _, _, .fllt .., _, _, _, h, _, _, _, _, _
  | _, _, .flle .., _, _, _, h, _, _, _, _, _
  | _, _, .none .., _, _, _, h, _, _, _, _, _
  | _, _, .some .., _, _, _, h, _, _, _, _, _
  | _, _, .istSome .., _, _, _, h, _, _, _, _, _
  | _, _, .case .., _, _, _, h, _, _, _, _, _
  | _, _, .why .., _, _, _, h, _, _, _, _, _
  | _, _, .forallSlots .., _, _, _, h, _, _, _, _, _
  | _, _, .existsSlots .., _, _, _, h, _, _, _, _, _
  | _, _, .reaches .., _, _, _, h, _, _, _, _, _
  | _, _, .refEq .., _, _, _, h, _, _, _, _, _
  | _, _, .slotRef .., _, _, _, h, _, _, _, _, _
  | _, _, .arrNil .., _, _, _, h, _, _, _, _, _
  | _, _, .arrCons .., _, _, _, h, _, _, _, _, _
  | _, _, .arrGet .., _, _, _, h, _, _, _, _, _
  | _, _, .arrSet .., _, _, _, h, _, _, _, _, _
  | _, _, .strLit .., _, _, _, h, _, _, _, _, _
  | _, _, .strLen .., _, _, _, h, _, _, _, _, _
  | _, _, .strCat .., _, _, _, h, _, _, _, _, _
  | _, _, .strGet .., _, _, _, h, _, _, _, _, _
  | _, _, .strEq .., _, _, _, h, _, _, _, _, _
  | _, _, .strLt .., _, _, _, h, _, _, _, _, _
  | _, _, .strWeit .., _, _, _, h, _, _, _, _, _
  | _, _, .wenn .., _, _, _, h, _, _, _, _, _
  | _, _, .eng .., _, _, _, h, _, _, _, _, _ => by simp [lowE] at h

end Gabbro.Stage0.Senke
