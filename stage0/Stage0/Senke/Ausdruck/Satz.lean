/-
  File:      stage0/Stage0/Senke/Ausdruck/Satz.lean
  Subject:   `lowE_ok`: every expression the lowering accepts computes, in IR, the word of its value in G.
-/
import Stage0.Senke.Ausdruck.Top
import Stage0.Senke.Welt.WeltAt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

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
  | _, _, .div h0 h1' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, sdiv_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .rem h0 h1' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, srem_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .sdiv hb a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, sdiv_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .srem hb a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, srem_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .band h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, and_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .bor _ h0 h0' _ _ a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, or_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .bxor _ h0 h0' _ _ a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, xor_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .shl _ _ _ h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, lt64, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, shl_w _ (by omega) (by omega)⟩
    · cases h
  | _, _, .shr _ _ _ h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, lt64, inW, decide_eq_true_eq] at hw
      refine binE_ok h hK (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ a d ca ta ha hta m pc ρ hp)
        (fun cb tb hb htb m pc hp => lowE_ok σ₀ σ b (d + 1) cb tb hb htb m pc ρ hp)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, shr_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .none _, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [Enc, eval, optN, hw]
  | _, _, .ptrOf .., d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun _ _ => trivial
  | _, _, .why n r, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hn =>
      simp only [decide_eq_true_eq] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := r.isLt
      refine (const_ok hp (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega) (by omega)).mono
        fun w hw => ?_
      simp only [Enc, eval, hw]
      exact BitVec.ofInt_natCast _ _
    · cases h
  | _, _, .some e, d, c, top, h, hK, m, pc, ρ, hp =>
    (lowE_ok σ₀ σ e d c top h hK m pc ρ hp).mono fun w hw => by simpa [Enc, eval, optN] using hw
  | _, _, .istSome e, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE] at h
    split at h
    · next hn =>
      simp only [decide_eq_true_eq] at hn
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, he, hc⟩ := h
      simp only [bin2, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have := lowE_top e d ce te he
      refine bin_ok (cb := [ci 1 (d + 1) 1 0])
        (Pa := fun w => w = if (eval σ₀ e σ ρ).isSome = false then 1 else 0)
        (fun m pc hp => bin_ok (fun m pc hp => lowE_ok σ₀ σ e d ce te he (by omega) m pc ρ hp)
          (fun m pc hp => const_ok hp (by decide) (by omega))
          (g := fun x y => some (Runner.IR.bool (x == y))) (fun we wm pe pm => ⟨_, rfl, by
            simp only [Enc] at pe
            rw [pe, pm, bool_word]
            cases hv : eval σ₀ e σ ρ with
            | none => simp [optN]
            | some k =>
              have := k.lo_le; have := k.le_hi
              have hne : k.n ≠ -1 := by omega
              have hb : (BitVec.ofInt 64 (optN (some k)) == BitVec.ofInt 64 (-1)) = false := by
                simp only [optN]
                rw [beq_in (by omega) (by decide)]
                simp [hne]
              simp only [hb, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]⟩) rfl (by decide) (by omega) hp)
        (fun m pc hp => const_ok hp (by decide) (by omega))
        (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at ⊢
      rw [pa, pb]
      by_cases hs : (eval σ₀ e σ ρ).isSome = true
      · simp only [hs, wahr?, Bool.true_eq_false, ↓reduceIte]; decide
      · simp only [Bool.not_eq_true] at hs
        simp only [hs, wahr?, Bool.false_eq_true, ↓reduceIte]; decide
    · cases h
  | _, _, .glob .., _, _, _, h, _, _, _, _, _
  | _, _, .slot .., _, _, _, h, _, _, _, _, _
  | _, _, .thru .., _, _, _, h, _, _, _, _, _
  | _, _, .fnref .., _, _, _, h, _, _, _, _, _
  | _, _, .oldG .., _, _, _, h, _, _, _, _, _
  | _, _, .oldS .., _, _, _, h, _, _, _, _, _
  | _, _, .getBytes .., _, _, _, h, _, _, _, _, _
  | _, _, .fllt .., _, _, _, h, _, _, _, _, _
  | _, _, .flle .., _, _, _, h, _, _, _, _, _
  | _, _, .case .., _, _, _, h, _, _, _, _, _
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
