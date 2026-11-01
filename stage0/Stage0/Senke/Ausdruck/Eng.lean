/- Expression narrowing through the common exact scalar interval predicate. -/
import Stage0.Senke.Ausdruck.Arithmetik.Interval

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A scalar interval, signed or unsigned, occupies one word. -/
theorem scalarFits_word {lo hi : Int} (h : scalarFits lo hi = true) : valueWords (.int lo hi) = 1 := by
  simp only [scalarFits, inW, inU, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact integerWords_word a b
  · exact integerWords_unsigned a b

/-- The narrowed target of a successful lowering is a one-word scalar. -/
theorem eng_width {lo hi lo' hi' : Int} {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (lower : engL d lo hi lo' hi' a b = some (c, top)) : valueWords (.int lo' hi') = 1 := by
  simp only [engL, bind, Option.bind_eq_some_iff] at lower
  obtain ⟨_, _, _, _, ⟨ct, tt⟩, ht, _⟩ := lower
  unfold intervalTestL at ht
  split at ht
  · next fits =>
    simp only [Bool.and_eq_true] at fits
    exact scalarFits_word fits.2
  · cases ht

/-- Input and fallback are each evaluated once on their canonical path. The
    shared predicate preserves the input word and reports the original interval. -/
theorem eng_ok {Λ : List (Res D)} {Γ : Ctx} {lo hi lo' hi' : Int}
    {e : Expr D Γ Λ (.int lo hi)} {b : Expr D Γ Λ (.int lo' hi')}
    {L : Lay D} {fp : Runner.W} {K d top : Nat} {c : List II} {W : Runner.Mem → Prop}
    {σ₀ σ : World D} {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (h : engL d lo hi lo' hi' (lowE L (reserved := reserved) e d) (lowE L (reserved := reserved) b d) =
      some (c, top)) (hK : top ≤ K)
    (ihe : ∀ ce te, lowE L (reserved := reserved) e d = some (ce, te) → te ≤ K → ∀ m pc,
      Pre L m pc fp K d ce ρ W reserved → Ok m pc fp K d ce (Enc L (.int lo hi) (eval σ₀ e σ ρ)))
    (ihb : ∀ cb tb, lowE L (reserved := reserved) b d = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d cb ρ W reserved → Ok m pc fp K d cb (Enc L (.int lo' hi') (eval σ₀ b σ ρ)))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.int lo' hi') (eval σ₀ (.eng e lo' hi' b) σ ρ)) := by
  simp only [engL, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ce, te⟩, he, ⟨cb, tb⟩, hb, ⟨ct, tt⟩, ht, h⟩ := h
  split at h
  · next hlen =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hd : d + 1 < K := by have := (intervalTestL_top ht).1; omega
    have hp' : Pre L m pc fp K d
        (ce ++ (ct ++ ([ci 19 (d + 1) ((16 * (cb.length + 1) : Nat) : Int) 0] ++ cb))) ρ W reserved := by
      simpa only [engC, List.append_assoc] using hp
    obtain ⟨m1, s1, a1, w1, r1, p1⟩ := ihe ce te he (by omega) _ _ hp'.left
    simp only [Enc] at p1
    subst w1
    have h1 := hp'.next a1 (Nat.le_refl _) (by omega)
    obtain ⟨m2, s2, a2, w2, r2, p2⟩ := interval_test_ok ht (by omega)
      (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi
      { h1.left with ctx := by have := hp.ctx; omega } r1
    subst w2
    have h2 := h1.next (a2.mono (by omega : d ≤ d + 1)) (Nat.le_refl _) (by omega)
    have hi := h2.code 0 (by simp)
    simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
    rw [← sx_nat (d := d + 1) (by have := hp.small; omega)] at r2
    by_cases hin : lo' ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ hi'
    · have hz : Runner.IR.bool (decide (¬ (lo' ≤ (eval σ₀ e σ ρ).n ∧
          (eval σ₀ e σ ρ).n ≤ hi'))) = 0 := by simp [Runner.IR.bool, hin]
      rw [hz] at r2
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_zero hi r2))
      have rv : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 (eval σ₀ e σ ρ).n) := by
        rw [agree_rd_low a2 h1.frame.room (by omega) (by omega)]; exact r1
      refine ⟨m2, s1.trans (s2.trans (star_cast sb rfl ?_)),
        a1.trans (a2.mono (by omega)), _, rv, ?_⟩
      · simp only [T.mk.injEq, and_true]
        rw [sx_nat hlen, pc_add, pc_add]
        congr 2 <;> simp only [engC, List.length_append, List.length_singleton] <;> omega
      · simp only [Enc, eval]
        erw [dite_eq_left hin]
    · have hn : Runner.IR.bool (decide (¬ (lo' ≤ (eval σ₀ e σ ρ).n ∧
          (eval σ₀ e σ ρ).n ≤ hi'))) = 1 := by simp [Runner.IR.bool, hin]
      rw [hn] at r2
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_ne hi r2 (by decide)))
      have h3 := h2.next (Agree.refl fp d K m2) (Nat.le_refl _) (by omega)
      obtain ⟨m3, s3, a3, w3, r3, p3⟩ := ihb cb tb hb (by omega) _ _ h3
      refine ⟨m3, s1.trans (s2.trans ((star_cast sb rfl ?_).trans (star_cast s3 rfl ?_))),
        a1.trans ((a2.mono (by omega)).trans a3), w3, r3, ?_⟩
      · rfl
      · simp only [T.mk.injEq, and_true]
        rw [pc_add, pc_add, pc_add]
        congr 2 <;> simp only [engC, List.length_append, List.length_singleton] <;> omega
      · simp only [Enc, eval]
        erw [dite_eq_right hin]
        exact p3
  · cases h

end Gabbro.Stage0.Senke
