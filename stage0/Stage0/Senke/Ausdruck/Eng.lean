/-
  File:      stage0/Stage0/Senke/Ausdruck/Eng.lean
  Subject:   Signed interval narrowing: evaluate once, keep a fitting word or execute the fallback.
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {reserved : Nat}

variable [Kern] {D : Deklaration} {L : Lay D}

/-- A binary instruction may read any two frame slots, including its destination. -/
theorem eng_bin_ok {m : Runner.Mem} {pc fp : Runner.W} {K d a b o : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {va vb r : Runner.W}
    {g : Runner.W → Runner.W → Option Runner.W}
    (hp : Pre L m pc fp K d [ci o d a b] ρ W reserved) (hd : d < K) (ha : a < K) (hb : b < K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (hop : op o = bin g) (ho : o < 256) (hg : g va vb = some r) :
    Ok m pc fp K d [ci o d a b] (· = r) := by
  have := hp.small
  refine one_ok hp (by simpa [ci] using ho) hd rfl fun m' hw => ?_
  have hi := hp.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci]
  rw [hop]
  apply run_bin hi
  · simpa only [sx_nat (d := a) (by omega)] using ra
  · simpa only [sx_nat (d := b) (by omega)] using rb
  · exact hg
  · simpa only [sx_nat (d := d) (by omega)] using hw

/-- The five test instructions preserve the value in `d` and put the outside flag in `d+1`. -/
theorem eng_test_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {lo hi : Int}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {v : Runner.W}
    (hp : Pre L m pc fp K (d + 1) (engTest d lo hi) ρ W reserved) (hd : d + 2 < K)
    (hl : lit32 lo = true) (hh : lit32 hi = true)
    (rv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some v) :
    Ok m pc fp K (d + 1) (engTest d lo hi)
      (· = Runner.IR.bool (v.slt (BitVec.ofInt 64 lo) || (BitVec.ofInt 64 hi).slt v)) := by
  change Pre L _ _ _ _ _ ([ci 1 (d+1) lo 0] ++ ([ci 13 (d+1) d (d+1)] ++
    ([ci 1 (d+2) hi 0] ++ ([ci 13 (d+2) (d+2) d] ++ [ci 9 (d+1) (d+1) (d+2)])))) _ _ reserved at hp
  obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := const_ok hp.left hl (by omega)
  have h1 := hp.next a1 (Nat.le_refl _) (by omega)
  have rv1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := eng_bin_ok (d := d+1) (a := d) (b := d+1) h1.left (by omega) (by omega) (by omega)
    rv1 r1 (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h2 := h1.next a2 (Nat.le_refl _) (by omega)
  obtain ⟨m3, s3, a3, w3, r3, rfl⟩ := const_ok (d := d+2)
    { h2.left with ctx := by have := hp.ctx; omega } hh (by omega : d+2 < K)
  have h3 := h2.next (a3.mono (by omega : d+1 ≤ d+2)) (Nat.le_refl _) (by omega)
  have rv3 : m3.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low (a1.trans a2 |>.trans (a3.mono (by omega))) hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m4, s4, a4, w4, r4, rfl⟩ := eng_bin_ok (d := d+2) (a := d+2) (b := d)
    { h3.left with ctx := by have := hp.ctx; omega }
    (by omega : d+2 < K) (by omega) (by omega) r3 rv3
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h4 := h3.next (a4.mono (by omega : d+1 ≤ d+2)) (Nat.le_refl _) (by omega)
  have r24 : m4.rd64 (slot fp (BitVec.ofNat 64 (d+1))) = some (Runner.IR.bool (v.slt (BitVec.ofInt 64 lo))) := by
    rw [agree_rd_low (a3.trans a4) h2.frame.room (by omega) (by omega)]; exact r2
  obtain ⟨m5, s5, a5, w5, r5, rfl⟩ := eng_bin_ok (d := d+1) (a := d+1) (b := d+2) h4 (by omega) (by omega) (by omega) r24 r4
    (g := fun x y => some (x ||| y)) rfl (by decide) rfl
  refine ⟨m5, ?_, a1.trans (a2.trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans a5))), _, r5, ?_⟩
  · simpa only [engTest, List.length_cons, List.length_nil, List.length_singleton, pc_add,
      Nat.reduceAdd] using s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · simp only [bool_word]; exact or_word _ _

/-- Successful lowering of `eng` computes its model value, including the fallback outside the interval. -/
theorem eng_ok {Λ : List (Res D)} {Γ : Ctx} {lo hi lo' hi' : Int}
    {e : Expr D Γ Λ (.int lo hi)} {b : Expr D Γ Λ (.int lo' hi')}
    {L : Lay D} {fp : Runner.W} {K d top : Nat} {c : List II} {W : Runner.Mem → Prop}
    {σ₀ σ : World D} {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (h : lowE L (reserved := reserved) (.eng e lo' hi' b) d = some (c, top)) (hK : top ≤ K)
    (ihe : ∀ ce te, lowE L (reserved := reserved) e d = some (ce, te) → te ≤ K → ∀ m pc,
      Pre L m pc fp K d ce ρ W reserved → Ok m pc fp K d ce (Enc L (.int lo hi) (eval σ₀ e σ ρ)))
    (ihb : ∀ cb tb, lowE L (reserved := reserved) b d = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d cb ρ W reserved → Ok m pc fp K d cb (Enc L (.int lo' hi') (eval σ₀ b σ ρ)))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.int lo' hi') (eval σ₀ (.eng e lo' hi' b) σ ρ)) := by
  simp only [lowE_eqs, engL] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    obtain ⟨⟨heW, hl⟩, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cb, tb⟩, hb, h⟩ := h
    split at h
    · next hlen =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd : d + 2 < K := by omega
      have hp' : Pre L m pc fp K d
          (ce ++ (engTest d lo' hi' ++ ([ci 19 (d+1) ((16 * (cb.length+1) : Nat) : Int) 0] ++ cb))) ρ W reserved := by
        simpa only [engC, List.append_assoc] using hp
      obtain ⟨m1, s1, a1, w1, r1, p1⟩ := ihe ce te he (by omega) _ _ hp'.left
      simp only [Enc] at p1
      subst w1
      have h1 := hp'.next a1 (Nat.le_refl _) (by omega)
      obtain ⟨m2, s2, a2, w2, r2, p2⟩ := eng_test_ok
        { h1.left with ctx := by have := hp.ctx; omega } hd hl hh r1
      subst w2
      have h2 := h1.next (a2.mono (by omega : d ≤ d+1)) (Nat.le_refl _) (by omega)
      have hi := h2.code 0 (by simp)
      simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
      rw [← sx_nat (d := d+1) (by have := hp.small; omega)] at r2
      have hx := inW_spec heW (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi
      have hlW : -2^63 ≤ lo' ∧ lo' < 2^63 := by
        simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hl; omega
      have hhW : -2^63 ≤ hi' ∧ hi' < 2^63 := by
        simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hh; omega
      by_cases hin : lo' ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ hi'
      · have hz : Runner.IR.bool ((BitVec.ofInt 64 (eval σ₀ e σ ρ).n).slt (BitVec.ofInt 64 lo') ||
            (BitVec.ofInt 64 hi').slt (BitVec.ofInt 64 (eval σ₀ e σ ρ).n)) = 0 := by
          rw [slt_in hx hlW, slt_in hhW hx]
          have hlow : ¬ (eval σ₀ e σ ρ).n < lo' := by omega
          have hhigh : ¬ hi' < (eval σ₀ e σ ρ).n := by omega
          simp [Runner.IR.bool, hlow, hhigh]
        rw [hz] at r2
        have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_zero hi r2))
        have rv : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 (eval σ₀ e σ ρ).n) := by
          rw [agree_rd_low a2 h1.frame.room (by omega) (by omega)]; exact r1
        refine ⟨m2, s1.trans (s2.trans (star_cast sb rfl ?_)),
          a1.trans (a2.mono (by omega)), _, rv, ?_⟩
        · simp only [T.mk.injEq, and_true]
          rw [sx_nat hlen, pc_add, pc_add]
          congr 2 <;> simp [engC, engTest] <;> omega
        · simp only [Enc, eval]
          erw [dite_eq_left hin]
      · have hn : Runner.IR.bool ((BitVec.ofInt 64 (eval σ₀ e σ ρ).n).slt (BitVec.ofInt 64 lo') ||
            (BitVec.ofInt 64 hi').slt (BitVec.ofInt 64 (eval σ₀ e σ ρ).n)) = 1 := by
          rw [slt_in hx hlW, slt_in hhW hx]
          have hout : (eval σ₀ e σ ρ).n < lo' ∨ hi' < (eval σ₀ e σ ρ).n := by omega
          simp [Runner.IR.bool, hout]
        rw [hn] at r2
        have sb := Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) (run_brz_ne hi r2 (by decide)))
        have h3 := h2.next (Agree.refl fp d K m2) (Nat.le_refl _) (by omega)
        obtain ⟨m3, s3, a3, w3, r3, p3⟩ := ihb cb tb hb (by omega) _ _ h3
        refine ⟨m3, s1.trans (s2.trans ((star_cast sb rfl ?_).trans (star_cast s3 rfl ?_))),
          a1.trans ((a2.mono (by omega)).trans a3), w3, r3, ?_⟩
        · rfl
        · simp only [T.mk.injEq, and_true]
          rw [pc_add, pc_add, pc_add]
          congr 2 <;> simp [engC, engTest] <;> omega
        · simp only [Enc, eval]
          erw [dite_eq_right hin]
          exact p3
    · cases h
  · cases h

/-- Both inclusive endpoints and both fallback directions satisfy the recursive proof premises. -/
theorem eng_ok_zeuge {Λ : List (Res D)} {Γ : Ctx} (L : Lay D) (σ₀ σ : World D) (ρ : Env D Γ)
    (n : Int) (hn : n = -4 ∨ n = -3 ∨ n = 5 ∨ n = 6)
    {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {W : Runner.Mem → Prop}
    (hd : d + 3 ≤ K)
    (hp : Pre L m pc fp K d (engC d (-3) 5 [ci 1 d n 0] [ci 1 d 2 0]) ρ W reserved) :
    Ok m pc fp K d (engC d (-3) 5 [ci 1 d n 0] [ci 1 d 2 0])
      (· = BitVec.ofInt 64 (if -3 ≤ n ∧ n ≤ 5 then n else 2)) := by
  let b : Expr D Γ Λ (.int (-3) 5) := .widen (by decide) (by decide) (.lit 2)
  have hl : lit32 n = true := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  have he : lowE L (reserved := reserved) (.eng (.lit n) (-3) 5 b) d =
      some (engC d (-3) 5 [ci 1 d n 0] [ci 1 d 2 0], d + 3) := by
    have hw : inW n n = true := by
      rcases hn with rfl | rfl | rfl | rfl <;> decide
    simp only [lowE_eqs, b, engL, hl, hw]
    change some (engC d (-3) 5 [ci 1 d n 0] [ci 1 d 2 0],
      max (d+1) (max (d+1) (d+3))) = _
    congr 2
    omega
  refine (eng_ok (σ₀ := σ₀) (σ := σ) he hd ?_ ?_ hp).mono ?_
  · intro ce te he hte m pc hp
    simp only [lowE_eqs, hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact const_ok hp hl (by omega)
  · intro cb tb hb htb m pc hp
    have hb' : some ([ci 1 d 2 0], d+1) = some (cb, tb) := hb
    cases Option.some.inj hb'
    exact const_ok hp (by decide) (by omega)
  · intro w hw
    rcases hn with rfl | rfl | rfl | rfl <;> exact hw

/-- Refuse a source outside signed 64 bits and either bound outside the signed literal field. -/
theorem eng_refused_zeuge {Λ : List (Res D)} {Γ : Ctx} (L : Lay D) (d : Nat) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.eng (.lit (2^63)) 0 0 (.lit 0)) d = none ∧
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.eng (.lit 0) (-(2^31)-1) 0
      (.widen (by decide) (by decide) (.lit 0))) d = none ∧
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.eng (.lit 0) 0 (2^31)
      (.widen (by decide) (by decide) (.lit 0))) d = none := by
  exact ⟨rfl, rfl, rfl⟩

end Gabbro.Stage0.Senke
