/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Iter.lean
  Subject:   The arithmetic of restoring division: `N` steps from `(x, 0)` end at `(x / y, x % y)`.

  After `i` steps the remainder register holds `P_i mod y` and the dividend register
  `(x * 2^i + P_i / y) mod 2^N`, where `P_i = x / 2^(N-i)` are the top `i` bits of `x`.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Step
@[expose] public section


namespace Gabbro.Stage0.Senke

def dvIter (k y x : Nat) : Nat → Nat × Nat
  | 0 => (x, 0)
  | i + 1 => dvNext k y (dvIter k y x i).1 (dvIter k y x i).2

theorem top_bit_of_register (x Q i N : Nat) (hi : i + 1 ≤ N) (hQ : Q < 2 ^ i) :
    (x * 2 ^ i + Q) % 2 ^ N / 2 ^ (N - 1) % 2 = x / 2 ^ (N - 1 - i) % 2 := by
  have hN : 2 ^ N = 2 ^ (N - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [hN, Nat.mod_mul_right_div_self]
  have hA : (x * 2 ^ i + Q) / 2 ^ (N - 1) = x / 2 ^ (N - 1 - i) := by
    have e : 2 ^ (N - 1) = 2 ^ i * 2 ^ (N - 1 - i) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm x, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hQ,
      Nat.add_zero]
  rw [hA, Nat.mod_mod]

/-- One doubling step of the quotient and remainder of a growing prefix. -/
theorem div_step_arith (P y b : Nat) (hy : 0 < y) (hb : b < 2) :
    (2 * P + b) % y = P % y * 2 + b - (if y ≤ P % y * 2 + b then 1 else 0) * y ∧
    (2 * P + b) / y = 2 * (P / y) + (if y ≤ P % y * 2 + b then 1 else 0) := by
  have hd := Nat.div_add_mod P y
  have hr : P % y < y := Nat.mod_lt _ hy
  generalize P / y = Q at hd ⊢
  generalize P % y = Rr at hd hr ⊢
  have key : ∀ d m : Nat, m + y * d = 2 * P + b → m < y → (2 * P + b) % y = m ∧ (2 * P + b) / y = d := by
    intro d m h1 h2
    have := (Nat.div_mod_unique hy).mpr ⟨h1, h2⟩
    exact ⟨this.2, this.1⟩
  have hyQ : y * (2 * Q) = 2 * (y * Q) := by rw [Nat.mul_left_comm]
  by_cases h : y ≤ Rr * 2 + b
  · obtain ⟨k1, k2⟩ := key (2 * Q + 1) (Rr * 2 + b - y) (by rw [Nat.mul_add, hyQ]; omega) (by omega)
    simp only [h, ite_true, Nat.one_mul]
    exact ⟨k1, k2⟩
  · obtain ⟨k1, k2⟩ := key (2 * Q) (Rr * 2 + b) (by rw [hyQ]; omega) (by omega)
    simp only [h, ite_false, Nat.zero_mul, Nat.sub_zero, Nat.add_zero]
    exact ⟨k1, k2⟩

theorem mod_mul_add (A M c g : Nat) : ((A % M) * c + g) % M = (A * c + g) % M :=
  by rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem dvIter_spec (k y x : Nat) (hy0 : 0 < y) (hx : x < 2 ^ (64 * k)) (hk : 1 ≤ k) :
    ∀ i, i ≤ 64 * k →
      (dvIter k y x i).2 = x / 2 ^ (64 * k - i) % y ∧
      (dvIter k y x i).1 = (x * 2 ^ i + x / 2 ^ (64 * k - i) / y) % 2 ^ (64 * k)
  | 0, _ => by
    simp only [dvIter, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    refine ⟨?_, ?_⟩
    · rw [Nat.div_eq_of_lt hx]; simp
    · rw [Nat.div_eq_of_lt hx]; simp [Nat.mod_eq_of_lt hx]
  | i + 1, hi => by
    obtain ⟨ihR, ihX⟩ := dvIter_spec k y x hy0 hx hk i (by omega)
    have hQ : x / 2 ^ (64 * k - i) / y < 2 ^ i := by
      have h1 : x / 2 ^ (64 * k - i) < 2 ^ i := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show i + (64 * k - i) = 64 * k by omega]
        exact hx
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h1
    have hb : (dvIter k y x i).1 / 2 ^ (64 * k - 1) % 2 = x / 2 ^ (64 * k - 1 - i) % 2 := by
      rw [ihX]; exact top_bit_of_register x _ i (64 * k) (by omega) hQ
    have hP' : x / 2 ^ (64 * k - (i + 1)) = 2 * (x / 2 ^ (64 * k - i)) + x / 2 ^ (64 * k - 1 - i) % 2 := by
      have e : 2 ^ (64 * k - i) = 2 ^ (64 * k - 1 - i) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      rw [show 64 * k - (i + 1) = 64 * k - 1 - i by omega, e, ← Nat.div_div_eq_div_mul]
      have := Nat.div_add_mod (x / 2 ^ (64 * k - 1 - i)) 2
      omega
    obtain ⟨a1, a2⟩ := div_step_arith (x / 2 ^ (64 * k - i)) y (x / 2 ^ (64 * k - 1 - i) % 2) hy0
      (Nat.mod_lt _ (by decide))
    show (dvNext k y (dvIter k y x i).1 (dvIter k y x i).2).2 = _ ∧ (dvNext k y (dvIter k y x i).1 (dvIter k y x i).2).1 = _
    simp only [dvNext, hb, ihR]
    rw [hP']
    refine ⟨a1.symm, ?_⟩
    rw [a2, ihX, mod_mul_add, Nat.pow_succ]
    congr 1
    rw [← Nat.mul_assoc]
    omega

end Gabbro.Stage0.Senke
