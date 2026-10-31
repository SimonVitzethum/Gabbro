/-
  File:      stage0/Stage0/Senke/Ausdruck/Wide/Link.lean
  Subject:   The canonical integer encoding as a digit sequence.

  `integerEncoding k v` has the limb `lmb v j` at position `j`. Its digit sequence has the value
  `v mod 2^(64k)` (`dval_lmb`), and digit sequences of equal value are equal (`dval_inj`), so a
  carry chain that produces the right value produces exactly the canonical limbs.
-/
import Mathlib.Tactic.Linarith
import Stage0.Senke.Ausdruck.Aggregat.Encoding
import Stage0.Senke.Ausdruck.Wide.Limbs

namespace Gabbro.Stage0.Senke

/-- Limb `j` of the two's complement representation of `v`. -/
def lmb (v : Int) (j : Nat) : Runner.W := BitVec.ofInt 64 (v / 2 ^ (64 * j))

theorem lmb_shift (v : Int) (j : Nat) : lmb (v / 2 ^ 64) j = lmb v (j + 1) := by
  simp only [lmb]
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add, show 64 + 64 * j = 64 * (j + 1) by omega]

theorem integerEncoding_get (k : Nat) : ∀ (v : Int) (j : Nat) (h : j < (integerEncoding k v).length),
    (integerEncoding k v)[j] = lmb v j := by
  induction k with
  | zero => intro v j h; simp at h
  | succ k ih =>
    intro v j h
    cases j with
    | zero => simp [integerEncoding, lmb]
    | succ j =>
      simp only [integerEncoding, List.getElem_cons_succ]
      rw [ih (v / 2 ^ 64) j (by simpa using h), lmb_shift]

theorem lmb_toNat (v : Int) (j : Nat) :
    (lmb v j).toNat = ((v / 2 ^ (64 * j)) % 2 ^ 64).toNat := by
  simp [lmb]

/-- The Int modulus decomposition used by the limb recursion. -/
theorem int_mod_mul (v P N : Int) (hP : 0 < P) (hN : 0 < N) :
    v % (P * N) = v % P + P * ((v / P) % N) := by
  have e1 := Int.mul_ediv_add_emod v P
  have e2 := Int.mul_ediv_add_emod (v / P) N
  have e3 : P * (N * (v / P / N) + (v / P) % N) = P * (v / P) := by rw [e2]
  have h0 : 0 ≤ v % P := Int.emod_nonneg _ hP.ne'
  have h1 : v % P < P := Int.emod_lt_of_pos _ hP
  have h2 : 0 ≤ (v / P) % N := Int.emod_nonneg _ hN.ne'
  have h3 : (v / P) % N < N := Int.emod_lt_of_pos _ hN
  have h4 : 0 ≤ P * (N - 1 - (v / P) % N) := Int.mul_nonneg hP.le (by omega)
  have h5 : 0 ≤ P * ((v / P) % N) := Int.mul_nonneg hP.le h2
  have hq : v / P / N = v / (P * N) := Int.ediv_ediv_of_nonneg hP.le
  have := (Int.ediv_emod_unique (a := v) (b := P * N) (r := v % P + P * ((v / P) % N))
    (q := v / P / N) (Int.mul_pos hP hN)).mpr
    ⟨by linarith, by linarith, by linarith⟩
  exact this.2

theorem dval_lmb (v : Int) : ∀ k : Nat,
    dval (fun j => (lmb v j).toNat) k = (v % 2 ^ (64 * k)).toNat
  | 0 => by simp [dval]
  | k + 1 => by
    rw [dval_succ, dval_lmb v k, lmb_toNat]
    have hP : (0 : Int) < 2 ^ (64 * k) := by positivity
    have hN : (0 : Int) < 2 ^ 64 := by positivity
    have e : (2 : Int) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
      rw [Nat.mul_succ, pow_add]
    rw [e, int_mod_mul v _ _ hP hN]
    have h1 : 0 ≤ v % 2 ^ (64 * k) := Int.emod_nonneg _ hP.ne'
    have h2 : 0 ≤ (v / 2 ^ (64 * k)) % 2 ^ 64 := Int.emod_nonneg _ hN.ne'
    rw [Int.toNat_add h1 (Int.mul_nonneg hP.le h2), Int.toNat_mul hP.le h2,
      Int.toNat_pow_of_nonneg (by norm_num)]
    simp only [Nat.mul_comm]
    rfl

end Gabbro.Stage0.Senke
