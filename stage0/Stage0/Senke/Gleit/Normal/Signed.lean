/- Transport signed exact dyadics through the canonical rounding replay. -/
module
public import Stage0.Senke.Gleit.Normal.Aligned
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

private theorem signedData (s : Bool) (n : Nat) (positive : 0 < n) :
    (if s then -(n : Int) else (n : Int)) ≠ 0 ∧
      (if s then -(n : Int) else (n : Int)).natAbs = n ∧
      decide ((if s then -(n : Int) else (n : Int)) < 0) = s := by
  cases s <;> simp [positive, show n ≠ 0 by omega]

/-- The replay depends on the sign, the positioned leading bit, and the
    rounded significand. A subnormal decision is needed only below `emin`. -/
theorem softRound_signed_congr (s : Bool) (n₁ n₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < n₁) (positive₂ : 0 < n₂)
    (position : e₁ + (bitlen n₁ : Int) = e₂ + (bitlen n₂ : Int))
    (normal : softRoundDyadic n₁ (53 - (bitlen n₁ : Int)) =
      softRoundDyadic n₂ (53 - (bitlen n₂ : Int)))
    (subnormal : e₂ + (bitlen n₂ : Int) - 1 < f64.emin →
      softRoundDyadic n₁ (e₁ + 1074) = softRoundDyadic n₂ (e₂ + 1074)) :
    rundeExakt f64 ⟨if s then -(n₁ : Int) else (n₁ : Int), e₁⟩ =
      rundeExakt f64 ⟨if s then -(n₂ : Int) else (n₂ : Int), e₂⟩ := by
  obtain ⟨nz₁, mag₁, sign₁⟩ := signedData s n₁ positive₁
  obtain ⟨nz₂, mag₂, sign₂⟩ := signedData s n₂ positive₂
  have first := softRound_replay_all (if s then -(n₁ : Int) else (n₁ : Int)) e₁ nz₁
  have second := softRound_replay_all (if s then -(n₂ : Int) else (n₂ : Int)) e₂ nz₂
  dsimp only at first second
  rw [mag₁, sign₁, position, normal] at first
  rw [mag₂, sign₂] at second
  by_cases above : f64.emin ≤ e₂ + (bitlen n₂ : Int) - 1
  · simp only [if_pos above] at first second
    exact first.trans second.symm
  · rw [subnormal (by omega)] at first
    exact first.trans second.symm

/-- Lossless normalization is exact even when it crosses the normal versus
    subnormal boundary. This equality retains the canonical overflow cases. -/
theorem softRound_signed_mul_pow (s : Bool) (n t : Nat) (e : Int)
    (positive : 0 < n) :
    rundeExakt f64 ⟨if s then -((n * 2 ^ t : Nat) : Int) else (n * 2 ^ t : Nat), e⟩ =
      rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), e + (t : Int)⟩ := by
  apply softRound_signed_congr s (n * 2 ^ t) n e (e + (t : Int))
    (Nat.mul_pos positive (Nat.two_pow_pos _)) positive
  · rw [bitlen_mul_pow2 n t positive]
    push_cast
    ring
  · rw [bitlen_mul_pow2 n t positive, softRoundDyadic_mul_pow]
    congr 1
    push_cast
    ring
  · intro _
    rw [softRoundDyadic_mul_pow]
    congr 1
    ring

/-- Exact left normalization at the subnormal floor and a wide overflowing
    numerator exercise the premises jointly for both signs. -/
theorem softRound_signed_mul_pow_zeuge :
    rundeExakt f64 ⟨-(16 * 2 ^ 2 : Int), -1079⟩ =
      rundeExakt f64 ⟨-16, -1077⟩ ∧
    rundeExakt f64 ⟨(2 ^ 54 - 2 : Int) * 2 ^ 80, 891⟩ =
      rundeExakt f64 ⟨2 ^ 54 - 2, 971⟩ := by
  decide +kernel

#print axioms softRound_signed_congr
#print axioms softRound_signed_mul_pow
#print axioms softRound_signed_mul_pow_zeuge
end Gabbro.Stage0.Senke
