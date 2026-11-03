/- A normalized product's sticky certificate is sufficient at every scale.
   This extends the adder's normal-range interval argument to underflow. -/
module
public import Stage0.Senke.Gleit.Mul.Underflow
public import Stage0.Senke.Gleit.Normal.Interval
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- With bit 55 retained there are three guard bits on the normal path,
    and at least four on every subnormal path. The same sticky interval
    therefore reproduces all branches of the general rounding replay. -/
theorem softMulRound_interval (s : Bool) (m n gap : Nat) (e : Int)
    (ml : 2 ^ 55 ≤ m) (mb : m < 2 ^ 56)
    (certificate : n = m * 2 ^ gap ∨
      (m % 2 = 1 ∧ (m - 1) * 2 ^ gap < n ∧ n < (m + 1) * 2 ^ gap)) :
    rundeExakt f64 ⟨if s then -(n : Int) else n, e - (gap : Int)⟩ =
      rundeExakt f64 ⟨if s then -(m : Int) else m, e⟩ := by
  have mp : 0 < m := by omega
  have bits : bitlen m = 56 := bitlen_unique m 56 ml mb (by decide)
  by_cases normal : f64.emin ≤ e + (bitlen m : Int) - 1
  · exact softRound_signed_interval s m n gap e (by omega) normal certificate
  · have lowScale : e < -1077 := by
      rw [bits] at normal
      change ¬ (-1022 : Int) ≤ e + (56 : Nat) - 1 at normal
      omega
    rcases certificate with exactValue | ⟨odd, lo, hi⟩
    · subst n
      have result := softRound_signed_mul_pow s m gap (e - (gap : Int)) mp
      simpa only [sub_add_cancel] using result
    · have nbits := bitlen_odd_interval m n gap (by omega) odd lo hi
      apply softRound_signed_congr s n m (e - (gap : Int)) e (by
        have lower := Nat.zero_le ((m - 1) * 2 ^ gap)
        omega) mp
      · rw [nbits]
        omega
      · have result := softRoundDyadic_odd_interval m n gap 3 (by decide) odd lo hi
        rw [bits] at nbits
        have left : -((gap + 3 : Nat) : Int) = 53 - (bitlen n : Int) := by omega
        have right : -(3 : Int) = 53 - (bitlen m : Int) := by rw [bits]
        rwa [left, right] at result
      · intro _
        let k := (-e - 1074).toNat
        have guard : 2 ≤ k := by dsimp only [k]; omega
        have result := softRoundDyadic_odd_interval m n gap k guard odd lo hi
        have left : -((gap + k : Nat) : Int) = e - (gap : Int) + 1074 := by
          dsimp only [k]
          omega
        have right : -(k : Int) = e + 1074 := by dsimp only [k]; omega
        rwa [left, right] at result

/-- Compressing the actual two-limb product retains the canonical rounded
    result even when the eventual exponent is below the subnormal floor. -/
theorem softMulCompress_round (s : Bool) (a b : Runner.W) (k : Nat) (e : Int)
    (count : k = 49 ∨ k = 50)
    (low : 2 ^ (k + 55) ≤ a.toNat * b.toNat)
    (high : a.toNat * b.toNat < 2 ^ (k + 56)) :
    rundeExakt f64 ⟨if s then -((a.toNat * b.toNat : Nat) : Int)
      else (a.toNat * b.toNat : Nat), e - (k : Int)⟩ =
      rundeExakt f64 ⟨if s then -((softMulCompressWord a b k).toNat : Int)
      else (softMulCompressWord a b k).toNat, e⟩ := by
  have bounds := softMulJam_bounds (a.toNat * b.toNat) k count low high
  have result := softMulRound_interval s (softShiftJamNat (a.toNat * b.toNat) k)
    (a.toNat * b.toNat) k e bounds.1 bounds.2 (by
      rcases softShiftJamNat_interval (a.toNat * b.toNat) k with exactValue | jam
      · exact Or.inl exactValue.2
      · exact Or.inr jam)
  rw [softMulCompressWord_model a b k count low high, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : softShiftJamNat (a.toNat * b.toNat) k < 2 ^ 64)]
  exact result

/-- The exact product normalization moves both operand shifts into the
    binary scale. This uses the same lossless scaling lemma as addition. -/
theorem softMulNormalize_round (s : Bool) (a b ca cb : Nat) (e : Int)
    (ap : 0 < a) (bp : 0 < b) :
    rundeExakt f64 ⟨if s then -(((a * 2 ^ ca) * (b * 2 ^ cb) : Nat) : Int)
      else ((a * 2 ^ ca) * (b * 2 ^ cb) : Nat), e - (ca : Int) - (cb : Int)⟩ =
      rundeExakt f64 ⟨if s then -((a * b : Nat) : Int) else (a * b : Nat), e⟩ := by
  have product : (a * 2 ^ ca) * (b * 2 ^ cb) = (a * b) * 2 ^ (ca + cb) := by
    rw [Nat.pow_add]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [product]
  have result := softRound_signed_mul_pow s (a * b) (ca + cb)
    (e - (ca : Int) - (cb : Int)) (Nat.mul_pos ap bp)
  have scale : e - (ca : Int) - (cb : Int) + ((ca + cb : Nat) : Int) = e := by omega
  rwa [scale] at result

#print axioms softMulRound_interval
#print axioms softMulCompress_round
#print axioms softMulNormalize_round
end Gabbro.Stage0.Senke
