/- Leading-bit and canonical rounding preservation of an aligned interval. -/
module
public import Stage0.Senke.Gleit.Normal.Signed
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Powers of two cannot lie strictly between the adjacent even endpoints
    of an odd interval above one. Alignment therefore preserves the leading
    bit position as well as the eventual rounding decision. -/
theorem bitlen_odd_interval (j n gap : Nat) (jp : 2 ≤ j)
    (odd : j % 2 = 1) (lo : (j - 1) * 2 ^ gap < n)
    (hi : n < (j + 1) * 2 ^ gap) :
    bitlen n = bitlen j + gap := by
  have upper := bitlen_obere j
  have lower := bitlen_untere j (by omega : j ≠ 0)
  have bits : 2 ≤ bitlen j := by
    by_contra h
    have power := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show bitlen j ≤ 1 by omega)
    omega
  have lowPower : 2 ^ (bitlen j - 1) = 2 * 2 ^ (bitlen j - 2) := by
    rw [show bitlen j - 1 = (bitlen j - 2) + 1 by omega,
      Nat.pow_succ, Nat.mul_comm]
  have highPower : 2 ^ bitlen j = 2 * 2 ^ (bitlen j - 1) := by
    rw [show bitlen j = (bitlen j - 1) + 1 by omega,
      Nat.pow_succ, Nat.mul_comm]
  have powerEven : 2 ^ (bitlen j - 1) % 2 = 0 := by rw [lowPower]; omega
  have different : 2 ^ (bitlen j - 1) ≠ j := by
    intro same
    rw [same, odd] at powerEven
    cases powerEven
  have below : 2 ^ (bitlen j - 1) ≤ j - 1 := by rw [highPower] at lower; omega
  have lowScaled := Nat.mul_le_mul_right (2 ^ gap) below
  have highScaled := Nat.mul_le_mul_right (2 ^ gap) (show j + 1 ≤ 2 ^ bitlen j by omega)
  apply bitlen_unique n (bitlen j + gap)
  · have power : 2 ^ (bitlen j + gap - 1) = 2 ^ (bitlen j - 1) * 2 ^ gap := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [power]
    omega
  · rw [Nat.pow_add]
    omega
  · omega

/-- In the normal range an exact scaled numerator or its odd sticky
    certificate produces the same canonical binary64 result. The bound
    leaves two bits below the normal significand's rounding position. -/
theorem softRound_signed_interval (s : Bool) (j n gap : Nat) (e : Int)
    (wide : 2 ^ 54 ≤ j)
    (normal : f64.emin ≤ e + (bitlen j : Int) - 1)
    (certificate : n = j * 2 ^ gap ∨
      (j % 2 = 1 ∧ (j - 1) * 2 ^ gap < n ∧ n < (j + 1) * 2 ^ gap)) :
    rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), e - (gap : Int)⟩ =
      rundeExakt f64 ⟨if s then -(j : Int) else (j : Int), e⟩ := by
  have jp : 0 < j := by omega
  rcases certificate with exactValue | ⟨odd, lo, hi⟩
  · subst n
    have result := softRound_signed_mul_pow s j gap (e - (gap : Int)) jp
    simpa only [sub_add_cancel] using result
  · have bits := bitlen_odd_interval j n gap (by omega) odd lo hi
    have enough : 55 ≤ bitlen j := by
      have bound := bitlen_obere j
      by_contra h
      have power := Nat.pow_le_pow_right (by decide : 0 < 2)
        (show bitlen j ≤ 54 by omega)
      omega
    apply softRound_signed_congr s n j (e - (gap : Int)) e (by omega) jp
    · rw [bits]
      push_cast
      ring
    · have result := softRoundDyadic_odd_interval j n gap (bitlen j - 53)
        (by omega) odd lo hi
      have leftScale : -((gap + (bitlen j - 53) : Nat) : Int) =
          53 - (bitlen n : Int) := by rw [bits]; omega
      have rightScale : -((bitlen j - 53 : Nat) : Int) =
          53 - (bitlen j : Int) := by omega
      rwa [leftScale, rightScale] at result
    · intro below
      omega

/-- A numerator far wider than a machine word, and the negative direction,
    satisfy the same canonical rounding certificate. -/
theorem softRound_signed_interval_zeuge :
    rundeExakt f64 ⟨2 ^ 55 * 2 ^ 1022 + 8, -1077⟩ =
      rundeExakt f64 ⟨2 ^ 55 + 1, -55⟩ ∧
    rundeExakt f64 ⟨-((2 ^ 55 - 1) * 8 + 1 : Int), -58⟩ =
      rundeExakt f64 ⟨-(2 ^ 55 - 1 : Int), -55⟩ := by
  decide +kernel

#print axioms bitlen_odd_interval
#print axioms softRound_signed_interval
#print axioms softRound_signed_interval_zeuge
end Gabbro.Stage0.Senke
