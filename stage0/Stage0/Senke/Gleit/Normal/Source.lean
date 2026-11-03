/- Preserve the canonical exact sum through signed sticky alignment. -/
module
public import Stage0.Senke.Gleit.Normal.Interval
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

private theorem signedScale (s : Bool) (n k : Nat) (e : Int) :
    rundeExakt f64 ⟨if s then -((n * 2 ^ k : Nat) : Int) else (n * 2 ^ k : Nat), e⟩ =
      rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), e + (k : Int)⟩ := by
  by_cases nz : n = 0
  · subst n
    rw [rundeExakt_null f64 _ (by cases s <;> simp),
      rundeExakt_null f64 _ (by cases s <;> simp)]
  · exact softRound_signed_mul_pow s n k e (by omega)

private theorem alignedCertificate (l r gap : Nat) (same : Bool)
    (even : l % 2 = 0) (ordered : softShiftJamNat r gap ≤ l)
    (cover : r ≤ l * 2 ^ gap) :
    let j := if same then l + softShiftJamNat r gap else l - softShiftJamNat r gap
    let n := if same then l * 2 ^ gap + r else l * 2 ^ gap - r
    (r % 2 ^ gap = 0 ∧ n = j * 2 ^ gap) ∨
      (j % 2 = 1 ∧ (j - 1) * 2 ^ gap < n ∧ n < (j + 1) * 2 ^ gap) := by
  dsimp only
  have dp := Nat.two_pow_pos gap
  have difference := Nat.sub_add_cancel ordered
  have differenceScaled := congrArg (fun n : Nat => n * 2 ^ gap) difference
  have numerator := Nat.sub_add_cancel cover
  rcases softShiftJamNat_interval r gap with exactValue | ⟨odd, lo, hi⟩
  · left
    refine ⟨exactValue.1, ?_⟩
    cases same <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · nlinarith [exactValue.2]
    · rw [Nat.add_mul, ← exactValue.2]
  · right
    have jp : 0 < softShiftJamNat r gap := by omega
    have jpred : softShiftJamNat r gap - 1 + 1 = softShiftJamNat r gap := by omega
    have jpredScaled := congrArg (fun n : Nat => n * 2 ^ gap) jpred
    cases same <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have parity := congrArg (fun n : Nat => n % 2) difference
      rw [Nat.add_mod, odd, even] at parity
      have positive : 0 < l - softShiftJamNat r gap := by omega
      have pred : l - softShiftJamNat r gap - 1 + 1 = l - softShiftJamNat r gap := by omega
      have predScaled := congrArg (fun n : Nat => n * 2 ^ gap) pred
      exact ⟨by omega, by nlinarith, by nlinarith⟩
    · have pred : l + softShiftJamNat r gap - 1 = l + (softShiftJamNat r gap - 1) := by omega
      refine ⟨by rw [Nat.add_mod, even, odd]; decide, ?_, ?_⟩
      · rw [pred, Nat.add_mul]
        omega
      · rw [Nat.add_mul] at *
        nlinarith

/-- The exact operands retain their full unbounded sum. Only its rounding
    is replaced by the routine's signed, three-guard-bit aligned magnitude.
    The inexact premise places a discarded tail below the normal rounding
    grid; exact alignment also covers cancellation and subnormal results. -/
theorem softRound_exaktAdd_aligned (sa sb : Bool) (l r gap : Nat) (e : Int)
    (cover : r ≤ l * 2 ^ gap)
    (ordered : softShiftJamNat (r * 8) gap ≤ l * 8)
    (inexact : (r * 8) % 2 ^ gap ≠ 0 →
      let j := if sa == sb then l * 8 + softShiftJamNat (r * 8) gap
        else l * 8 - softShiftJamNat (r * 8) gap
      2 ^ 54 ≤ j ∧ f64.emin ≤ e - 3 + (bitlen j : Int) - 1) :
    rundeExakt f64 (exaktAdd
      ⟨if sa then -(l : Int) else (l : Int), e⟩
      ⟨if sb then -(r : Int) else (r : Int), e - (gap : Int)⟩) =
      rundeExakt f64
        ⟨if sa then -((if sa == sb then l * 8 + softShiftJamNat (r * 8) gap
            else l * 8 - softShiftJamNat (r * 8) gap : Nat) : Int)
          else (if sa == sb then l * 8 + softShiftJamNat (r * 8) gap
            else l * 8 - softShiftJamNat (r * 8) gap : Nat), e - 3⟩ := by
  let same := sa == sb
  let n := if same then l * 2 ^ gap + r else l * 2 ^ gap - r
  let j := if same then l * 8 + softShiftJamNat (r * 8) gap
    else l * 8 - softShiftJamNat (r * 8) gap
  have sum : exaktAdd
      ⟨if sa then -(l : Int) else (l : Int), e⟩
      ⟨if sb then -(r : Int) else (r : Int), e - (gap : Int)⟩ =
      ⟨if sa then -(n : Int) else (n : Int), e - (gap : Int)⟩ := by
    have gapNat : (e - (e - (gap : Int))).toNat = gap := by omega
    rw [floatAdd_align]
    by_cases zero : gap = 0
    · subst gap
      simp only [Int.natCast_zero, sub_zero, le_refl, ite_true, sub_self,
        Int.toNat_zero, Nat.pow_zero, Nat.cast_one, mul_one]
      have sub : ((l - r : Nat) : Int) = (l : Int) - r := Int.ofNat_sub (by simpa using cover)
      cases sa <;> cases sb <;> simp [n, same, sub] <;> ring
    · rw [if_neg (by omega), gapNat]
      dsimp only
      have sub : ((l * 2 ^ gap - r : Nat) : Int) = (l : Int) * (2 ^ gap : Nat) - r := by
        rw [Int.ofNat_sub cover, Nat.cast_mul]
      cases sa <;> cases sb <;> simp [n, same, sub, Nat.cast_add, Nat.cast_mul] <;> ring
  rw [sum]
  have guarded : n * 2 ^ 3 =
      if same then (l * 8) * 2 ^ gap + r * 8 else (l * 8) * 2 ^ gap - r * 8 := by
    cases same <;> simp only [n, Bool.false_eq_true, ↓reduceIte]
    · have subtraction := Nat.sub_add_cancel cover
      have scaled := congrArg (fun n : Nat => n * 8) subtraction
      have cover8 : r * 8 ≤ (l * 8) * 2 ^ gap := by nlinarith
      have subtraction8 := Nat.sub_add_cancel cover8
      change (l * 2 ^ gap - r) * 8 = _
      nlinarith
    · change (l * 2 ^ gap + r) * 8 = _
      ring
  have replay : rundeExakt f64
      ⟨if sa then -((n * 2 ^ 3 : Nat) : Int) else (n * 2 ^ 3 : Nat),
        e - 3 - (gap : Int)⟩ =
      rundeExakt f64 ⟨if sa then -(n : Int) else (n : Int), e - (gap : Int)⟩ := by
    have result := signedScale sa n 3 (e - 3 - (gap : Int))
    have scale : e - 3 - (gap : Int) + (3 : Nat) = e - (gap : Int) := by omega
    rwa [scale] at result
  rw [← replay]
  rcases alignedCertificate (l * 8) (r * 8) gap same (by omega) ordered
    (by nlinarith) with exactValue | ⟨odd, lo, hi⟩
  · have exactN : n * 2 ^ 3 = j * 2 ^ gap := guarded.trans exactValue.2
    rw [exactN]
    have result := signedScale sa j gap (e - 3 - (gap : Int))
    have scale : e - 3 - (gap : Int) + (gap : Int) = e - 3 := by omega
    simpa only [scale] using result
  · by_cases tail : (r * 8) % 2 ^ gap = 0
    · have exactR : r * 8 = softShiftJamNat (r * 8) gap * 2 ^ gap := by
        unfold softShiftJamNat
        simp only [tail, ite_true, Nat.or_zero, Nat.shiftRight_eq_div_pow]
        have division := Nat.div_add_mod' (r * 8) (2 ^ gap)
        omega
      have exactN : n * 2 ^ 3 = j * 2 ^ gap := by
        rw [guarded]
        cases same <;> simp only [j, Bool.false_eq_true, ↓reduceIte] at *
        · have sub := Nat.sub_add_cancel ordered
          have subScaled := congrArg (fun n : Nat => n * 2 ^ gap) sub
          nlinarith
        · rw [Nat.add_mul, ← exactR]
      rw [exactN]
      have result := signedScale sa j gap (e - 3 - (gap : Int))
      have scale : e - 3 - (gap : Int) + (gap : Int) = e - 3 := by omega
      simpa only [scale] using result
    · obtain ⟨wide, normal⟩ := inexact tail
      exact softRound_signed_interval sa j (n * 2 ^ 3) gap (e - 3) wide normal
        (Or.inr ⟨odd, by simpa only [guarded] using lo, by simpa only [guarded] using hi⟩)

#print axioms softRound_exaktAdd_aligned
end Gabbro.Stage0.Senke
