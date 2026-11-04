/- Actual stored-word cases for the native saturating cast proofs. -/
module
public import NativeFloat.CastCore
import all NativeFloat.CastCore
import all NativeFloat.Transport
@[expose] public section

namespace RootNativeFloat.CastDecode
open Float.Model
open Float.Model.UnpackedFloat

private abbrev magnitudeMask (F : Format) : BitVec F.numBits :=
  (0#1 ++ (-1#F.exponentBits)) ++ (-1#F.mantissaBitsWithoutImplicit)

private abbrev limitBits (F : Format) (b : Nat) : BitVec F.numBits :=
  packComponents F .positive (BitVec.ofNat _ (F.exponentBias + b)) 0#_

private abbrev Domain (F : Format) (x : UnpackedFloat) : Prop :=
  x.isNaN = false ∧
    x.lt (.finite .negative (2 ^ F.mantissaBitsWithoutImplicit)
      (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = false ∧
    x.lt (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
      (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = true

private theorem fields_nat (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    (packComponents F s e m).toNat =
      (s.toBitVec.toNat * 2 ^ F.exponentBits + e.toNat) * 2 ^ F.mantissaBitsWithoutImplicit + m.toNat := by
  unfold packComponents
  rw [BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt m.isLt, ← Nat.shiftLeft_add_eq_or_of_lt e.isLt]
  simp only [Nat.shiftLeft_eq]

private theorem magnitude_fields (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    (packComponents F s e m &&& magnitudeMask F).toNat =
      e.toNat * 2 ^ F.mantissaBitsWithoutImplicit + m.toNat := by
  have erased : packComponents F s e m &&& magnitudeMask F = packComponents F .positive e m := by
    simp only [packComponents, magnitudeMask, Sign.toBitVec, BitVec.and_append, BitVec.and_zero,
      BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
  rw [erased, fields_nat]
  simp only [Sign.toBitVec, BitVec.toNat_zero, Nat.zero_mul, Nat.zero_add]

private theorem sign_fields (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    (packComponents F s e m).msb = decide (s = .negative) := by
  cases s <;> simp [packComponents, BitVec.msb_append, Sign.toBitVec]

private theorem threshold_nat (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (b : Nat) (bound : b ≤ 64) :
    (limitBits F b).toNat = (F.exponentBias + b) * 2 ^ F.mantissaBitsWithoutImplicit := by
  have fits : F.exponentBias + b < 2 ^ F.exponentBits := by
    rcases standard with rfl | rfl <;> dsimp [Format.exponentBias] <;> omega
  rw [fields_nat]
  simp only [Sign.toBitVec, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt fits, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

private theorem infinity_nat (F : Format) :
    (packedInfinity F .positive).toNat = (2 ^ F.exponentBits - 1) * 2 ^ F.mantissaBitsWithoutImplicit := by
  have mantissaZero : (0 : BitVec F.mantissaBitsWithoutImplicit).toNat = 0 := by
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  rw [packedInfinity, fields_nat]
  simp only [Sign.toBitVec, BitVec.toNat_zero, mantissaZero, BitVec.neg_one_eq_allOnes,
    BitVec.toNat_allOnes, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

private theorem range_guard (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (s : Sign) (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit)
    (b : Nat) (bound : b ≤ 64) :
    (packComponents F s e m &&& magnitudeMask F).ult (limitBits F b) =
      decide (e.toNat < F.exponentBias + b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, magnitude_fields, threshold_nat F standard b bound]
  have mb := m.isLt
  rcases standard with rfl | rfl <;> dsimp [Format.exponentBias] at * <;> omega

private theorem nan_guard (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (s : Sign) (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    (packedInfinity F .positive).ult (packComponents F s e m &&& magnitudeMask F) =
      decide (e = -1#_ ∧ m ≠ 0#_) := by
  have exponent : e = -1#_ ↔ e.toNat = 2 ^ F.exponentBits - 1 := by
    constructor
    · intro h
      simp only [h, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
    · intro h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] using h
  have mantissa : m ≠ 0#_ ↔ m.toNat ≠ 0 := by
    constructor
    · intro h zero
      exact h (BitVec.eq_of_toNat_eq (by simpa using zero))
    · intro h zero
      exact h (by simp only [zero, BitVec.toNat_zero])
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, magnitude_fields, infinity_nat, exponent, mantissa]
  have eb := e.isLt
  have mb := m.isLt
  rcases standard with rfl | rfl <;> dsimp at * <;> omega

private theorem with_fields (F : Format) (word : BitVec F.numBits) {P : BitVec F.numBits → Prop}
    (fields : ∀ s e m, P (packComponents F s e m)) : P word := by
  rw [← components_roundtrip F word]
  exact fields _ _ _

private theorem leading_mantissa (F : Format) (m : BitVec F.mantissaBitsWithoutImplicit) :
    (1#1 ++ m).toNat = 2 ^ F.mantissaBitsWithoutImplicit + m.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_one (by decide : 0 < 1), Nat.one_mul]

private theorem decoded_nan (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits)
    (nan : (packedInfinity F .positive).ult (word &&& magnitudeMask F) = true) :
    UnpackedFloat.unpack F word = .notANumber := by
  apply with_fields F word (P := fun word =>
    (packedInfinity F .positive).ult (word &&& magnitudeMask F) = true →
      UnpackedFloat.unpack F word = .notANumber) ?_ nan
  intro s e m hn
  rw [nan_guard F standard] at hn
  have fields := of_decide_eq_true hn
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpack_sign_components, sign_unbits, fields.1, fields.2, ↓reduceIte]

private theorem small_cases (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) {P : UnpackedFloat → Prop}
    (zero : ∀ s, word.msb = decide (s = .negative) → P (.zero s))
    (finite : ∀ s m e h, word.msb = decide (s = .negative) →
      m < 2 ^ (F.mantissaBitsWithoutImplicit + 1) → e < 63 - (F.mantissaBitsWithoutImplicit : Int) →
      P (.finite s m e h))
    (small : (word &&& magnitudeMask F).ult (limitBits F 63) = true) :
    P (UnpackedFloat.unpack F word) := by
  apply with_fields F word (P := fun word =>
    (∀ s, word.msb = decide (s = .negative) → P (.zero s)) →
    (∀ s m e h, word.msb = decide (s = .negative) →
      m < 2 ^ (F.mantissaBitsWithoutImplicit + 1) → e < 63 - (F.mantissaBitsWithoutImplicit : Int) →
      P (.finite s m e h)) →
    (word &&& magnitudeMask F).ult (limitBits F 63) = true → P (UnpackedFloat.unpack F word))
    ?_ zero finite small
  intro s e m hz hf hs
  rw [range_guard F standard _ _ _ 63 (by decide)] at hs
  have eb : e.toNat < F.exponentBias + 63 := of_decide_eq_true hs
  have notMax : e ≠ -1#_ := by
    intro eq
    have value : e.toNat = 2 ^ F.exponentBits - 1 := by
      simp only [eq, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
    rcases standard with rfl | rfl <;> dsimp [Format.exponentBias] at * <;> omega
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpack_sign_components, sign_unbits, notMax, ↓reduceIte]
  split
  · next isZero =>
      split
      · exact hz s (sign_fields F s e m)
      · apply hf s _ _ _ (sign_fields F s e m)
        · exact Nat.lt_of_lt_of_le m.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
        · have bias : 0 < F.exponentBias := by rcases standard with rfl | rfl <;> decide
          simp only [isZero, BitVec.toNat_zero, Int.natCast_zero]
          omega
  · apply hf s _ _ _ (sign_fields F s e m)
    · have bound := (1#1 ++ m).isLt
      simpa only [Nat.add_comm] using bound
    · omega

private theorem overflow_cases (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) (b : Nat) (bottom : 63 ≤ b) (top : b ≤ 64)
    {P : UnpackedFloat → Prop}
    (infinite : ∀ s, word.msb = decide (s = .negative) → P (.infinity s))
    (finite : ∀ s m e h, word.msb = decide (s = .negative) →
      2 ^ F.mantissaBitsWithoutImplicit ≤ m → (b : Int) - F.mantissaBitsWithoutImplicit ≤ e →
      P (.finite s m e h))
    (nan : (packedInfinity F .positive).ult (word &&& magnitudeMask F) = false)
    (large : (word &&& magnitudeMask F).ult (limitBits F b) = false) :
    P (UnpackedFloat.unpack F word) := by
  apply with_fields F word (P := fun word =>
    (∀ s, word.msb = decide (s = .negative) → P (.infinity s)) →
    (∀ s m e h, word.msb = decide (s = .negative) →
      2 ^ F.mantissaBitsWithoutImplicit ≤ m → (b : Int) - F.mantissaBitsWithoutImplicit ≤ e →
      P (.finite s m e h)) →
    (packedInfinity F .positive).ult (word &&& magnitudeMask F) = false →
    (word &&& magnitudeMask F).ult (limitBits F b) = false → P (UnpackedFloat.unpack F word))
    ?_ infinite finite nan large
  intro s e m hi hf hn hl
  rw [range_guard F standard _ _ _ b top] at hl
  have eb : F.exponentBias + b ≤ e.toNat := by
    have bad : ¬ e.toNat < F.exponentBias + b := of_decide_eq_false hl
    omega
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpack_sign_components, sign_unbits]
  by_cases maximal : e = -1#_
  · rw [if_pos maximal]
    have zero : m = 0#_ := by
      rw [nan_guard F standard] at hn
      have absent : ¬ (e = -1#_ ∧ m ≠ 0#_) := of_decide_eq_false hn
      by_cases eq : m = 0#_
      · exact eq
      · exact False.elim (absent ⟨maximal, eq⟩)
    rw [if_pos zero]
    exact hi s (sign_fields F s e m)
  · rw [if_neg maximal]
    have nonzero : e ≠ 0#_ := by
      intro eq
      simp only [eq, BitVec.toNat_zero] at eb
      omega
    rw [if_neg nonzero]
    apply hf s _ _ _ (sign_fields F s e m)
    · rw [leading_mantissa]
      omega
    · omega

private theorem repack_unpack (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) :
    UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.unpack F word)) =
      UnpackedFloat.unpack F word := by
  by_cases nan : UnpackedFloat.unpack F word = .notANumber
  · rw [nan]
    rcases standard with rfl | rfl <;> rfl
  · rw [pack_unpack F word (valid_of_not_nan F word nan)]

end RootNativeFloat.CastDecode
