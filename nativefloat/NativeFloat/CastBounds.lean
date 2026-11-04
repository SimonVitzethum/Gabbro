/- Complete outer branches of the portable native saturating casts. -/
module
public import NativeFloat.CastDecode
import all NativeFloat.CastCore
import all NativeFloat.CastDecode
import all NativeFloat.Transport
@[expose] public section

namespace RootNativeFloat.CastBounds
open Float.Model
open Float.Model.UnpackedFloat
open CastCore CastDecode

private theorem decoded_cvtt (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits)
    (small : (word &&& magnitudeMask F).ult (limitBits F 63) = true) :
    Domain F (UnpackedFloat.unpack F word) := by
  apply small_cases F standard word
  · intro s _
    exact cvtt_zero F s
  · intro s m e h _ _ exponent
    exact cvtt_small F s m e h exponent
  · exact small

private theorem decoded_signed_overflow (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits)
    (nan : (packedInfinity F .positive).ult (word &&& magnitudeMask F) = false)
    (large : (word &&& magnitudeMask F).ult (limitBits F 63) = false) :
    (UnpackedFloat.unpack F word).toInt64.toBitVec =
      if word.msb then 0x8000000000000000 else 0x7fffffffffffffff := by
  apply overflow_cases F standard word 63 (by decide) (by decide)
  · intro s sign
    rw [sign]
    cases s <;> rfl
  · intro s m e h sign lower exponent
    have room : F.mantissaBitsWithoutImplicit ≤ 63 := by rcases standard with rfl | rfl <;> decide
    have magnitude := magnitude_large _ 63 m e room lower exponent
    rw [finite_signed_overflow s m e h magnitude, sign]
    cases s <;> rfl
  · exact nan
  · exact large

private theorem decoded_negative_unsigned (F : Format) (word : BitVec F.numBits)
    (negative : word.msb = true) : (UnpackedFloat.unpack F word).toUInt64.toBitVec = 0 := by
  apply with_fields F word (P := fun word => word.msb = true →
    (UnpackedFloat.unpack F word).toUInt64.toBitVec = 0) ?_ negative
  intro s e m sign
  rw [sign_fields] at sign
  cases s
  · simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpack_sign_components, sign_unbits]
    split
    · split <;> rfl
    · split
      · split
        · rfl
        · rw [negative_unsigned]
          rfl
      · rw [negative_unsigned]
        rfl
  · cases sign

private theorem decoded_unsigned_low (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) (nonnegative : word.msb = false)
    (small : (word &&& magnitudeMask F).ult (limitBits F 63) = true) :
    (UnpackedFloat.unpack F word).toUInt64.toBitVec =
      (UnpackedFloat.unpack F word).toInt64.toBitVec := by
  apply small_cases F standard word
  · intro s _
    cases s <;> rfl
  · intro s m e h sign upper exponent
    have room : F.mantissaBitsWithoutImplicit < 63 := by rcases standard with rfl | rfl <;> decide
    have bound := magnitude_small _ m e room upper exponent
    cases s
    · rw [nonnegative] at sign
      change false = true at sign
      cases sign
    · exact positive_low m e h bound
  · exact small

private theorem decoded_unsigned_overflow (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) (nonnegative : word.msb = false)
    (nan : (packedInfinity F .positive).ult (word &&& magnitudeMask F) = false)
    (large : (word &&& magnitudeMask F).ult (limitBits F 64) = false) :
    (UnpackedFloat.unpack F word).toUInt64.toBitVec = -1#64 := by
  apply overflow_cases F standard word 64 (by decide) (by decide)
  · intro s sign
    cases s
    · rw [nonnegative] at sign
      change false = true at sign
      cases sign
    · rfl
  · intro s m e h sign lower exponent
    have room : F.mantissaBitsWithoutImplicit ≤ 64 := by rcases standard with rfl | rfl <;> decide
    have magnitude := magnitude_large _ 64 m e room lower exponent
    cases s
    · rw [nonnegative] at sign
      change false = true at sign
      cases sign
    · exact finite_unsigned_overflow m e h magnitude
  · exact nan
  · exact large

end RootNativeFloat.CastBounds
