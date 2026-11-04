/- Proof adapters for the toolchain's native float word representation. -/
module
public import Init.Data.Float
import Init.Data.UInt.Bitwise
@[expose] public section

namespace RootNativeFloat
open Float.Model Float.Model.UnpackedFloat

private theorem sign_roundtrip (b : BitVec 1) : Sign.toBitVec (Sign.ofBitVec b) = b := by
  rcases b with ⟨⟨n, hn⟩⟩
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl <;> rfl

private theorem components_roundtrip (F : Format) (b : BitVec F.numBits) :
    packComponents F (Sign.ofBitVec (unpackSign (spec := F) b))
      (unpackExponent (spec := F) b) (unpackMantissa (spec := F) b) = b := by
  unfold packComponents
  rw [sign_roundtrip]
  ext i hi
  simp only [unpackSign, unpackExponent, unpackMantissa, BitVec.getElem_append,
    BitVec.getElem_extractLsb', Nat.zero_add]
  split
  · exact (BitVec.getLsbD_eq_getElem (x := b) (i := i) hi).symm
  · rename_i hm
    split
    · have e : F.mantissaBitsWithoutImplicit + (i - F.mantissaBitsWithoutImplicit) = i := by omega
      simpa only [e] using (BitVec.getLsbD_eq_getElem (x := b) (i := i) hi)
    · have e : F.mantissaBitsWithoutImplicit + F.exponentBits +
          (i - F.mantissaBitsWithoutImplicit - F.exponentBits) = i := by omega
      rw [e]
      exact BitVec.getLsbD_eq_getElem hi

/-- The toolchain pack/unpack boundary is an inverse on its own valid words.
    This proves storage transport only; it defines no arithmetic or rounding. -/
theorem pack_unpack (F : Format) (b : BitVec F.numBits) (valid : F.Valid b) :
    UnpackedFloat.pack F (UnpackedFloat.unpack F b) = b := by
  let e := unpackExponent (spec := F) b
  let m := unpackMantissa (spec := F) b
  let s := Sign.ofBitVec (unpackSign (spec := F) b)
  have reassemble := components_roundtrip F b
  change packComponents F s e m = b at reassemble
  have eb : e.toNat < 2 ^ F.exponentBits := e.isLt
  have mb : m.toNat < 2 ^ F.mantissaBitsWithoutImplicit := m.isLt
  have expRoom : 4 ≤ 2 ^ F.exponentBits :=
    Nat.pow_le_pow_right (by decide : 0 < 2) F.he
  have zeroNotMax : (0#F.exponentBits) ≠ -1#F.exponentBits := by
    intro h
    have := BitVec.zero_eq_neg_one_iff.mp h
    have := F.he
    omega
  by_cases heMax : e = -1#_
  · by_cases hm : m = 0#_
    · simpa only [UnpackedFloat.unpack, e, m, s, heMax, hm, ↓reduceIte,
        UnpackedFloat.pack, packedInfinity, BitVec.ofNat_eq_ofNat] using reassemble
    · have canonical : b = packedNaN F := valid.eq_packedNaN heMax hm
      simpa only [UnpackedFloat.unpack, e, m, s, heMax, hm, ↓reduceIte,
        UnpackedFloat.pack] using canonical.symm
  · have eNotMax : e.toNat ≠ 2 ^ F.exponentBits - 1 := by
      intro h
      apply heMax
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] using h
    by_cases heZero : e = 0#_
    · by_cases hm : m = 0#_
      · simpa only [UnpackedFloat.unpack, e, m, s, heMax, heZero, hm, ↓reduceIte,
          zeroNotMax, ↓reduceDIte, UnpackedFloat.pack, packedZero, BitVec.ofNat_eq_ofNat] using reassemble
      · have positive : m.toNat ≠ 0 := by
          intro h
          apply hm
          apply BitVec.eq_of_toNat_eq
          simpa using h
        have smallLog : m.toNat.log2 < F.mantissaBitsWithoutImplicit := (Nat.log2_lt positive).mpr mb
        have exponent : ((0 : Int) - (F.exponentBias + F.mantissaBitsWithoutImplicit) + 1 +
            F.exponentBias + F.mantissaBitsWithoutImplicit).toNat = 1 := by omega
        simpa only [UnpackedFloat.unpack, e, m, s, heMax, heZero, hm, zeroNotMax,
          ↓reduceIte, ↓reduceDIte, UnpackedFloat.pack,
          BitVec.toNat_zero, Int.natCast_zero, exponent, show ¬ 2 ^ F.exponentBits ≤ 1 + 1 by omega,
          show m.toNat.log2 + 1 ≠ F.mantissaBits by unfold Format.mantissaBits; omega,
          BitVec.ofNat_toNat, BitVec.setWidth_eq] using reassemble
    · have ep : 0 < e.toNat := by
        have nonzero : e.toNat ≠ 0 := by
          intro h
          apply heZero
          apply BitVec.eq_of_toNat_eq
          simpa using h
        omega
      have magnitude : (1#1 ++ m).toNat = 2 ^ F.mantissaBitsWithoutImplicit + m.toNat := by
        rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt mb, Nat.shiftLeft_eq]
        simp
      have log : (1#1 ++ m).toNat.log2 = F.mantissaBitsWithoutImplicit := by
        apply (Nat.log2_eq_iff (by rw [magnitude]; have := Nat.two_pow_pos F.mantissaBitsWithoutImplicit; omega)).mpr
        rw [magnitude, Nat.pow_succ]
        omega
      have exponent : ((e.toNat : Int) - (F.exponentBias + F.mantissaBitsWithoutImplicit) +
          F.exponentBias + F.mantissaBitsWithoutImplicit).toNat = e.toNat := by omega
      have mantissa : BitVec.ofNat F.mantissaBitsWithoutImplicit (1#1 ++ m).toNat = m := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, magnitude, Nat.add_mod, Nat.mod_self,
          Nat.zero_add, Nat.mod_eq_of_lt mb]
      have noOverflow : ¬ 2 ^ F.exponentBits ≤ e.toNat + 1 := by omega
      have width : F.mantissaBitsWithoutImplicit + 1 = F.mantissaBits := by
        simp only [Format.mantissaBits, Nat.add_comm]
      simpa only [UnpackedFloat.unpack, e, m, s, heMax, heZero, ↓reduceIte, UnpackedFloat.pack, exponent,
        noOverflow, log, width, ↓reduceIte, mantissa,
        BitVec.ofNat_toNat, BitVec.setWidth_eq] using reassemble

/-- Complete native binary64 values survive their canonical word encoding. -/
theorem bits_roundtrip (x : Float) : Float.ofBits x.toBits = x := by
  rcases x with ⟨⟨bits, valid⟩⟩
  change Float.ofModel (Float.Model.ofBits bits) = Float.ofModel ⟨bits, valid⟩
  apply congrArg Float.ofModel
  have same : (Float.Model.ofBits bits).toBits = bits := by
    apply UInt64.eq_of_toBitVec_eq
    exact pack_unpack Format.binary64 bits.toBitVec valid
  cases decoded : Float.Model.ofBits bits with
  | mk raw proof =>
      have rawEq : raw = bits := by simpa only [decoded] using same
      cases rawEq
      rfl

/-- Complete native binary32 values survive their canonical word encoding. -/
theorem bits32_roundtrip (x : Float32) : Float32.ofBits x.toBits = x := by
  rcases x with ⟨⟨bits, valid⟩⟩
  change Float32.ofModel (Float32.Model.ofBits bits) = Float32.ofModel ⟨bits, valid⟩
  apply congrArg Float32.ofModel
  have same : (Float32.Model.ofBits bits).toBits = bits := by
    apply UInt32.eq_of_toBitVec_eq
    exact pack_unpack Format.binary32 bits.toBitVec valid
  cases decoded : Float32.Model.ofBits bits with
  | mk raw proof =>
      have rawEq : raw = bits := by simpa only [decoded] using same
      cases rawEq
      rfl

private theorem valid_of_not_nan (F : Format) (bits : BitVec F.numBits)
    (notNan : UnpackedFloat.unpack F bits ≠ .notANumber) : F.Valid bits := by
  constructor
  intro he hm
  have decoded : UnpackedFloat.unpack F bits = .notANumber := by
    simp only [UnpackedFloat.unpack, he, hm, ↓reduceIte]
  exact False.elim (notNan decoded)

/-- A finite decoded CPU word is recovered exactly. This does not constrain
    raw NaN payloads: their nonfinite decode cannot satisfy the premise. -/
theorem finite_bits_inverse {word : UInt64} (finite : (Float.ofBits word).isFinite = true) :
    (Float.ofBits word).toBits = word := by
  have notNan : UnpackedFloat.unpack Format.binary64 word.toBitVec ≠ .notANumber := by
    intro bad
    change (Float.ofModel (Float.Model.pack
      (UnpackedFloat.unpack Format.binary64 word.toBitVec))).isFinite = true at finite
    rw [bad] at finite
    have nonfinite : (Float.ofModel (Float.Model.pack .notANumber)).isFinite = false := by decide
    rw [nonfinite] at finite
    cases finite
  apply UInt64.eq_of_toBitVec_eq
  exact pack_unpack Format.binary64 word.toBitVec (valid_of_not_nan _ _ notNan)

/-- The corresponding exact storage fact for finite native binary32 words. -/
theorem finite_bits32_inverse {word : UInt32} (finite : (Float32.ofBits word).isFinite = true) :
    (Float32.ofBits word).toBits = word := by
  have notNan : UnpackedFloat.unpack Format.binary32 word.toBitVec ≠ .notANumber := by
    intro bad
    change (Float32.ofModel (Float32.Model.pack
      (UnpackedFloat.unpack Format.binary32 word.toBitVec))).isFinite = true at finite
    rw [bad] at finite
    have nonfinite : (Float32.ofModel (Float32.Model.pack .notANumber)).isFinite = false := by decide
    rw [nonfinite] at finite
    cases finite
  apply UInt32.eq_of_toBitVec_eq
  exact pack_unpack Format.binary32 word.toBitVec (valid_of_not_nan _ _ notNan)

private theorem unpack_finite (F : Format) (bits : BitVec F.numBits) :
    (UnpackedFloat.unpack F bits).isFinite =
      decide (unpackExponent (spec := F) bits ≠ -1#F.exponentBits) := by
  by_cases he : unpackExponent (spec := F) bits = -1#F.exponentBits
  · simp only [UnpackedFloat.unpack, he, ↓reduceIte]
    split <;> simp [UnpackedFloat.isFinite]
  · simp only [UnpackedFloat.unpack, he, ↓reduceIte]
    split
    · split <;> simp [UnpackedFloat.isFinite, he]
    · simp [UnpackedFloat.isFinite, he]

private theorem repack_finite (F : Format) (bits : BitVec F.numBits) :
    (UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.unpack F bits))).isFinite =
      (UnpackedFloat.unpack F bits).isFinite := by
  by_cases nan : UnpackedFloat.unpack F bits = .notANumber
  · rw [nan, unpack_finite]
    simp [UnpackedFloat.pack, packedNaN, UnpackedFloat.isFinite]
  · rw [pack_unpack F bits (valid_of_not_nan F bits nan)]

private theorem exponent_mask_eq (F : Format) (bits : BitVec F.numBits) :
    bits &&& ((0#1 ++ (-1#F.exponentBits)) ++ 0#F.mantissaBitsWithoutImplicit) =
      ((0#1 ++ (-1#F.exponentBits)) ++ 0#F.mantissaBitsWithoutImplicit) ↔
      unpackExponent (spec := F) bits = -1#F.exponentBits := by
  have masked : bits &&& ((0#1 ++ (-1#F.exponentBits)) ++ 0#F.mantissaBitsWithoutImplicit) =
      (0#1 ++ unpackExponent (spec := F) bits) ++ 0#F.mantissaBitsWithoutImplicit := by
    calc
      _ = packComponents F (Sign.ofBitVec (unpackSign (spec := F) bits))
          (unpackExponent (spec := F) bits) (unpackMantissa (spec := F) bits) &&&
          ((0#1 ++ (-1#F.exponentBits)) ++ 0#F.mantissaBitsWithoutImplicit) :=
        congrArg (fun word => word &&&
          ((0#1 ++ (-1#F.exponentBits)) ++ 0#F.mantissaBitsWithoutImplicit))
          (components_roundtrip F bits).symm
      _ = _ := by simp only [packComponents, BitVec.and_append, BitVec.and_zero,
        BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
  rw [masked, BitVec.append_left_inj, BitVec.append_right_inj]

/-- Native binary64 finiteness is exactly the integer exponent-mask guard,
    including all raw NaN payloads and both signed infinities. -/
theorem finite_word_mask (word : UInt64) :
    (Float.ofBits word).isFinite = ((word &&& 0x7ff0000000000000) != 0x7ff0000000000000) := by
  have fields : (word &&& 0x7ff0000000000000) = 0x7ff0000000000000 ↔
      unpackExponent (spec := Format.binary64) word.toBitVec = -1#11 := by
    rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and]
    have mask : (0x7ff0000000000000 : UInt64).toBitVec = (0#1 ++ (-1#11)) ++ 0#52 := by decide
    rw [mask]
    exact exponent_mask_eq Format.binary64 word.toBitVec
  change (UnpackedFloat.unpack Format.binary64
    (UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 word.toBitVec))).isFinite = _
  rw [repack_finite, unpack_finite]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, bne_iff_ne]
  exact not_congr fields.symm

/-- The corresponding integer exponent mask for native binary32 storage. -/
theorem finite_word32_mask (word : UInt32) :
    (Float32.ofBits word).isFinite = ((word &&& 0x7f800000) != 0x7f800000) := by
  have fields : (word &&& 0x7f800000) = 0x7f800000 ↔
      unpackExponent (spec := Format.binary32) word.toBitVec = -1#8 := by
    rw [← UInt32.toBitVec_inj, UInt32.toBitVec_and]
    have mask : (0x7f800000 : UInt32).toBitVec = (0#1 ++ (-1#8)) ++ 0#23 := by decide
    rw [mask]
    exact exponent_mask_eq Format.binary32 word.toBitVec
  change (UnpackedFloat.unpack Format.binary32
    (UnpackedFloat.pack Format.binary32 (UnpackedFloat.unpack Format.binary32 word.toBitVec))).isFinite = _
  rw [repack_finite, unpack_finite]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, bne_iff_ne]
  exact not_congr fields.symm

private theorem unpack_sign_components (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents F s e m) = s.toBitVec := by
  ext i hi
  have index : i = 0 := by omega
  subst i
  have top : ¬ F.mantissaBitsWithoutImplicit + F.exponentBits <
      F.mantissaBitsWithoutImplicit := by omega
  simp (disch := omega) [unpackSign, packComponents, BitVec.getLsbD_append,
    BitVec.getElem_append, Nat.add_sub_cancel_left, BitVec.getLsbD_eq_getElem, top]

private theorem sign_unbits (s : Sign) : Sign.ofBitVec s.toBitVec = s := by cases s <;> rfl

private theorem unpack_components_neg (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    UnpackedFloat.unpack F (packComponents F (-s) e m) =
      UnpackedFloat.neg (UnpackedFloat.unpack F (packComponents F s e m)) := by
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents,
    unpackExponent_packComponents, unpack_sign_components, sign_unbits]
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

private theorem sign_xor (s : Sign) : s.toBitVec ^^^ 1#1 = (-s).toBitVec := by cases s <;> rfl

private theorem unpack_sign_flip (F : Format) (bits : BitVec F.numBits) :
    UnpackedFloat.unpack F (bits ^^^ ((1#1 ++ 0#F.exponentBits) ++ 0#F.mantissaBitsWithoutImplicit)) =
      UnpackedFloat.neg (UnpackedFloat.unpack F bits) := by
  have flipped : bits ^^^ ((1#1 ++ 0#F.exponentBits) ++ 0#F.mantissaBitsWithoutImplicit) =
      packComponents F (-Sign.ofBitVec (unpackSign (spec := F) bits))
        (unpackExponent (spec := F) bits) (unpackMantissa (spec := F) bits) := by
    calc
      _ = packComponents F (Sign.ofBitVec (unpackSign (spec := F) bits))
          (unpackExponent (spec := F) bits) (unpackMantissa (spec := F) bits) ^^^
          ((1#1 ++ 0#F.exponentBits) ++ 0#F.mantissaBitsWithoutImplicit) :=
        congrArg (fun word => word ^^^
          ((1#1 ++ 0#F.exponentBits) ++ 0#F.mantissaBitsWithoutImplicit))
          (components_roundtrip F bits).symm
      _ = _ := by simp only [packComponents, BitVec.xor_append, BitVec.xor_zero, sign_xor]
  rw [flipped, unpack_components_neg, components_roundtrip]

/-- Flipping the stored binary64 sign bit is native negation as a decoded
    value. Arbitrary NaN payloads are allowed on both sides. -/
theorem neg_word64 (word : UInt64) :
    Float.ofBits (word ^^^ 0x8000000000000000) = Float.neg (Float.ofBits word) := by
  have decoded : UnpackedFloat.unpack Format.binary64 (word ^^^ 0x8000000000000000).toBitVec =
      UnpackedFloat.neg (UnpackedFloat.unpack Format.binary64 word.toBitVec) := by
    rw [UInt64.toBitVec_xor]
    have mask : (0x8000000000000000 : UInt64).toBitVec = (1#1 ++ 0#11) ++ 0#52 := by decide
    rw [mask]
    exact unpack_sign_flip Format.binary64 word.toBitVec
  change Float.ofModel (Float.Model.pack
      (UnpackedFloat.unpack Format.binary64 (word ^^^ 0x8000000000000000).toBitVec)) =
    Float.ofModel (Float.Model.pack (UnpackedFloat.neg (UnpackedFloat.unpack Format.binary64
      (UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 word.toBitVec)))))
  by_cases nan : UnpackedFloat.unpack Format.binary64 word.toBitVec = .notANumber
  · rw [decoded, nan]
    rfl
  · rw [decoded, pack_unpack Format.binary64 word.toBitVec (valid_of_not_nan _ _ nan)]

/-- The corresponding native binary32 sign-bit transport. -/
theorem neg_word32 (word : UInt32) :
    Float32.ofBits (word ^^^ 0x80000000) = Float32.neg (Float32.ofBits word) := by
  have decoded : UnpackedFloat.unpack Format.binary32 (word ^^^ 0x80000000).toBitVec =
      UnpackedFloat.neg (UnpackedFloat.unpack Format.binary32 word.toBitVec) := by
    rw [UInt32.toBitVec_xor]
    have mask : (0x80000000 : UInt32).toBitVec = (1#1 ++ 0#8) ++ 0#23 := by decide
    rw [mask]
    exact unpack_sign_flip Format.binary32 word.toBitVec
  change Float32.ofModel (Float32.Model.pack
      (UnpackedFloat.unpack Format.binary32 (word ^^^ 0x80000000).toBitVec)) =
    Float32.ofModel (Float32.Model.pack (UnpackedFloat.neg (UnpackedFloat.unpack Format.binary32
      (UnpackedFloat.pack Format.binary32 (UnpackedFloat.unpack Format.binary32 word.toBitVec)))))
  by_cases nan : UnpackedFloat.unpack Format.binary32 word.toBitVec = .notANumber
  · rw [decoded, nan]
    rfl
  · rw [decoded, pack_unpack Format.binary32 word.toBitVec (valid_of_not_nan _ _ nan)]

theorem neg_bits64 (word : BitVec 64) :
    Float.ofBits (UInt64.ofBitVec (word ^^^ 0x8000000000000000)) =
      -(Float.ofBits (UInt64.ofBitVec word)) := by
  have stored : UInt64.ofBitVec (word ^^^ 0x8000000000000000) =
      UInt64.ofBitVec word ^^^ 0x8000000000000000 := by
    apply UInt64.eq_of_toBitVec_eq
    rfl
  rw [stored]
  exact neg_word64 (UInt64.ofBitVec word)

theorem neg_bits32 (word : BitVec 32) :
    Float32.ofBits (UInt32.ofBitVec (word ^^^ 0x80000000)) =
      -(Float32.ofBits (UInt32.ofBitVec word)) := by
  have stored : UInt32.ofBitVec (word ^^^ 0x80000000) = UInt32.ofBitVec word ^^^ 0x80000000 := by
    apply UInt32.eq_of_toBitVec_eq
    rfl
  rw [stored]
  exact neg_word32 (UInt32.ofBitVec word)

/-- Every non-NaN CPU word, including both infinities, is recovered exactly. -/
theorem bits_ofBits_notNaN {word : UInt64} (notNaN : (Float.ofBits word).isNaN = false) :
    (Float.ofBits word).toBits = word := by
  have decoded : UnpackedFloat.unpack Format.binary64 word.toBitVec ≠ .notANumber := by
    intro bad
    change (Float.ofModel (Float.Model.pack
      (UnpackedFloat.unpack Format.binary64 word.toBitVec))).isNaN = false at notNaN
    rw [bad] at notNaN
    change true = false at notNaN
    cases notNaN
  apply UInt64.eq_of_toBitVec_eq
  exact pack_unpack Format.binary64 word.toBitVec (valid_of_not_nan _ _ decoded)

/-- The same complete-word transport for native binary32 values. -/
theorem bits32_ofBits_notNaN {word : UInt32} (notNaN : (Float32.ofBits word).isNaN = false) :
    (Float32.ofBits word).toBits = word := by
  have decoded : UnpackedFloat.unpack Format.binary32 word.toBitVec ≠ .notANumber := by
    intro bad
    change (Float32.ofModel (Float32.Model.pack
      (UnpackedFloat.unpack Format.binary32 word.toBitVec))).isNaN = false at notNaN
    rw [bad] at notNaN
    change true = false at notNaN
    cases notNaN
  apply UInt32.eq_of_toBitVec_eq
  exact pack_unpack Format.binary32 word.toBitVec (valid_of_not_nan _ _ decoded)

end RootNativeFloat
