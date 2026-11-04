/- Proof adapters for the toolchain's native float word representation. -/
module
public import Init.Data.Float
@[expose] public section

namespace Gabbro.Grammatik.NativeFloat
open Float.Model Float.Model.UnpackedFloat

private theorem sign_roundtrip (b : BitVec 1) : Sign.toBitVec (Sign.ofBitVec b) = b := by
  rcases b with ⟨⟨n, hn⟩⟩
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl <;> rfl

private theorem components_roundtrip (F : Format) (b : BitVec F.numBits) :
    packComponents F (Sign.ofBitVec (unpackSign b)) (unpackExponent b) (unpackMantissa b) = b := by
  unfold packComponents
  rw [sign_roundtrip]
  ext i hi
  simp only [unpackSign, unpackExponent, unpackMantissa, BitVec.getElem_append,
    BitVec.getElem_extractLsb', Nat.zero_add]
  split
  · exact (BitVec.getLsbD_eq_getElem b i hi).symm
  · rename_i hm
    split
    · have e : F.mantissaBitsWithoutImplicit + (i - F.mantissaBitsWithoutImplicit) = i := by omega
      simpa only [e] using (BitVec.getLsbD_eq_getElem b i hi).symm
    · have e : F.mantissaBitsWithoutImplicit + F.exponentBits +
          (i - F.mantissaBitsWithoutImplicit - F.exponentBits) = i := by omega
      simpa only [e, Nat.add_assoc, Nat.sub_sub] using (BitVec.getLsbD_eq_getElem b i hi).symm

/-- The toolchain pack/unpack boundary is an inverse on its own valid words.
    This proves storage transport only; it defines no arithmetic or rounding. -/
theorem pack_unpack (F : Format) (b : BitVec F.numBits) (valid : F.Valid b) :
    pack F (unpack F b) = b := by
  let e := unpackExponent b
  let m := unpackMantissa b
  let s := Sign.ofBitVec (unpackSign b)
  have reassemble := components_roundtrip F b
  change packComponents F s e m = b at reassemble
  have eb : e.toNat < 2 ^ F.exponentBits := e.isLt
  have mb : m.toNat < 2 ^ F.mantissaBitsWithoutImplicit := m.isLt
  have expRoom : 4 ≤ 2 ^ F.exponentBits :=
    Nat.pow_le_pow_right (by decide : 0 < 2) F.he
  by_cases heMax : e = -1#_
  · by_cases hm : m = 0#_
    · simpa only [unpack, e, m, s, heMax, hm, ↓reduceIte, pack, packedInfinity] using reassemble
    · have canonical : b = packedNaN F := valid.eq_packedNaN heMax hm
      simpa only [unpack, e, m, s, heMax, hm, ↓reduceIte, pack] using canonical.symm
  · have eNotMax : e.toNat ≠ 2 ^ F.exponentBits - 1 := by
      intro h
      apply heMax
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] using h
    by_cases heZero : e = 0#_
    · by_cases hm : m = 0#_
      · simpa only [unpack, e, m, s, heMax, heZero, hm, ↓reduceIte, pack, packedZero] using reassemble
      · have positive : m.toNat ≠ 0 := by
          intro h
          apply hm
          apply BitVec.eq_of_toNat_eq
          simpa using h
        have smallLog : m.toNat.log2 < F.mantissaBitsWithoutImplicit := (Nat.log2_lt positive).mpr mb
        have exponent : ((0 : Int) - (F.exponentBias + F.mantissaBitsWithoutImplicit) + 1 +
            F.exponentBias + F.mantissaBitsWithoutImplicit).toNat = 1 := by omega
        simpa only [unpack, e, m, s, heMax, heZero, hm, ↓reduceIte, pack,
          BitVec.toNat_zero, exponent, show ¬ 2 ^ F.exponentBits ≤ 1 + 1 by omega,
          show m.toNat.log2 + 1 ≠ F.mantissaBits by unfold Format.mantissaBits; omega,
          BitVec.ofNat_toNat, BitVec.setWidth_eq] using reassemble
    · have ep : 0 < e.toNat := by
        by_contra h
        apply heZero
        apply BitVec.eq_of_toNat_eq
        simpa using (show e.toNat = 0 by omega)
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
      simpa only [unpack, e, m, s, heMax, heZero, ↓reduceIte, pack, exponent,
        show ¬ 2 ^ F.exponentBits ≤ e.toNat + 1 by omega,
        log, Format.mantissaBits, ↓reduceIte, mantissa,
        BitVec.ofNat_toNat, BitVec.setWidth_eq] using reassemble

/-- Complete native binary64 values survive their canonical word encoding. -/
theorem bits_roundtrip (x : Float) : Float.ofBits x.toBits = x := by
  rcases x with ⟨⟨bits, valid⟩⟩
  change Float.ofModel (Float.Model.ofBits bits) = Float.ofModel ⟨bits, valid⟩
  apply congrArg Float.ofModel
  apply Float.Model.ext
  apply UInt64.eq_of_toBitVec_eq
  exact pack_unpack Format.binary64 bits.toBitVec valid

/-- Complete native binary32 values survive their canonical word encoding. -/
theorem bits32_roundtrip (x : Float32) : Float32.ofBits x.toBits = x := by
  rcases x with ⟨⟨bits, valid⟩⟩
  change Float32.ofModel (Float32.Model.ofBits bits) = Float32.ofModel ⟨bits, valid⟩
  apply congrArg Float32.ofModel
  apply Float32.Model.ext
  apply UInt32.eq_of_toBitVec_eq
  exact pack_unpack Format.binary32 bits.toBitVec valid

end Gabbro.Grammatik.NativeFloat
