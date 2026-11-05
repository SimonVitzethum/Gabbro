module

public import Init.Data.Float.Float32
public import Init.Data.UInt.Bitwise

public section

namespace RootNativeFloat.Contracts

/-- Native value/word transport, finite classification and sign-bit operations.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Codec : Prop where
  bits32_roundtrip : ∀ (x : Float32),
      Float32.ofBits x.toBits = x

  bits_roundtrip : ∀ (x : Float),
      Float.ofBits x.toBits = x

  bits_ofBits_notNaN : ∀ {word : UInt64} (notNaN : (Float.ofBits word).isNaN = false),
      (Float.ofBits word).toBits = word

  finite_bits_inverse : ∀ {word : UInt64} (finite : (Float.ofBits word).isFinite = true),
      (Float.ofBits word).toBits = word

  finite_word32_mask : ∀ (word : UInt32),
      (Float32.ofBits word).isFinite = ((word &&& 0x7f800000) != 0x7f800000)

  finite_word_mask : ∀ (word : UInt64),
      (Float.ofBits word).isFinite = ((word &&& 0x7ff0000000000000) != 0x7ff0000000000000)

  neg_bits32 : ∀ (word : BitVec 32),
      Float32.ofBits (UInt32.ofBitVec (word ^^^ 0x80000000)) =
        -(Float32.ofBits (UInt32.ofBitVec word))

  neg_bits64 : ∀ (word : BitVec 64),
      Float.ofBits (UInt64.ofBitVec (word ^^^ 0x8000000000000000)) =
        -(Float.ofBits (UInt64.ofBitVec word))

end RootNativeFloat.Contracts
