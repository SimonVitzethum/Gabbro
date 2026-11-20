module

public import NativeFloat.Primitives

public section

namespace RootNativeFloat.Contracts

/-- Full-range unsigned conversion through the portable native instruction sequence.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Unsigned : Prop where
  uint64_toFloat_nonnegative : ∀ (word : BitVec 64) (low : word.msb = false),
      (UInt64.ofBitVec word).hwToFloat = (Int64.ofBitVec word).hwToFloat

  uint64_toFloat32_nonnegative : ∀ (word : BitVec 64) (low : word.msb = false),
      (UInt64.ofBitVec word).hwToFloat32 = (Int64.ofBitVec word).hwToFloat32

  uint64_toFloat32_high : ∀ (word : BitVec 64) (high : word.msb = true),
      let half := (word >>> 1) ||| (word &&& 1)
      (UInt64.ofBitVec word).hwToFloat32 =
        Float32.hwAdd (Int64.ofBitVec half).hwToFloat32 (Int64.ofBitVec half).hwToFloat32

  uint64_toFloat_high : ∀ (word : BitVec 64) (high : word.msb = true),
      let half := (word >>> 1) ||| (word &&& 1)
      (UInt64.ofBitVec word).hwToFloat =
        Float.hwAdd (Int64.ofBitVec half).hwToFloat (Int64.ofBitVec half).hwToFloat

end RootNativeFloat.Contracts
