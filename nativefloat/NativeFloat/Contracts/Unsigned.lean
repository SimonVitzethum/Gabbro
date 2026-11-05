module

public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

public section

namespace RootNativeFloat.Contracts

/-- Full-range unsigned conversion through the portable native instruction sequence.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Unsigned : Prop where
  uint64_toFloat32_high : ∀ (word : BitVec 64) (high : word.msb = true),
      let half := (word >>> 1) ||| (word &&& 1)
      (UInt64.ofBitVec word).toFloat32 =
        Float32.add (Int64.ofBitVec half).toFloat32 (Int64.ofBitVec half).toFloat32

  uint64_toFloat_high : ∀ (word : BitVec 64) (high : word.msb = true),
      let half := (word >>> 1) ||| (word &&& 1)
      (UInt64.ofBitVec word).toFloat =
        Float.add (Int64.ofBitVec half).toFloat (Int64.ofBitVec half).toFloat

end RootNativeFloat.Contracts
