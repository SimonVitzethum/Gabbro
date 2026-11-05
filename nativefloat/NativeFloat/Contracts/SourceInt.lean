module

public import Init.Data.SInt.Float
public import Init.Data.Nat.Bitwise

public section

namespace RootNativeFloat.Contracts

/-- Source integer conversion on both bounded fast paths and the unbounded word sequence.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure SourceInt : Prop where
  ofInt_not_nan : ∀ (z : Int),
      (Float.ofInt z).isNaN = false

  ofInt_signed64_bits : ∀ (z : Int) (lower : -(2 ^ 63) ≤ z) (upper : z < 2 ^ 63),
      Float.ofInt z = (Int64.ofBitVec (BitVec.ofInt 64 z)).toFloat

  ofInt_unsigned64 : ∀ (z : Int) (lower : 0 ≤ z) (upper : z < 2 ^ 64),
      Float.ofInt z = (UInt64.ofNat z.toNat).toFloat

  ofInt_jam56 : ∀ (z : Int) (large : 2 ^ 55 ≤ z.natAbs),
      let n := z.natAbs
      let k := n.log2 - 55
      let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
      let i := min 2047 (k + 1078)
      Float.ofInt z = Float.mul (Int64.ofInt (g : Int)).toFloat
        (Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) + (i - 55) * 2 ^ 52)))

end RootNativeFloat.Contracts
