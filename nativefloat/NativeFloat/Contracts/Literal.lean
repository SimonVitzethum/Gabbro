module

public import NativeFloat.Literal

public section

namespace RootNativeFloat.Contracts

/-- Compile-time native literal conversion, including the existing smallest-subnormal word contracts.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Literal : Prop where
  canonLiteral_integer : ∀ (z : Int),
      canonLiteral (z, 1) = Float.hwOfInt z

  canonLiteral_subnormal_one : (canonLiteral (1, 2 ^ 1074)).hwToBits = 1

  canonLiteral_subnormal_two : (canonLiteral (2, 2 ^ 1074)).hwToBits = 2

  canonLiteral_subnormal_negative : (canonLiteral (-1, 2 ^ 1074)).hwToBits = 0x8000000000000001 ∧
        (canonLiteral (1, -(2 ^ 1074))).hwToBits = 0x8000000000000001 ∧
        (canonLiteral (-1, -(2 ^ 1074))).hwToBits = 1

end RootNativeFloat.Contracts
