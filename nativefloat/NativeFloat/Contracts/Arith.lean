module

public import NativeFloat.Primitives

public section

namespace RootNativeFloat.Contracts

/-! Correct-rounding contract for the native arithmetic operations.
    Values are scaled to integers: `Float.sval x = value x * 2^1074` and
    `Float32.sval x = value x * 2^149`, read from the bit pattern only, so the
    specification needs no floating model and no rational numbers. -/

/-- Scaled integer value of a binary64 bit pattern (meaningful for finite values). -/
def Float.sval (x : Float) : Int :=
  let w := x.hwToBits
  let e := ((w >>> 52) &&& 0x7ff).toNat
  let f := (w &&& 0xfffffffffffff).toNat
  let mag : Nat := (if e = 0 then f else f + 2 ^ 52) * 2 ^ (max e 1 - 1)
  if w >>> 63 = 1 then -(mag : Int) else mag

/-- Scaled integer value of a binary32 bit pattern (meaningful for finite values). -/
def Float32.sval (x : Float32) : Int :=
  let w := x.hwToBits
  let e := ((w >>> 23) &&& 0xff).toNat
  let f := (w &&& 0x7fffff).toNat
  let mag : Nat := (if e = 0 then f else f + 2 ^ 23) * 2 ^ (max e 1 - 1)
  if w >>> 31 = 1 then -(mag : Int) else mag

/-- Format-independent description of one IEEE binary format over a carrier `α`. -/
structure Format (α : Type) where
  finite : α → Bool
  nan : α → Bool
  sval : α → Int
  /-- Parity bit of the fraction field. -/
  parity : α → Nat
  /-- Sign bit. -/
  sign : α → Nat
  /-- `value * 2^scale` is an integer for every finite value. -/
  scale : Nat
  /-- Round-to-nearest-even overflow threshold, times `2^scale`. -/
  maxScaled : Nat

def Format.binary64 : Format Float where
  finite := Float.hwIsFinite
  nan := Float.hwIsNaN
  sval := Float.sval
  parity := fun x => (x.hwToBits &&& 1).toNat
  sign := fun x => (x.hwToBits >>> 63).toNat
  scale := 1074
  maxScaled := (2 ^ 1024 - 2 ^ 970) * 2 ^ 1074

def Format.binary32 : Format Float32 where
  finite := Float32.hwIsFinite
  nan := Float32.hwIsNaN
  sval := Float32.sval
  parity := fun x => (x.hwToBits &&& 1).toNat
  sign := fun x => (x.hwToBits >>> 31).toNat
  scale := 149
  maxScaled := (2 ^ 128 - 2 ^ 103) * 2 ^ 149

variable {α : Type}

/-- `x` is the finite value nearest to the real number `T / D` (`D > 0`); a tie goes to the
    candidate with an even fraction. Zero signs are not constrained. -/
def Format.RoundsTo (F : Format α) (T : Int) (D : Nat) (x : α) : Prop :=
  F.finite x = true ∧ ∀ y, F.finite y = true →
    (F.sval x * D - T * 2 ^ F.scale).natAbs ≤ (F.sval y * D - T * 2 ^ F.scale).natAbs ∧
    ((F.sval x * D - T * 2 ^ F.scale).natAbs = (F.sval y * D - T * 2 ^ F.scale).natAbs →
      F.sval x ≠ F.sval y → F.parity x = 0)

/-- Round-to-nearest-even of the real number `T / D` (`D > 0`): inside the finite range the
    nearest finite value, beyond the overflow threshold an infinity of the same sign. -/
def Format.Rounded (F : Format α) (T : Int) (D : Nat) (r : α) : Prop :=
  (T.natAbs * 2 ^ F.scale < F.maxScaled * D → F.RoundsTo T D r) ∧
  (F.maxScaled * D ≤ T.natAbs * 2 ^ F.scale →
    F.finite r = false ∧ F.nan r = false ∧ F.sign r = if T < 0 then 1 else 0)

/-- The four basic operations of one format on finite operands. -/
structure Format.Arith (F : Format α) (opAdd opSub opMul opDiv : α → α → α) : Prop where
  add : ∀ a b, F.finite a = true → F.finite b = true →
    F.Rounded (F.sval a + F.sval b) (2 ^ F.scale) (opAdd a b)
  sub : ∀ a b, F.finite a = true → F.finite b = true →
    F.Rounded (F.sval a - F.sval b) (2 ^ F.scale) (opSub a b)
  mul : ∀ a b, F.finite a = true → F.finite b = true →
    F.Rounded (F.sval a * F.sval b) (2 ^ (2 * F.scale)) (opMul a b)
  div : ∀ a b, F.finite a = true → F.finite b = true → F.sval b ≠ 0 →
    F.Rounded (if F.sval b < 0 then -F.sval a else F.sval a) (F.sval b).natAbs (opDiv a b)
  div_by_zero : ∀ a b, F.finite a = true → F.finite b = true → F.sval a ≠ 0 → F.sval b = 0 →
    F.finite (opDiv a b) = false ∧ F.nan (opDiv a b) = false ∧
      F.sign (opDiv a b) = (if F.sign a = F.sign b then 0 else 1)
  zero_div_zero : ∀ a b, F.finite a = true → F.finite b = true → F.sval a = 0 → F.sval b = 0 →
    F.nan (opDiv a b) = true

/-- Correct rounding of `+ - * /` at both widths, as an explicit hardware assumption.
    No implementation and no instance is supplied here. -/
structure Arith : Prop where
  binary64 : Format.binary64.Arith Float.hwAdd Float.hwSub Float.hwMul Float.hwDiv
  binary32 : Format.binary32.Arith Float32.hwAdd Float32.hwSub Float32.hwMul Float32.hwDiv

end RootNativeFloat.Contracts
