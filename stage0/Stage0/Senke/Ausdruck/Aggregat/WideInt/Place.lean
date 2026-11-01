/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Place.lean
  Subject:   Operand placement and kernel assembly of the multiword integer operators, below every proof.

  A binary operator evaluates its first operand into slot `d` with its own limb count and sign-extends or
  zero-extends it in place to the common width `k`, evaluates its second operand into slot `d + k`
  and extends that, then runs the kernel at `d`. The result is the first limbs of the kernel's output. The
  extension follows the operand's declared interval (`extSigned`): a negative lower bound sign-extends,
  otherwise the limbs are zero-extended, whatever bit the top limb carries. Signed kernels read their operands
  in the signed range of `k` limbs, so a nonnegative interval needs one more limb (`signedWords`).
-/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.KernelCode
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- An operand is extended with its sign exactly when its interval admits negative values. -/
def extSigned (lo : Int) : Bool := decide (lo < 0)

/-- Limbs of an interval in the signed reading of the top limb. -/
def signedWords (lo hi : Int) : Nat := if lo < 0 then integerWords lo hi else integerWords lo hi + 1

/-- Common width of the unsigned-reading operators: both operands and the result fit. -/
def arithWords (l1 h1 l2 h2 lr hr : Int) : Nat :=
  max (max (integerWords l1 h1) (integerWords l2 h2)) (integerWords lr hr)

/-- Common width of the signed-reading operators. -/
def signedArithWords (l1 h1 l2 h2 lr hr : Int) : Nat :=
  max (max (signedWords l1 h1) (signedWords l2 h2)) (integerWords lr hr)

/-- Comparison width: both operands in the signed range of `k - 1` limbs, so their difference fits `k`. -/
def compareWords (l1 h1 l2 h2 : Int) : Nat := max (signedWords l1 h1) (signedWords l2 h2) + 1

/-- Shift width: the operand and the result fit and the largest count is below `64 k`. -/
def shiftWords (l1 h1 h2 lr hr : Int) : Nat :=
  max (max (integerWords l1 h1) (integerWords lr hr)) (h2.toNat / 64 + 1)

/-- The number of doubling stages of the shift kernel: `k ≤ 2 ^ shiftStages k`. -/
def shiftStages (k : Nat) : Nat := k.log2 + 1

/-- Both operands, each extended in place to its width, followed by the kernel at `d`. The first operand is
    lowered at `d`, the second at `d + ka`; the extension scratch reaches slot `d + ka + kb + 3`. -/
def wideBinaryL (ja jb ka kb : Nat) (sa sb : Bool) (d foot : Nat) (kern : List II)
    (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  match fa d, fb (d + ka) with
  | some (ca, ta), some (cb, tb) =>
    some (ca ++ wideExtendC sa ja ka d ++ cb ++ wideExtendC sb jb kb (d + ka) ++ kern,
      max (max (max ta tb) (d + ka + kb + 3)) (d + foot))
  | _, _ => none

/-- One operand extended in place, followed by the kernel at `d`. -/
def wideUnaryL (ja ka : Nat) (sa : Bool) (d foot : Nat) (kern : List II)
    (fa : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  match fa d with
  | some (ca, ta) => some (ca ++ wideExtendC sa ja ka d ++ kern, max (max ta (d + ka + 3)) (d + foot))
  | none => none

theorem wideBinaryL_top {ja jb ka kb : Nat} {sa sb : Bool} {d foot : Nat} {kern : List II}
    {fa fb : Nat → Option (List II × Nat)} {c : List II} {top : Nat}
    (h : wideBinaryL ja jb ka kb sa sb d foot kern fa fb = some (c, top)) : d < top := by
  unfold wideBinaryL at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

theorem wideUnaryL_top {ja ka : Nat} {sa : Bool} {d foot : Nat} {kern : List II}
    {fa : Nat → Option (List II × Nat)} {c : List II} {top : Nat}
    (h : wideUnaryL ja ka sa d foot kern fa = some (c, top)) : d < top := by
  unfold wideUnaryL at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

/-- `x + y` modulo `2 ^ (64 k)`, `k` the common width. -/
def wideAddL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (2 * arithWords l1 h1 l2 h2 lr hr + 7)
    (wideAddC (arithWords l1 h1 l2 h2 lr hr) d 0 0) fa fb

def wideSubL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (2 * arithWords l1 h1 l2 h2 lr hr + 7)
    (wideAddC (arithWords l1 h1 l2 h2 lr hr) d (-1) 1) fa fb

def wideMulL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (3 * arithWords l1 h1 l2 h2 lr hr + 17)
    (wideMulC (arithWords l1 h1 l2 h2 lr hr) d) fa fb

/-- Bitwise operators by their opcode: `8` and, `9` or, `10` xor. -/
def wideBitL (o : Nat) (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (2 * arithWords l1 h1 l2 h2 lr hr)
    (wideBitC o (arithWords l1 h1 l2 h2 lr hr) d) fa fb

/-- Unsigned division: the quotient replaces the dividend. -/
def wideDivL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (4 * arithWords l1 h1 l2 h2 lr hr + 18)
    (wideDivC (arithWords l1 h1 l2 h2 lr hr) d) fa fb

/-- Unsigned remainder: the kernel leaves it in the divisor's slots, which are copied down. -/
def wideRemL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (arithWords l1 h1 l2 h2 lr hr)
    (arithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d (4 * arithWords l1 h1 l2 h2 lr hr + 18)
    (wideDivC (arithWords l1 h1 l2 h2 lr hr) d ++
      copyWords (arithWords l1 h1 l2 h2 lr hr) d (d + arithWords l1 h1 l2 h2 lr hr)) fa fb

/-- Signed division truncating toward zero. -/
def wideSdivL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (signedArithWords l1 h1 l2 h2 lr hr)
    (signedArithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d
    (4 * signedArithWords l1 h1 l2 h2 lr hr + 25) (wideSdivC (signedArithWords l1 h1 l2 h2 lr hr) d) fa fb

def wideSremL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (signedArithWords l1 h1 l2 h2 lr hr)
    (signedArithWords l1 h1 l2 h2 lr hr) (extSigned l1) (extSigned l2) d
    (4 * signedArithWords l1 h1 l2 h2 lr hr + 25)
    (wideSdivC (signedArithWords l1 h1 l2 h2 lr hr) d ++
      copyWords (signedArithWords l1 h1 l2 h2 lr hr) d (d + signedArithWords l1 h1 l2 h2 lr hr)) fa fb

/-- `x < y`: the sign of the `k`-limb difference. -/
def wideLtL (l1 h1 l2 h2 : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (compareWords l1 h1 l2 h2) (compareWords l1 h1 l2 h2)
    (extSigned l1) (extSigned l2) d (2 * compareWords l1 h1 l2 h2 + 7)
    (wideLtC (compareWords l1 h1 l2 h2 - 1) d) fa fb

/-- `x ≤ y` is `¬ (y < x)`: the operands are lowered in the swapped order. -/
def wideLeL (l1 h1 l2 h2 : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l2 h2) (integerWords l1 h1) (compareWords l2 h2 l1 h1) (compareWords l2 h2 l1 h1)
    (extSigned l2) (extSigned l1) d (2 * compareWords l2 h2 l1 h1 + 7)
    (wideLtC (compareWords l2 h2 l1 h1 - 1) d ++ [ci 1 (d + 1 : Nat) 1 0, ci 10 (d : Nat) (d : Nat) (d + 1 : Nat)])
    fb fa

def wideEqL (l1 h1 l2 h2 : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (compareWords l1 h1 l2 h2) (compareWords l1 h1 l2 h2)
    (extSigned l1) (extSigned l2) d (2 * compareWords l1 h1 l2 h2 + 7)
    (wideEqC (compareWords l1 h1 l2 h2 - 1) d) fa fb

/-- Shift left by a runtime count: the count keeps its own limbs, the kernel reads the first. -/
def wideShlL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (shiftWords l1 h1 h2 lr hr) (integerWords l2 h2)
    (extSigned l1) (extSigned l2) d (shiftWords l1 h1 h2 lr hr + 10)
    (wideShlC (shiftWords l1 h1 h2 lr hr) (shiftStages (shiftWords l1 h1 h2 lr hr)) d) fa fb

def wideShrL (l1 h1 l2 h2 lr hr : Int) (d : Nat) (fa fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wideBinaryL (integerWords l1 h1) (integerWords l2 h2) (shiftWords l1 h1 h2 lr hr) (integerWords l2 h2)
    (extSigned l1) (extSigned l2) d (shiftWords l1 h1 h2 lr hr + 10)
    (wideShrC (shiftWords l1 h1 h2 lr hr) (shiftStages (shiftWords l1 h1 h2 lr hr)) d) fa fb

/-- Negation: `0 - x` at the common width. -/
def wideNegL (lo hi lr hr : Int) (d : Nat) (fa : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wideUnaryL (integerWords lo hi) (max (integerWords lo hi) (integerWords lr hr)) (extSigned lo) d
    (2 * max (integerWords lo hi) (integerWords lr hr) + 7)
    (wideNegC (max (integerWords lo hi) (integerWords lr hr)) d) fa

/-- The width at which `eng` tests its input against the narrowed bounds: all three fit the signed range. -/
def engWords (lo hi lo' hi' : Int) : Nat := max (signedWords lo hi) (signedWords lo' hi')

/-- Narrowing of a multiword input: extend, test against `lo' .. hi'` (the flag lands in slot `d + k + 3`),
    and branch over the fallback, which is evaluated into `d` only when the test fails. -/
def wideEngL (lo hi lo' hi' : Int) (d : Nat) (fe fb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  match fe d, fb d with
  | some (ce, te), some (cb, tb) =>
    if 16 * (cb.length + 1) < 2 ^ 31 then
      some (ce ++ wideExtendC (extSigned lo) (integerWords lo hi) (engWords lo hi lo' hi') d ++
          wideOutC (engWords lo hi lo' hi') d lo' hi' ++
          [ci 19 (d + engWords lo hi lo' hi' + 3 : Nat) ((16 * (cb.length + 1) : Nat) : Int) 0] ++ cb,
        max (max te tb) (d + 5 * engWords lo hi lo' hi' + 22))
    else none
  | _, _ => none

theorem wideEngL_top {lo hi lo' hi' : Int} {d : Nat} {fe fb : Nat → Option (List II × Nat)}
    {c : List II} {top : Nat} (h : wideEngL lo hi lo' hi' d fe fb = some (c, top)) : d < top := by
  unfold wideEngL at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · cases h
  · cases h

end Gabbro.Stage0.Senke
