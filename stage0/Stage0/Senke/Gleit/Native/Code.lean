/- Native CPU operations over the existing runner's scalar slots. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Both source operands are evaluated in order, then the actual FP opcode reads
    their slots. The temporary ceiling includes both physical reads. -/
def nativeFPWordL (kind : Runner.NativeFPOp) (d : Nat)
    (a b : Option (List II × Nat)) : Option (List II × Nat) :=
  wordL kind.code d a b

def nativeArithmeticOp : GleitOp → Runner.NativeFPOp
  | .add => .add .f64
  | .sub => .sub .f64
  | .mul => .mul .f64
  | .div => .div .f64

/-- Arithmetic executes in the assembly runner, including division by zero and
    overflow. The source range check consumes the resulting native value. -/
def floatWordsL (op : GleitOp) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  nativeFPWordL (nativeArithmeticOp op) d (a d) (b (d + 1))

/-- The second comparison form retains the existing reverse-operand interface. -/
def floatExprL (le : Bool) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  if le then nativeFPWordL (.le .f64) d (b d) (a (d + 1))
  else nativeFPWordL (.lt .f64) d (a d) (b (d + 1))

/-- Constants are compiler inputs; executing their code only materializes bits. -/
def floatConstL (x : GFloat) (d : Nat) : List II × Nat :=
  konstWL 4 x.hwToBits.toNat d

/-- Finiteness is an integer mask test, not an additional floating request. -/
def nativeFloatFiniteL (d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let mask := fun j => some (konstWL 4 0x7ff0000000000000 j)
  wordK 10 d (wordL 14 d (wordL 8 d (e d) (mask (d + 1))) (mask (d + 1))) 1

/-- Reject exactly a failed source `gleitPasst`: finite and both inclusive
    comparisons must hold. Unordered bounds therefore reject, without a key or
    any software implementation of IEEE arithmetic. -/
def floatRangeL (d : Nat) (lo hi : Int × Int)
    (e : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let lower := fun j => nativeFPWordL (.le .f64) j
    (some (floatConstL (bruch lo) j)) (e (j + 1))
  let upper := fun j => nativeFPWordL (.le .f64) j
    (e j) (some (floatConstL (bruch hi) (j + 1)))
  (wordK 10 d (wordL 8 d (nativeFloatFiniteL d e)
    (wordL 8 (d + 1) (lower (d + 1)) (upper (d + 2)))) 1).map
      (fun code => (code.1, max code.2 (d + 8)))

def floatRangeReject (lo hi : Int × Int) (x : GFloat) : Bool :=
  !(gleitEndlich x && (gleitLe (bruch lo) x && gleitLe x (bruch hi)))

end Gabbro.Stage0.Senke
