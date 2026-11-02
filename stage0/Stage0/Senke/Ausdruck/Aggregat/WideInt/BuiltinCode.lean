/- C13 arithmetic code uses complete integer values and exact temporary intervals. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Code
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- The sum is computed at its exact interval, before any comparison or clamp.
    Negative ranges and sums needing an additional limb use the same wide kernels. -/
def saturatingAddL (lo hi : Int) (d : Nat)
    (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let sum := fun q => wideAddL lo hi lo hi (lo + lo) (hi + hi) q fa fb
  let fallback := fun q => wennL q
    (wideLtL (lo + lo) (hi + hi) lo lo q sum (intConstL lo lo lo))
    (intConstL lo hi lo q) (intConstL lo hi hi q)
  wideEngL (lo + lo) (hi + hi) lo hi d sum fallback

/-- Mask every limb, including a partial top limb, to exactly `W = w + 1`
    bits. The mask is a complete value, not a host instruction immediate. -/
def wrapL (w : Nat) (lo hi : Int) (d : Nat)
    (source : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let upper := (2 : Int) ^ (w + 1) - 1
  wideBitL 8 lo hi 0 upper 0 upper d source (intConstL 0 upper upper)

def wrappingAddL (w d : Nat) (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let u := (2 : Int) ^ (w + 1) - 1
  wrapL w (0 + 0) (u + u) d (fun q => wideAddL 0 u 0 u (0 + 0) (u + u) q fa fb)

/-- Add one modulus to the exact signed difference before masking; its value
    is then nonnegative, including unsigned underflow. -/
def wrappingSubL (w d : Nat) (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let modulus := (2 : Int) ^ (w + 1)
  let u := modulus - 1
  wrapL w ((0 - u) + modulus) ((u - 0) + modulus) d (fun q =>
    wideAddL (0 - u) (u - 0) modulus modulus ((0 - u) + modulus) ((u - 0) + modulus) q
      (fun r => wideSubL 0 u 0 u (0 - u) (u - 0) r fa fb)
      (intConstL modulus modulus modulus))

def wrappingMulL (w d : Nat) (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let u := (2 : Int) ^ (w + 1) - 1
  let lo := imin (imin (0 * 0) (0 * u)) (imin (u * 0) (u * u))
  let hi := imax (imax (0 * 0) (0 * u)) (imax (u * 0) (u * u))
  wrapL w lo hi d (fun q => wideMulL 0 u 0 u lo hi q fa fb)

def wrappingShlL (w d : Nat) (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let u := (2 : Int) ^ (w + 1) - 1
  wrapL w 0 (u * 2 ^ w) d (fun q => wideShlL 0 u 0 (w : Int) 0 (u * 2 ^ w) q fa fb)

/-- One dispatch shared by ordinary and snapshot-aware expression lowering. -/
def intBuiltin2L {τ1 τ2 τ : Ty} (op : IntBuiltin [τ1, τ2] τ) (d : Nat)
    (fa fb : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  match op with
  | .addW w => wrappingAddL w d fa fb
  | .subW w => wrappingSubL w d fa fb
  | .mulW w => wrappingMulL w d fa fb
  | .shlW w => wrappingShlL w d fa fb
  | .addS lo hi => saturatingAddL lo hi d fa fb
  | .rotl w => BitBuiltin.rotate false w fa fb d
  | .rotr w => BitBuiltin.rotate true w fa fb d

theorem intBuiltin2L_top {τ1 τ2 τ : Ty} (op : IntBuiltin [τ1, τ2] τ)
    {d top : Nat} {c : List II} {fa fb : Nat → Option (List II × Nat)}
    (h : intBuiltin2L op d fa fb = some (c, top)) : d < top := by
  cases op <;> simp only [intBuiltin2L] at h
  all_goals first
    | contradiction
    | exact wideEngL_top h
    | exact wideBinaryL_top h
    | exact BitBuiltin.cast_top h

end Gabbro.Stage0.Senke
