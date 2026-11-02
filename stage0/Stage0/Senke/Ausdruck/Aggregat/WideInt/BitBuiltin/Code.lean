/- C13 bit builtins composed from the existing complete-value limb kernels. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Place
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Materialize an integer with the destination interval's complete representation. -/
def intConstL (lo hi n : Int) (d : Nat) : Option (List II × Nat) :=
  some (constWords (integerEncoding (integerWords lo hi) n) d)

theorem intConstL_top {lo hi n : Int} {d top : Nat} {c : List II}
    (h : intConstL lo hi n d = some (c, top)) : d < top := by
  obtain ⟨rfl, rfl⟩ := Option.some.inj h
  have size := constWords_span (integerEncoding (integerWords lo hi) n) d
  have positive : 0 < integerWords lo hi := valueWords_pos (.int lo hi)
  rw [integerEncoding_length] at size
  omega

namespace BitBuiltin
abbrev Emitter := Nat → Option (List II × Nat)

/-- Change the complete representation after a proved value-preserving composition.
    The explicit result slot also makes the top bound independent of operand code. -/
def cast (lo hi lo' hi' : Int) (f : Emitter) : Emitter := fun d =>
  (resizeIntegerL lo hi lo' hi' d (f d)).map fun p => (p.1, max p.2 (d + 1))

def constant (hi n : Int) : Emitter := intConstL 0 hi n

def add (ha hb hr : Int) (fa fb : Emitter) : Emitter :=
  cast (0 + 0) (ha + hb) 0 hr (fun d => wideAddL 0 ha 0 hb (0 + 0) (ha + hb) d fa fb)

def sub (ha hb hr : Int) (fa fb : Emitter) : Emitter :=
  cast (0 - hb) (ha - 0) 0 hr (fun d => wideSubL 0 ha 0 hb (0 - hb) (ha - 0) d fa fb)

def shl (hi : Int) (s : Nat) (fa fb : Emitter) : Emitter := fun d =>
  wideShlL 0 hi 0 (s : Int) 0 (hi * 2 ^ s) d fa fb

def shr (hi : Int) (s : Nat) (fa fb : Emitter) : Emitter := fun d =>
  wideShrL 0 hi 0 (s : Int) 0 hi d fa fb

/-- Put the mask first: the existing and theorem then supplies its tight bound. -/
def mask (hi : Int) (bits : Nat) (fa : Emitter) : Emitter := fun d =>
  let upper := (2 : Int) ^ bits - 1
  wideBitL 8 0 upper 0 hi 0 upper d (constant upper upper) fa

def eq (ha hb : Int) (fa fb : Emitter) : Emitter := fun d => wideEqL 0 ha 0 hb d fa fb

def lt (ha hb : Int) (fa fb : Emitter) : Emitter := fun d => wideLtL 0 ha 0 hb d fa fb

def choose (fc fa fb : Emitter) : Emitter := fun d =>
  (wennL d (fc d) (fa d) (fb d)).map fun p => (p.1, max p.2 (d + 1))

/-- A bounded binary fold. Each recursive operand is shifted using the wide
    kernel, including bits crossing limbs. The folds are unrolled; repeated
    pure operand emission can produce quadratic code in W. Branch displacements
    retain wennL's checked instruction budget. No host scan instruction is emitted. -/
def population (hi : Int) : Nat → Emitter → Emitter
  | 0, _ => constant 0 0
  | fuel + 1, fa => add 1 (fuel : Int) (fuel + 1 : Nat)
      (mask hi 1 fa) (population hi fuel (shr hi 1 fa (constant 1 1)))

def trailing (hi : Int) : Nat → Emitter → Emitter
  | 0, _ => constant 0 0
  | fuel + 1, fa =>
      let zero := constant (fuel + 1 : Nat) 0
      choose (eq hi 0 fa (constant 0 0)) zero
        (choose (eq 1 1 (mask hi 1 fa) (constant 1 1)) zero
          (add 1 (fuel : Int) (fuel + 1 : Nat) (constant 1 1)
            (trailing hi fuel (shr hi 1 fa (constant 1 1)))))

/-- Fuel bounds the bit length; comparison with two makes the zero case total
    internally. The public scan constructors still exclude zero by their type. -/
def logarithm (hi : Int) : Nat → Emitter → Emitter
  | 0, _ => constant 0 0
  | fuel + 1, fa => choose (lt hi 2 fa (constant 2 2)) (constant (fuel + 1 : Nat) 0)
      (add 1 (fuel : Int) (fuel + 1 : Nat) (constant 1 1)
        (logarithm hi fuel (shr hi 1 fa (constant 1 1))))

/-- W-s can equal W at s=0. Internal shifts therefore use a width larger
    than W; the result is masked to exactly W bits, including a partial limb. -/
def rotate (right : Bool) (w : Nat) (fa fb : Emitter) : Emitter :=
  let W := w + 1
  let u := (2 : Int) ^ W - 1
  let complement := sub (W : Int) (w : Int) (W : Int) (constant (W : Int) (W : Int)) fb
  let leftAmount := if right then complement else cast 0 (w : Int) 0 (W : Int) fb
  let rightAmount := if right then cast 0 (w : Int) 0 (W : Int) fb else complement
  add u u u (mask (u * 2 ^ W) W (shl u W fa leftAmount)) (shr u W fa rightAmount)

/-- Byte packets are read with wide shifts and masks, then assembled by Horner
    steps. There is one implementation for all three named byte-swap widths. -/
def reverseBytes (hi : Int) : Nat → Emitter → Emitter
  | 0, _ => constant 0 0
  | bytes + 1, fa =>
      let rest := reverseBytes hi bytes (shr hi 8 fa (constant 8 8))
      add (255 * 2 ^ (8 * bytes)) ((256 : Int) ^ bytes - 1) ((256 : Int) ^ (bytes + 1) - 1)
        (shl 255 (8 * bytes) (mask hi 8 fa) (constant (8 * bytes : Nat) (8 * bytes : Nat))) rest

/-- Result representation is always explicit, even when an internal scan uses
    an extra value (ctz's total auxiliary can return W for a partial input). -/
def unary {τ1 τ : Ty} (op : IntBuiltin [τ1] τ) (fa : Emitter) : Emitter :=
  match op with
  | .clz w =>
      let u := (2 : Int) ^ (w + 1) - 1
      sub (w : Int) (w : Int) (w : Int) (constant (w : Int) (w : Int))
        (logarithm u w (cast 1 u 0 u fa))
  | .log2Floor w =>
      let u := (2 : Int) ^ (w + 1) - 1
      logarithm u w (cast 1 u 0 u fa)
  | .ctz w =>
      let u := (2 : Int) ^ (w + 1) - 1
      cast 0 (w + 1 : Nat) 0 (w : Int) (trailing u (w + 1) (cast 1 u 0 u fa))
  | .popcount w => population ((2 : Int) ^ (w + 1) - 1) (w + 1) fa
  | .bswap16 => reverseBytes ((2 : Int) ^ 16 - 1) 2 fa
  | .bswap32 => reverseBytes ((2 : Int) ^ 32 - 1) 4 fa
  | .bswap64 => reverseBytes ((2 : Int) ^ 64 - 1) 8 fa

theorem cast_top {lo hi lo' hi' : Int} {f : Emitter} {d top : Nat} {c : List II}
    (h : cast lo hi lo' hi' f d = some (c, top)) : d < top := by
  simp only [cast, Option.map_eq_some_iff] at h
  obtain ⟨p, _, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  omega

theorem choose_top {fc fa fb : Emitter} {d top : Nat} {c : List II}
    (h : choose fc fa fb d = some (c, top)) : d < top := by
  simp only [choose, Option.map_eq_some_iff] at h
  obtain ⟨p, _, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  omega

theorem unary_top {τ1 τ : Ty} (op : IntBuiltin [τ1] τ) {fa : Emitter}
    {d top : Nat} {c : List II} (h : unary op fa d = some (c, top)) : d < top := by
  cases op with
  | clz w => exact cast_top h
  | ctz w => exact cast_top h
  | log2Floor w =>
    cases w with
    | zero => exact intConstL_top h
    | succ w => exact choose_top h
  | popcount w => exact cast_top h
  | bswap16 => exact cast_top h
  | bswap32 => exact cast_top h
  | bswap64 => exact cast_top h

end BitBuiltin
end Gabbro.Stage0.Senke
