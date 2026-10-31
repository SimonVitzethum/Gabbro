/- Shared add/sub decomposition for the integer software-float lowering.
   This module proves the specification boundary only. Block.float remains
   refused until the emitted finite path and its resource bounds are proved. -/
import Stage0.Senke.Ausdruck.Gleit.Runden

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma

/-- Subtraction changes only the second operand before the shared adder. -/
def floatAddOperand (subtract : Bool) (F : Format) (b : GBits F) : GBits F :=
  if subtract then neg F b else b

/-- Special-case dispatch before finite alignment. Left NaN wins, including
    its payload and sign; subtraction has already changed the right sign. -/
def floatAddSpecial (F : Format) (a b : GBits F) : Option (GBits F) :=
  if klasse F a = .nan then some a
  else if klasse F b = .nan then some b
  else if klasse F a = .unendlich then
    if klasse F b = .unendlich then
      some (if a.sign == b.sign then a else nanQ F)
    else some a
  else if klasse F b = .unendlich then some b
  else if klasse F a = .null ∧ klasse F b = .null then some ⟨a.sign && b.sign, 0, 0⟩
  else none

/-- Exact equivalence to the canonical adder for every format and bit triple,
    including malformed triples. No IEEE rules are added by the lowering. -/
theorem floatAddSpecial_model (F : Format) (a b : GBits F) :
    add F a b = match floatAddSpecial F a b with
      | some r => r
      | none => match wertExakt F a, wertExakt F b with
        | some u, some v => rundeExakt F (exaktAdd u v)
        | _, _ => nanQ F := by
  generalize ha : klasse F a = ka
  generalize hb : klasse F b = kb
  cases ka <;> cases kb <;> simp [add, floatAddSpecial, wertExakt, ha, hb]

/-- Both source operations use exactly the same special dispatch and finite
    rounding continuation. This includes subtraction of a right-hand NaN. -/
theorem floatAddSub_model (subtract : Bool) (F : Format) (a b : GBits F) :
    (if subtract then sub F a b else add F a b) =
      match floatAddSpecial F a (floatAddOperand subtract F b) with
      | some r => r
      | none => match wertExakt F a, wertExakt F (floatAddOperand subtract F b) with
        | some u, some v => rundeExakt F (exaktAdd u v)
        | _, _ => nanQ F := by
  cases subtract
  · simpa [floatAddOperand] using floatAddSpecial_model F a b
  · simpa [floatAddOperand, sub] using floatAddSpecial_model F a (neg F b)

/-- The finite continuation always receives two exact values. The exceptional
    fallback in the canonical definition cannot be reached after dispatch. -/
theorem floatAddSpecial_none_exact (F : Format) (a b : GBits F)
    (h : floatAddSpecial F a b = none) :
    ∃ u v, wertExakt F a = some u ∧ wertExakt F b = some v := by
  generalize ha : klasse F a = ka
  generalize hb : klasse F b = kb
  cases ka <;> cases kb <;>
    simp_all [floatAddSpecial, wertExakt]

/-- In each alignment branch, one coefficient remains unshifted. This avoids
    forming two large shifted coefficients and is shared by both operations. -/
theorem floatAdd_align (u v : Exakt) :
    exaktAdd u v =
      if u.zweierExp ≤ v.zweierExp then
        ⟨u.zaehler + v.zaehler * (2 ^ (v.zweierExp - u.zweierExp).toNat : Nat), u.zweierExp⟩
      else
        ⟨u.zaehler * (2 ^ (u.zweierExp - v.zweierExp).toNat : Nat) + v.zaehler, v.zweierExp⟩ := by
  unfold exaktAdd
  split <;> simp_all

/-- Joint non-degeneracy: finite alignment with different exponents, an exact
    cancellation, signed zeros, infinity conflict, and NaN priority/payload.
    All are checked by the kernel against the same dispatcher. -/
theorem floatAddSub_model_zeuge :
    let a : GBits f64 := ⟨false, 1023, 0⟩
    let b : GBits f64 := ⟨false, 1022, 0⟩
    floatAddSpecial f64 a b = none ∧
    wertExakt f64 a = some ⟨2^52, -52⟩ ∧
    wertExakt f64 b = some ⟨2^52, -53⟩ ∧
    exaktAdd ⟨2^52, -52⟩ ⟨2^52, -53⟩ = ⟨3 * 2^52, -53⟩ ∧
    sub f64 a a = ⟨false, 0, 0⟩ ∧
    floatAddSpecial f64 ⟨true, 0, 0⟩ ⟨true, 0, 0⟩ = some ⟨true, 0, 0⟩ ∧
    floatAddSpecial f64 ⟨false, 2047, 0⟩ ⟨true, 2047, 0⟩ = some (nanQ f64) ∧
    floatAddSpecial f64 ⟨true, 2047, 7⟩ ⟨false, 2047, 9⟩ = some ⟨true, 2047, 7⟩ ∧
    floatAddOperand true f64 ⟨true, 2047, 9⟩ = ⟨false, 2047, 9⟩ := by
  decide +kernel

#print axioms floatAddSub_model
#print axioms floatAddSpecial_none_exact
#print axioms floatAdd_align
#print axioms floatAddSub_model_zeuge

end Gabbro.Stage0.Senke
