/- Binary64 arithmetic candidates and the complete rounded-result range guard. -/
module
public import Stage0.Senke.Gleit.Normal.Sub
public import Stage0.Senke.Ausdruck.Gleit.Slots.Test
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- A computed result must remain finite even if the declared bounds include
    infinity. The range decision is made after canonical IEEE rounding. -/
def softFloatReject (lo hi : Int × Int) (x : GFloat) : Bool :=
  if x.bexp = 2047 then true else floatRangeReject lo hi x

private theorem finiteOfExponent (x : GFloat) (h : x.bexp ≠ 2047) : gleitEndlich x = true := by
  by_cases zero : x.bexp = 0 <;> by_cases frac : x.frac = 0 <;>
    simp [gleitEndlich, klasse, show f64.bexpMax = 2047 from rfl, h, zero, frac]

/-- The complete emitted rejection predicate is exactly the source failure,
    including overflow, unordered endpoints and reversed intervals. -/
theorem softFloatReject_none {lo hi : Int × Int} {x : GFloat} (hw : wf f64 x) :
    gleitPasst lo hi x = none ↔ softFloatReject lo hi x = true := by
  by_cases maximum : x.bexp = 2047
  · have nonfinite : gleitEndlich x = false := by
      by_cases frac : x.frac = 0 <;>
        simp [gleitEndlich, klasse, show f64.bexpMax = 2047 from rfl, maximum, frac]
    have refused : gleitPasst lo hi x = none := by simp [gleitPasst, nonfinite]
    simp only [softFloatReject, if_pos maximum, refused, true_iff]
  · simpa only [softFloatReject, if_neg maximum] using
      floatRangeReject_none hw (finiteOfExponent x maximum)

/-- Reject nonfinite results before executing the ordinary range template. -/
def softFloatRangeL (d : Nat) (lo hi : Int × Int)
    (producer : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  routineChooseL d
    (fun j => wordK 14 j (unpackBexpL j producer) 2047)
    (fun j => some ([ci 1 j 1 0], j + 1))
    (fun j => canonicalFloatRangeL j lo hi producer)

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Both guard branches consume the same generic result producer, including
    its reserved prefix and its agreement outside the temporary frame. -/
theorem softFloatRangeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {producer : Nat → Option (List II × Nat)} {reserved : Nat}
    (lo hi : Int × Int) (x : GFloat) (hw : wf f64 x)
    (hp : WordCode (L := L) (reserved := reserved) ρ W producer
      (BitVec.ofNat 64 (zuBits f64 x))) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => softFloatRangeL d lo hi producer) (Runner.IR.bool (softFloatReject lo hi x)) := by
  have field := unpackBexpL_ok hp
  rw [(routineUnpack_canonical x hw).2.1] at field
  have condition := WordCode.bin field (WordCode.const 2047 (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have equality : (BitVec.ofNat 64 x.bexp == BitVec.ofInt 64 2047) =
      decide (x.bexp = 2047) := by
    apply Bool.eq_iff_iff.mpr
    have bound : x.bexp < 2 ^ 64 := by have := hw.1; change x.bexp ≤ 2047 at this; omega
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    simp
  rw [equality] at condition
  have ordinary (flag : decide (x.bexp = 2047) = false) :
      WordCode (L := L) (reserved := reserved) ρ W
        (fun d => canonicalFloatRangeL d lo hi producer) (Runner.IR.bool (floatRangeReject lo hi x)) := by
    have finite := finiteOfExponent x (by simpa only [decide_eq_false_iff_not] using flag)
    intro fp K d code top hc ht m pc pre
    exact canonicalFloatRangeL_ok x hw finite producer
      (fun j c t he htop m pc pre => (hp he htop m pc pre).mono (fun w eq => ⟨hw, eq⟩)) hc ht pre
  have chosen := routineChooseL_ok condition
    (fun _ => WordCode.const 1 (by decide)) ordinary
  by_cases maximum : x.bexp = 2047 <;>
    simpa [softFloatRangeL, softFloatReject, maximum, Runner.IR.bool] using chosen

/-- Add/sub share one kernel; multiply selects the wide-product kernel.
    Division has no emitter and is refused before this selection is used. -/
def softFloatKernel : GleitOp → SoftFloatKernel
  | .mul => .mul
  | .add | .sub | .div => .add

/-- One rounded-result guard and continuation template serves every checked
    arithmetic kernel. Subtraction keeps its single sign-bit xor adapter. -/
def floatArithmeticBlockL (op : GleitOp) (d : Nat) (lo hi : Int × Int)
    (left right : Nat → Option (List II × Nat))
    (rest : Unit → Option (List II × Nat)) : Option (List II × Nat) :=
  if op = .div then none else do
    let producer := fun j => softFloatWordsL (softFloatKernel op) j left
      (fun k => softAddOperandL (decide (op = .sub)) k right)
    let cc ← softFloatRangeL d lo hi producer
    let ce ← producer d
    let cr ← rest ()
    pure (floatNarrowC d cc.1 (stopC 107 d) ce.1 cr.1,
      max cc.2 (max (d + 8) (max ce.2 cr.2)))

/-- Successful operation selection uses exactly the shared code template. -/
theorem floatArithmeticBlockL_supported (op : GleitOp) (supported : op ≠ .div)
    (d : Nat) (lo hi : Int × Int) (left right : Nat → Option (List II × Nat))
    (rest : Unit → Option (List II × Nat)) :
    floatArithmeticBlockL op d lo hi left right rest = (do
      let cc ← softFloatRangeL d lo hi
        (fun j => softFloatWordsL (softFloatKernel op) j left
          (fun k => softAddOperandL (decide (op = .sub)) k right))
      let ce ← softFloatWordsL (softFloatKernel op) d left
        (fun k => softAddOperandL (decide (op = .sub)) k right)
      let cr ← rest ()
      pure (floatNarrowC d cc.1 (stopC 107 d) ce.1 cr.1,
        max cc.2 (max (d + 8) (max ce.2 cr.2)))) := by
  simp only [floatArithmeticBlockL, if_neg supported]

#print axioms floatArithmeticBlockL_supported
#print axioms softFloatReject_none
#print axioms softFloatRangeL_ok
end Gabbro.Stage0.Senke
