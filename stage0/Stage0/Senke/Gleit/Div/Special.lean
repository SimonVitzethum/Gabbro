/- Integer-only division dispatch using the shared IEEE classification flags. -/
module
public import Stage0.Senke.Gleit.Div.Model
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Invalid ratios precede the infinity and zero branches. NaN payloads are
    returned unchanged with left-operand priority, exactly as in the kernel. -/
def softDivSpecialWord (a b finite : Runner.W) : Runner.W :=
  let sign := unpackSignWord a ^^^ unpackSignWord b
  if routineNanFlag a then a
  else if routineNanFlag b then b
  else if (routineInfFlag a && routineInfFlag b) ||
      (routineZeroFlag a && routineZeroFlag b) then BitVec.ofNat 64 9218868437227405313
  else if routineInfFlag a || routineZeroFlag b then packWord sign 2047 0
  else if routineInfFlag b || routineZeroFlag a then packWord sign 0 0
  else finite

def softDivSpecialL (d : Nat) (a b finite : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let ea := fun j => unpackBexpL j a
  let eb := fun j => unpackBexpL j b
  let fa := fun j => unpackFracL j a
  let fb := fun j => unpackFracL j b
  let na := fun j => isNanL j ea fa
  let nb := fun j => isNanL j eb fb
  let ia := fun j => isInfL j ea fa
  let ib := fun j => isInfL j eb fb
  let za := fun j => isZeroL j ea fa
  let zb := fun j => isZeroL j eb fb
  let sign := fun j => xorSignL j (fun k => unpackSignL k a) (fun k => unpackSignL k b)
  let invalidA := fun j => wordL 8 j (ia j) (ib (j + 1))
  let invalidB := fun j => wordL 8 j (za j) (zb (j + 1))
  let invalid := fun j => wordL 9 j (invalidA j) (invalidB (j + 1))
  let infinity := fun j => wordL 9 j (ia j) (zb (j + 1))
  let isZero := fun j => wordL 9 j (ib j) (za (j + 1))
  let zero := fun j => some ([ci 1 j 0 0], j + 1)
  let inf := fun j => some ([ci 1 j 2047 0], j + 1)
  let nan := fun j => some (konstWL 4 9218868437227405313 j)
  let finiteOrZero := fun j => routineChooseL j isZero (fun k => packL k sign zero zero) finite
  let infOrFinite := fun j => routineChooseL j infinity (fun k => packL k sign inf zero) finiteOrZero
  let valid := fun j => routineChooseL j invalid nan infOrFinite
  let rightNan := fun j => routineChooseL j nb b valid
  routineChooseL d na a rightNan

private theorem flagAnd (a b : Bool) :
    Runner.IR.bool a &&& Runner.IR.bool b = Runner.IR.bool (a && b) := by
  cases a <;> cases b <;> rfl

private theorem flagOr (a b : Bool) :
    Runner.IR.bool a ||| Runner.IR.bool b = Runner.IR.bool (a || b) := by
  cases a <;> cases b <;> rfl

/-- The finite continuation is required only on the branch that executes it.
    Thus neither a zero divisor nor a nonfinite significand enters division. -/
theorem softDivSpecialL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b finite : Nat → Option (List II × Nat)} {av bv fv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (hf : routineNanFlag av = false → routineNanFlag bv = false →
      (routineInfFlag av || routineZeroFlag bv) = false →
      (routineInfFlag bv || routineZeroFlag av) = false → WordCode (L := L) ρ W finite fv) :
    WordCode (L := L) ρ W (fun d => softDivSpecialL d a b finite)
      (softDivSpecialWord av bv fv) := by
  have ia := routineInfL_ok ha
  have ib := routineInfL_ok hb
  have za := routineZeroL_ok ha
  have zb := routineZeroL_ok hb
  have sign := xorSignL_ok (unpackSignL_ok ha) (unpackSignL_ok hb)
  have invalidA : WordCode (L := L) ρ W _ _ := WordCode.bin ia ib (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have invalidB : WordCode (L := L) ρ W _ _ := WordCode.bin za zb (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  rw [flagAnd] at invalidA invalidB
  have invalid : WordCode (L := L) ρ W _ _ := WordCode.bin invalidA invalidB (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  have infinity : WordCode (L := L) ρ W _ _ := WordCode.bin ia zb (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  have isZero : WordCode (L := L) ρ W _ _ := WordCode.bin ib za (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  rw [flagOr] at invalid infinity isZero
  have zero : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 0 (by decide)
  have inf : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 2047 (by decide)
  exact routineChooseL_ok (routineNanL_ok ha) (fun _ => ha) (fun an =>
    routineChooseL_ok (routineNanL_ok hb) (fun _ => hb) (fun bn =>
      routineChooseL_ok invalid (fun _ => WordCode.konst 9218868437227405313 (by decide)) (fun _ =>
        routineChooseL_ok infinity (fun _ => packL_ok sign inf zero) (fun infinityFalse =>
          routineChooseL_ok isZero (fun _ => packL_ok sign zero zero)
            (fun zeroFalse => hf an bn infinityFalse zeroFalse)))))

/-- Total correspondence of the dispatcher independently of its continuation. -/
theorem softDivSpecialWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (finite : Runner.W) :
    softDivSpecialWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) finite =
      match softDivSpecial a b with
      | some r => BitVec.ofNat 64 (zuBits f64 r)
      | none => finite := by
  obtain ⟨an, ai, az⟩ := routineClass_canonical a ha
  obtain ⟨bn, bi, bz⟩ := routineClass_canonical b hb
  have sign := softMulSignWord_canonical a b ha hb
  have zero : packWord (Runner.IR.bool (a.sign != b.sign)) 0 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨a.sign != b.sign, 0, 0⟩) :=
    packWord_canonical _ ⟨by decide, by decide⟩
  have inf : packWord (Runner.IR.bool (a.sign != b.sign)) 2047 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨a.sign != b.sign, 2047, 0⟩) :=
    packWord_canonical _ ⟨by decide, by decide⟩
  simp only [softDivSpecialWord, an, ai, az, bn, bi, bz, sign, zero, inf]
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
    simp [softDivSpecial, ca, cb, nanQ, zuBits, f64, Format.bexpMax,
      Format.ebits, Format.fracBits, bitlen, bitlenAux]

#print axioms softDivSpecialL_word
#print axioms softDivSpecialWord_model
end Gabbro.Stage0.Senke
