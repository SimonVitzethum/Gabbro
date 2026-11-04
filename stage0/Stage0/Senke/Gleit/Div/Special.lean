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
  let zero := fun (j : Nat) => some ([ci 1 j 0 0], j + 1)
  let inf := fun (j : Nat) => some ([ci 1 j 2047 0], j + 1)
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
  have ia : WordCode (L := L) ρ W _ _ := routineInfL_ok ha
  have ib : WordCode (L := L) ρ W _ _ := routineInfL_ok hb
  have za : WordCode (L := L) ρ W _ _ := routineZeroL_ok ha
  have zb : WordCode (L := L) ρ W _ _ := routineZeroL_ok hb
  have sign : WordCode (L := L) ρ W _ _ := xorSignL_ok (unpackSignL_ok ha) (unpackSignL_ok hb)
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
  have result : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok (routineNanL_ok ha) (fun _ => ha) (fun an =>
      routineChooseL_ok (routineNanL_ok hb) (fun _ => hb) (fun bn =>
        routineChooseL_ok invalid (fun _ => WordCode.konst 9218868437227405313 (by decide)) (fun _ =>
          routineChooseL_ok infinity (fun _ => packL_ok sign inf zero) (fun infinityFalse =>
            routineChooseL_ok isZero (fun _ => packL_ok sign zero zero)
              (fun zeroFalse => hf an bn infinityFalse zeroFalse)))))
  intro fp K d c top emitted fits m pc pre
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

omit [Kern] in
private theorem divisionNanPack :
    BitVec.ofNat 64 9218868437227405313 =
      BitVec.ofNat 64 (zuBits f64 (nanQ f64)) := by
  have valid : wf f64 (nanQ f64) := by
    change 2047 ≤ 2047 ∧ 1 < 2 ^ 52
    constructor <;> decide
  have packed := packWord_canonical (nanQ f64) valid
  change packWord 0 2047 1 = BitVec.ofNat 64 (zuBits f64 (nanQ f64)) at packed
  calc
    BitVec.ofNat 64 9218868437227405313 = packWord 0 2047 1 := by decide +kernel
    _ = BitVec.ofNat 64 (zuBits f64 (nanQ f64)) := packed

omit [Kern] in
/-- Class priority is independent of how complete operand words are encoded. -/
private theorem divisionClass_model (encode : GFloat → Runner.W) (a b : GFloat)
    (finite : Runner.W) :
    (if decide (klasse f64 a = .nan) then encode a
    else if decide (klasse f64 b = .nan) then encode b
    else if (decide (klasse f64 a = .unendlich) && decide (klasse f64 b = .unendlich)) ||
        (decide (klasse f64 a = .null) && decide (klasse f64 b = .null)) then
      encode (nanQ f64)
    else if decide (klasse f64 a = .unendlich) || decide (klasse f64 b = .null) then
      encode ⟨a.sign != b.sign, 2047, 0⟩
    else if decide (klasse f64 b = .unendlich) || decide (klasse f64 a = .null) then
      encode ⟨a.sign != b.sign, 0, 0⟩
    else finite) =
      match softDivSpecial a b with
      | some r => encode r
      | none => finite := by
  unfold softDivSpecial
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;> rfl

omit [Kern] in
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
    packWord_canonical ⟨a.sign != b.sign, 0, 0⟩ (by
      change 0 ≤ 2047 ∧ 0 < 2 ^ 52
      constructor <;> decide)
  have inf : packWord (Runner.IR.bool (a.sign != b.sign)) 2047 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨a.sign != b.sign, 2047, 0⟩) :=
    packWord_canonical ⟨a.sign != b.sign, 2047, 0⟩ (by
      change 2047 ≤ 2047 ∧ 0 < 2 ^ 52
      constructor <;> decide)
  refine Eq.trans ?_ (divisionClass_model (fun r => BitVec.ofNat 64 (zuBits f64 r)) a b finite)
  unfold softDivSpecialWord
  rw [an, bn, ai, az, bi, bz, sign]
  dsimp only
  rw [zero, inf, divisionNanPack]

#print axioms softDivSpecialL_word
#print axioms softDivSpecialWord_model
end Gabbro.Stage0.Senke
