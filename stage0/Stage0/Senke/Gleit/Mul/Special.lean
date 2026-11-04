/- Integer-only multiplication dispatch, reusing the shared IEEE field flags. -/
module
public import Stage0.Senke.Gleit.Mul.Model
public import Stage0.Senke.Gleit.Normal.PackModel
public import Stage0.Senke.Gleit.AddMag
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The finite continuation is independent of NaN payload propagation,
    infinity times zero, xor-signed infinity and xor-signed zero. -/
def softMulSpecialWord (a b finite : Runner.W) : Runner.W :=
  let sign := unpackSignWord a ^^^ unpackSignWord b
  if routineNanFlag a then a
  else if routineNanFlag b then b
  else if (routineInfFlag a && routineZeroFlag b) ||
      (routineZeroFlag a && routineInfFlag b) then BitVec.ofNat 64 9218868437227405313
  else if routineInfFlag a || routineInfFlag b then packWord sign 2047 0
  else if routineZeroFlag a || routineZeroFlag b then packWord sign 0 0
  else finite

def softMulSpecialL (d : Nat) (a b finite : Nat → Option (List II × Nat)) :
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
  let invalidA := fun j => wordL 8 j (ia j) (zb (j + 1))
  let invalidB := fun j => wordL 8 j (za j) (ib (j + 1))
  let invalid := fun j => wordL 9 j (invalidA j) (invalidB (j + 1))
  let infinity := fun j => wordL 9 j (ia j) (ib (j + 1))
  let isZero := fun j => wordL 9 j (za j) (zb (j + 1))
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

/-- Every branch executes existing checked integer fragments. No condition
    computes a rounded product or discards the original NaN word. -/
theorem softMulSpecialL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b finite : Nat → Option (List II × Nat)} {av bv fv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (hf : WordCode (L := L) ρ W finite fv) :
    WordCode (L := L) ρ W (fun d => softMulSpecialL d a b finite)
      (softMulSpecialWord av bv fv) := by
  have ia : WordCode (L := L) ρ W _ _ := routineInfL_ok ha
  have ib : WordCode (L := L) ρ W _ _ := routineInfL_ok hb
  have za : WordCode (L := L) ρ W _ _ := routineZeroL_ok ha
  have zb : WordCode (L := L) ρ W _ _ := routineZeroL_ok hb
  have sa : WordCode (L := L) ρ W _ _ := unpackSignL_ok ha
  have sb : WordCode (L := L) ρ W _ _ := unpackSignL_ok hb
  have sign : WordCode (L := L) ρ W _ _ := xorSignL_ok sa sb
  have invalidA : WordCode (L := L) ρ W _ _ := WordCode.bin ia zb (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have invalidB : WordCode (L := L) ρ W _ _ := WordCode.bin za ib (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  rw [flagAnd] at invalidA invalidB
  have invalid : WordCode (L := L) ρ W _ _ := WordCode.bin invalidA invalidB (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  have infinity : WordCode (L := L) ρ W _ _ := WordCode.bin ia ib (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  have isZero : WordCode (L := L) ρ W _ _ := WordCode.bin za zb (g := fun x y => some (x ||| y))
    rfl rfl (by decide : 9 < 256)
  rw [flagOr] at invalid infinity isZero
  have zero : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 0 (by decide)
  have inf : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 2047 (by decide)
  have finiteOrZero : WordCode (L := L) ρ W _ _ := routineChooseL_ok isZero
    (fun _ => packL_ok sign zero zero) (fun _ => hf)
  have infOrFinite : WordCode (L := L) ρ W _ _ := routineChooseL_ok infinity
    (fun _ => packL_ok sign inf zero) (fun _ => finiteOrZero)
  have valid : WordCode (L := L) ρ W _ _ := routineChooseL_ok invalid
    (fun _ => WordCode.konst 9218868437227405313 (by decide)) (fun _ => infOrFinite)
  have rightNan : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok (routineNanL_ok hb) (fun _ => hb) (fun _ => valid)
  have result : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok (routineNanL_ok ha) (fun _ => ha) (fun _ => rightNan)
  intro fp K d c top emitted fits m pc pre
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

omit [Kern] in
private theorem signXor (a b : Bool) :
    Runner.IR.bool a ^^^ Runner.IR.bool b = Runner.IR.bool (a != b) := by
  cases a <;> cases b <;> rfl

omit [Kern] in
private theorem specialZeroPack (sign : Bool) :
    packWord (Runner.IR.bool sign) 0 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨sign, 0, 0⟩) :=
  packWord_canonical ⟨sign, 0, 0⟩ (by
    change 0 ≤ 2047 ∧ 0 < 2 ^ 52
    constructor <;> decide)

omit [Kern] in
private theorem specialInfPack (sign : Bool) :
    packWord (Runner.IR.bool sign) 2047 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨sign, 2047, 0⟩) :=
  packWord_canonical ⟨sign, 2047, 0⟩ (by
    change 2047 ≤ 2047 ∧ 0 < 2 ^ 52
    constructor <;> decide)

omit [Kern] in
private theorem specialNanPack :
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
/-- Compare only the class decisions; operand encodings remain opaque here. -/
private theorem specialClass_model (encode : GFloat → Runner.W) (a b : GFloat)
    (finite : Runner.W) :
    (if decide (klasse f64 a = .nan) then encode a
    else if decide (klasse f64 b = .nan) then encode b
    else if (decide (klasse f64 a = .unendlich) && decide (klasse f64 b = .null)) ||
        (decide (klasse f64 a = .null) && decide (klasse f64 b = .unendlich)) then
      encode (nanQ f64)
    else if decide (klasse f64 a = .unendlich) || decide (klasse f64 b = .unendlich) then
      encode ⟨a.sign != b.sign, 2047, 0⟩
    else if decide (klasse f64 a = .null) || decide (klasse f64 b = .null) then
      encode ⟨a.sign != b.sign, 0, 0⟩
    else finite) =
      match softMulSpecial a b with
      | some r => encode r
      | none => finite := by
  unfold softMulSpecial
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;> rfl

omit [Kern] in
/-- The dispatcher agrees with the source decomposition for every pair of
    well-formed inputs and every finite continuation supplied by the caller. -/
theorem softMulSpecialWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (finite : Runner.W) :
    softMulSpecialWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) finite =
      match softMulSpecial a b with
      | some r => BitVec.ofNat 64 (zuBits f64 r)
      | none => finite := by
  obtain ⟨sa, _, _⟩ := routineUnpack_canonical a ha
  obtain ⟨sb, _, _⟩ := routineUnpack_canonical b hb
  obtain ⟨an, ai, az⟩ := routineClass_canonical a ha
  obtain ⟨bn, bi, bz⟩ := routineClass_canonical b hb
  refine Eq.trans ?_ (specialClass_model (fun r => BitVec.ofNat 64 (zuBits f64 r)) a b finite)
  unfold softMulSpecialWord
  rw [sa, sb, signXor, an, bn, ai, az, bi, bz]
  dsimp only
  rw [specialZeroPack, specialInfPack, specialNanPack]

/-- Invalid operations, NaN priority and the sign of both zero and infinity
    instantiate the same dispatcher, independently of the finite result. -/
theorem softMulSpecialWord_zeuge :
    softMulSpecialWord 0 (BitVec.ofNat 64 9218868437227405312) 42 =
      BitVec.ofNat 64 9218868437227405313 ∧
    softMulSpecialWord (BitVec.ofNat 64 18442240474082181127)
      (BitVec.ofNat 64 9218868437227405321) 42 = BitVec.ofNat 64 18442240474082181127 ∧
    softMulSpecialWord (BitVec.ofNat 64 9223372036854775808)
      (BitVec.ofNat 64 4607182418800017408) 42 = BitVec.ofNat 64 9223372036854775808 ∧
    softMulSpecialWord (BitVec.ofNat 64 18442240474082181120)
      (BitVec.ofNat 64 13830554455654793216) 42 = BitVec.ofNat 64 9218868437227405312 := by
  decide +kernel

#print axioms softMulSpecialL_word
#print axioms softMulSpecialWord_model
#print axioms softMulSpecialWord_zeuge
end Gabbro.Stage0.Senke
