/- The integer-IR special dispatcher for binary64 addition. -/
module
public import Stage0.Senke.Gleit.RoutineBranch
public import Stage0.Senke.Gleit.Special
public import Stage0.Senke.Gleit.Pack
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Classification flags on unpacked runner words. -/
def routineNanFlag (a : Runner.W) : Bool :=
  (unpackBexpWord a == BitVec.ofInt 64 2047) &&
    !(unpackFracWord a == BitVec.ofInt 64 0)

def routineInfFlag (a : Runner.W) : Bool :=
  (unpackBexpWord a == BitVec.ofInt 64 2047) &&
    (unpackFracWord a == BitVec.ofInt 64 0)

def routineZeroFlag (a : Runner.W) : Bool :=
  (unpackBexpWord a == BitVec.ofInt 64 0) &&
    (unpackFracWord a == BitVec.ofInt 64 0)

/-- The dispatcher is parametric in the finite result, so its correctness
    does not assume that a jammed significand is the exact original operand. -/
def routineSpecialWord (a b finite : Runner.W) : Runner.W :=
  if routineNanFlag a then a
  else if routineNanFlag b then b
  else if routineInfFlag a then
    if routineInfFlag b then
      if unpackSignWord a == unpackSignWord b then a
      else BitVec.ofNat 64 9218868437227405313
    else a
  else if routineInfFlag b then b
  else if routineZeroFlag a && routineZeroFlag b then
    packWord (unpackSignWord a &&& unpackSignWord b) 0 0
  else finite

/-- NaNs retain their complete input word, including sign and payload.
    Opposite infinities select the kernel's `nanQ` word, and two zeros retain
    precisely the conjunction of their signs. All choices use checked jumps. -/
def routineSpecialL (d : Nat) (a b finite : Nat → Option (List II × Nat)) :
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
  let sa := fun j => unpackSignL j a
  let sb := fun j => unpackSignL j b
  let sameSign := fun j => wordL 14 j (sa j) (sb (j + 1))
  let bothZero := fun j => wordL 8 j (za j) (zb (j + 1))
  let zero := fun (j : Nat) => some ([ci 1 j 0 0], j + 1)
  let zeroSign := fun j => wordL 8 j (sa j) (sb (j + 1))
  let signedZero := fun j => packL j zeroSign zero zero
  let nan := fun j => some (konstWL 4 9218868437227405313 j)
  let infPair := fun j => routineChooseL j sameSign a nan
  let infLeft := fun j => routineChooseL j ib infPair a
  let finiteOrZero := fun j => routineChooseL j bothZero signedZero finite
  let infRight := fun j => routineChooseL j ib b finiteOrZero
  let infinities := fun j => routineChooseL j ia infLeft infRight
  let rightNan := fun j => routineChooseL j nb b infinities
  routineChooseL d na a rightNan

private theorem flagAnd (a b : Bool) :
    Runner.IR.bool a &&& Runner.IR.bool b = Runner.IR.bool (a && b) := by
  cases a <;> cases b <;> decide

private theorem flagAndNot (a b : Bool) :
    Runner.IR.bool a &&& (BitVec.ofInt 64 1 - Runner.IR.bool b) =
      Runner.IR.bool (a && !b) := by
  cases a <;> cases b <;> decide

/-- Classifying an input reuses the unpack and classification piece lemmas. -/
theorem routineNanL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => isNanL d
      (fun j => unpackBexpL j a) (fun j => unpackFracL j a))
      (Runner.IR.bool (routineNanFlag av)) := by
  intro fp K d c top hh hK m pc hp
  have h := (isNanL_ok (unpackBexpL_ok ha) (unpackFracL_ok ha)) hh hK m pc hp
  simpa only [isNanWord, isFracNonzeroWord, flagAndNot, routineNanFlag] using h

theorem routineInfL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => isInfL d
      (fun j => unpackBexpL j a) (fun j => unpackFracL j a))
      (Runner.IR.bool (routineInfFlag av)) := by
  intro fp K d c top hh hK m pc hp
  have h := (isInfL_ok (unpackBexpL_ok ha) (unpackFracL_ok ha)) hh hK m pc hp
  simpa only [isInfWord, flagAnd, routineInfFlag] using h

theorem routineZeroL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => isZeroL d
      (fun j => unpackBexpL j a) (fun j => unpackFracL j a))
      (Runner.IR.bool (routineZeroFlag av)) := by
  intro fp K d c top hh hK m pc hp
  have h := (isZeroL_ok (unpackBexpL_ok ha) (unpackFracL_ok ha)) hh hK m pc hp
  simpa only [isZeroWord, flagAnd, routineZeroFlag] using h

/-- Composition of the actual dispatcher IR. The only finite-path premise
    is its word-code proof; each special branch uses the existing pieces. -/
theorem routineSpecialL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b finite : Nat → Option (List II × Nat)} {av bv fv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (hf : WordCode (L := L) ρ W finite fv) :
    WordCode (L := L) ρ W (fun d => routineSpecialL d a b finite)
      (routineSpecialWord av bv fv) := by
  have sa : WordCode (L := L) ρ W _ _ := unpackSignL_ok ha
  have sb : WordCode (L := L) ρ W _ _ := unpackSignL_ok hb
  have sameSign : WordCode (L := L) ρ W _ _ := WordCode.bin sa sb
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have bothZero : WordCode (L := L) ρ W _ _ := WordCode.bin (routineZeroL_ok ha) (routineZeroL_ok hb)
    (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  rw [flagAnd] at bothZero
  have zeroSign : WordCode (L := L) ρ W _ _ := WordCode.bin sa sb (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have zero : WordCode (L := L) ρ W
      (fun j => some ([ci 1 j 0 0], j + 1)) 0 := WordCode.const 0 (by decide)
  have signedZero : WordCode (L := L) ρ W _ _ := packL_ok zeroSign zero zero
  have nan : WordCode (L := L) ρ W _ _ := WordCode.konst (L := L) (ρ := ρ) (W := W)
    9218868437227405313 (by decide)
  have infPair : WordCode (L := L) ρ W _ _ := routineChooseL_ok sameSign (fun _ => ha) (fun _ => nan)
  have infLeft : WordCode (L := L) ρ W _ _ := routineChooseL_ok (routineInfL_ok hb) (fun _ => infPair) (fun _ => ha)
  have finiteOrZero : WordCode (L := L) ρ W _ _ := routineChooseL_ok bothZero (fun _ => signedZero) (fun _ => hf)
  have infRight : WordCode (L := L) ρ W _ _ := routineChooseL_ok (routineInfL_ok hb) (fun _ => hb) (fun _ => finiteOrZero)
  have infinities : WordCode (L := L) ρ W _ _ := routineChooseL_ok (routineInfL_ok ha) (fun _ => infLeft) (fun _ => infRight)
  have rightNan : WordCode (L := L) ρ W _ _ := routineChooseL_ok (routineNanL_ok hb) (fun _ => hb) (fun _ => infinities)
  exact routineChooseL_ok (routineNanL_ok ha) (fun _ => ha) (fun _ => rightNan)

/-- Payload priority, opposite infinities, negative zeros and finite fallthrough
    all exercise the same dispatcher used in the emitted routine. -/
theorem routineSpecialWord_zeuge :
    routineSpecialWord (BitVec.ofNat 64 18442240474082181127)
      (BitVec.ofNat 64 9218868437227405321) 42 = BitVec.ofNat 64 18442240474082181127 ∧
    routineSpecialWord (BitVec.ofNat 64 9218868437227405312)
      (BitVec.ofNat 64 18442240474082181120) 42 = BitVec.ofNat 64 9218868437227405313 ∧
    routineSpecialWord (BitVec.ofNat 64 9223372036854775808)
      (BitVec.ofNat 64 9223372036854775808) 42 = BitVec.ofNat 64 9223372036854775808 ∧
    routineSpecialWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 4611686018427387904) 42 = 42 := by
  decide +kernel

#print axioms routineSpecialL_ok
#print axioms routineSpecialWord_zeuge
end Gabbro.Stage0.Senke
