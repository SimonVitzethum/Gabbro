/- Ordered finite magnitude arithmetic for the binary64 addition routine. -/
module
public import Stage0.Senke.Gleit.RoutineSpecial
public import Stage0.Senke.Gleit.Align
public import Stage0.Senke.Gleit.AddMag
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The signless encoding orders finite magnitudes, including subnormals. -/
def routineMagnitudeWord (a : Runner.W) : Runner.W :=
  a &&& BitVec.ofNat 64 9223372036854775807

def routineMagnitudeL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 8 d (a d) (some (konstWL 4 9223372036854775807 (d + 1)))

/-- Exponent zero contributes no hidden one. The scale index is one for
    subnormals and zero, as in the existing canonical field decoder. -/
def routineSigWord (a : Runner.W) : Runner.W :=
  if unpackBexpWord a == 0 then unpackFracWord a
  else unpackFracWord a + BitVec.ofNat 64 4503599627370496

def routineIndexWord (a : Runner.W) : Runner.W :=
  unpackBexpWord a + Runner.IR.bool (unpackBexpWord a == 0)

def routineSigL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let e := fun j => unpackBexpL j a
  let f := fun j => unpackFracL j a
  let normal := fun j => wordL 3 j (f j)
    (some (konstWL 4 4503599627370496 (j + 1)))
  routineChooseL d (fun j => isExpZeroL j e) f normal

def routineIndexL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let e := fun j => unpackBexpL j a
  wordL 3 d (e d) (isExpZeroL (d + 1) e)

/-- Three low guard bits precede saturating alignment. This word records
    rounding information; it is deliberately not claimed to be the exact sum. -/
def routineDirectionalWord (large small : Runner.W) : Runner.W :=
  let lm := routineSigWord large <<< 3
  let sm := floatShiftJamWord (routineSigWord small <<< 3)
    (routineIndexWord large - routineIndexWord small)
  if (unpackSignWord large ^^^ unpackSignWord small) == 0 then lm + sm else lm - sm

def routineDirectionalL (d : Nat) (large small : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let ls := fun j => routineSigL j large
  let ss := fun j => routineSigL j small
  let li := fun j => routineIndexL j large
  let si := fun j => routineIndexL j small
  let gap := fun j => alignGapL j si li
  let lm := fun j => wordK 11 j (ls j) 3
  let sm := fun j => alignShiftL j (fun k => wordK 11 k (ss k) 3) gap
  let xor := fun j => xorSignL j (fun k => unpackSignL k large) (fun k => unpackSignL k small)
  routineChooseL d (fun j => wordK 14 j (xor j) 0)
    (fun j => addMagL j lm sm) (fun j => subMagL j lm sm)

/-- Compare unsigned magnitudes before choosing the directional arithmetic.
    A tie keeps the original operand order, including exact cancellation. -/
def routineAlignWord (a b : Runner.W) : Runner.W :=
  if (routineMagnitudeWord a).ult (routineMagnitudeWord b) then
    routineDirectionalWord b a else routineDirectionalWord a b

def routineAlignL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  routineChooseL d
    (fun j => routineLessL j (fun k => routineMagnitudeL k a) (fun k => routineMagnitudeL k b))
    (fun j => routineDirectionalL j b a) (fun j => routineDirectionalL j a b)

/-- The magnitude reader needs no assumption about the float's class. -/
theorem routineMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => routineMagnitudeL d a) (routineMagnitudeWord av) :=
  WordCode.bin ha (WordCode.konst 9223372036854775807 (by decide))
    (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)

theorem routineSigL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => routineSigL d a) (routineSigWord av) := by
  have e := unpackBexpL_ok ha
  have f := unpackFracL_ok ha
  have normal := WordCode.bin f (WordCode.konst 4503599627370496 (by decide))
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  exact routineChooseL_ok (isExpZeroL_ok e) (fun _ => f) (fun _ => normal)

theorem routineIndexL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => routineIndexL d a) (routineIndexWord av) :=
  WordCode.bin (unpackBexpL_ok ha) (isExpZeroL_ok (unpackBexpL_ok ha))
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)

/-- Compose the gap, shift-with-sticky, sign xor and magnitude pieces.
    This theorem records exactly the word computation, without replacing
    the discarded remainder by its sticky flag in the model's exact sum. -/
theorem routineDirectionalL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {large small : Nat → Option (List II × Nat)} {lv sv : Runner.W}
    (hl : WordCode (L := L) ρ W large lv) (hs : WordCode (L := L) ρ W small sv) :
    WordCode (L := L) ρ W (fun d => routineDirectionalL d large small)
      (routineDirectionalWord lv sv) := by
  have lm := WordCode.bin (routineSigL_ok hl) (WordCode.const 3 (by decide))
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have ss := WordCode.bin (routineSigL_ok hs) (WordCode.const 3 (by decide))
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have gap := alignGapL_ok (routineIndexL_ok hs) (routineIndexL_ok hl)
  have sm := alignShiftL_ok ss gap
  have xor := xorSignL_ok (unpackSignL_ok hl) (unpackSignL_ok hs)
  have same := WordCode.bin xor (WordCode.const 0 (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  exact routineChooseL_ok same (fun _ => addMagL_ok lm sm) (fun _ => subMagL_ok lm sm)

/-- Both operand orders use the same directional routine. Unsigned comparison
    selects the order from the actual words, without an ordering premise. -/
theorem routineAlignL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => routineAlignL d a b) (routineAlignWord av bv) :=
  routineChooseL_ok (routineLessL_ok (routineMagnitudeL_ok ha) (routineMagnitudeL_ok hb))
    (fun _ => routineDirectionalL_ok hb ha) (fun _ => routineDirectionalL_ok ha hb)

/-- Unequal exponents in both orders, exact cancellation and subnormal
    addition jointly exercise the actual ordered arithmetic. -/
theorem routineAlignWord_zeuge :
    routineAlignWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 (3 * 2 ^ 54) ∧
    routineAlignWord (BitVec.ofNat 64 4611686018427387904)
      (BitVec.ofNat 64 4607182418800017408) = BitVec.ofNat 64 (3 * 2 ^ 54) ∧
    routineAlignWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 13830554455654793216) = 0 ∧
    routineAlignWord 1 1 = 16 := by
  decide +kernel

#print axioms routineAlignL_ok
#print axioms routineAlignWord_zeuge
end Gabbro.Stage0.Senke
