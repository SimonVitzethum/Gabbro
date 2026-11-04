/- Compose finite binary64 addition from alignment, normalization and packing. -/
module
public import Stage0.Senke.Gleit.Normal.Pack
public import Stage0.Senke.Gleit.Normal.GuardModel
public import Stage0.Senke.Gleit.Routine.RoutineOrderModel
public import Stage0.Senke.Gleit.Compose
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Operands are ordered by magnitude before entering this continuation.
    Exact cancellation selects positive zero before sign packing. -/
def routineFiniteDirectionalWord (large small : Runner.W) : Runner.W :=
  let m := routineDirectionalWord large small
  let e := routineIndexWord large
  let s := unpackSignWord large
  let c := routineLeftCountWord m e
  if m == 0 then 0
  else if m.ult (BitVec.ofNat 64 (2 ^ 56)) then
    routineRoundPackWord s (e - c) (m <<< (c.toNat % 64))
  else routineRoundPackWord s (e + 1) (floatShiftJamWord m 1)

def routineFiniteDirectionalL (d : Nat) (large small : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let m := fun j => routineDirectionalL j large small
  let e := fun j => routineIndexL j large
  let s := fun j => unpackSignL j large
  let c := fun j => routineLeftCountL j m e
  let left := fun j => routineRoundPackL j s
    (fun k => wordL 4 k (e k) (c (k + 1)))
    (fun k => wordL 11 k (m k) (c (k + 1)))
  let right := fun j => routineRoundPackL j s
    (fun k => wordK 3 k (e k) 1)
    (fun k => floatShiftJamL k m (fun v => some ([ci 1 v 1 0], v + 1)))
  let normalized := fun j => routineChooseL j
    (fun k => routineLessL k m (fun v => some (konstWL 4 (2 ^ 56) v))) left right
  routineChooseL d (fun j => wordK 14 j (m j) 0)
    (fun j => some ([ci 1 j 0 0], j + 1)) normalized

theorem routineFiniteDirectionalL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {large small : Nat → Option (List II × Nat)} {lv sv : Runner.W}
    (hl : WordCode (L := L) ρ W large lv) (hs : WordCode (L := L) ρ W small sv) :
    WordCode (L := L) ρ W (fun d => routineFiniteDirectionalL d large small)
      (routineFiniteDirectionalWord lv sv) := by
  have m : WordCode (L := L) ρ W _ _ := routineDirectionalL_ok hl hs
  have e : WordCode (L := L) ρ W _ _ := routineIndexL_ok hl
  have s : WordCode (L := L) ρ W _ _ := unpackSignL_ok hl
  have count : WordCode (L := L) ρ W _ _ := routineLeftCountL_word m e
  have leftE : WordCode (L := L) ρ W _ _ := WordCode.bin e count
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have leftM : WordCode (L := L) ρ W _ _ := WordCode.bin m count
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have left : WordCode (L := L) ρ W _ _ := routineRoundPackL_ok s leftE leftM
  have rightE : WordCode (L := L) ρ W _ _ := WordCode.bin e (WordCode.const 1 (by decide))
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  have rightM : WordCode (L := L) ρ W _ _ := floatShiftJamL_ok m (WordCode.const 1 (by decide))
  have right : WordCode (L := L) ρ W _ _ := routineRoundPackL_ok s rightE rightM
  have normalized : WordCode (L := L) ρ W _ _ := routineChooseL_ok
    (routineLessL_ok m (WordCode.konst (2 ^ 56) (by decide)))
    (fun _ => left) (fun _ => right)
  have zero : WordCode (L := L) ρ W _ _ := WordCode.bin m (WordCode.const 0 (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have result : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok zero (fun _ => WordCode.const 0 (by decide)) (fun _ => normalized)
  intro fp K d c top emitted fits m pc pre
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

def routineFiniteWord (a b : Runner.W) : Runner.W :=
  if (routineMagnitudeWord a).ult (routineMagnitudeWord b) then
    routineFiniteDirectionalWord b a else routineFiniteDirectionalWord a b

def routineFiniteL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  routineChooseL d
    (fun j => routineLessL j (fun k => routineMagnitudeL k a) (fun k => routineMagnitudeL k b))
    (fun j => routineFiniteDirectionalL j b a) (fun j => routineFiniteDirectionalL j a b)

theorem routineFiniteL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => routineFiniteL d a b) (routineFiniteWord av bv) :=
  routineChooseL_ok (routineLessL_ok (routineMagnitudeL_ok ha) (routineMagnitudeL_ok hb))
    (fun _ => routineFiniteDirectionalL_word hb ha) (fun _ => routineFiniteDirectionalL_word ha hb)

/-- One integer-only routine handles the special dispatcher and finite path.
    The kernel equality must be established before enabling `Block.float`. -/
def softAddRoutineWord (a b : Runner.W) : Runner.W :=
  routineSpecialWord a b (routineFiniteWord a b)

def softAddRoutineL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  routineSpecialL d a b (fun j => routineFiniteL j a b)

/-- Generic execution of the full emitted routine, including both operand
    orders and every special branch. This word simulation does not assert
    the still-required equality to `softAddComposed`. -/
theorem softAddRoutineL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => softAddRoutineL d a b) (softAddRoutineWord av bv) :=
  routineSpecialL_ok ha hb (routineFiniteL_word ha hb)

/-- The complete routine already agrees with the canonical addition on
    every special-case input. The finite continuation is irrelevant there. -/
theorem softAddRoutineWord_special_model (a b : GFloat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (special : floatAddSpecial Gleitkomma.f64 a b ≠ none) :
    softAddRoutineWord (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 b)) =
      BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 (Gleitkomma.add Gleitkomma.f64 a b)) := by
  unfold softAddRoutineWord
  rw [routineSpecialWord_model a b ha hb]
  cases hs : floatAddSpecial Gleitkomma.f64 a b with
  | none => exact (special hs).elim
  | some r =>
    have model := floatAddSpecial_model Gleitkomma.f64 a b
    rw [hs] at model
    rw [model]

theorem softAddRoutineL_special_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} (a b : GFloat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 b)))
    (special : floatAddSpecial Gleitkomma.f64 a b ≠ none) :
    WordCode (L := L) ρ W (fun d => softAddRoutineL d left right)
      (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 (Gleitkomma.add Gleitkomma.f64 a b))) := by
  rw [← softAddRoutineWord_special_model a b ha hb special]
  exact softAddRoutineL_word hl hr

/-- Fixtures cover both orders, signed cancellation, subnormal output,
    overflow, a wide exact sum, NaN payload priority and negative zero. -/
theorem softAddRoutineWord_zeuge :
    softAddRoutineWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 4613937818241073152 ∧
    softAddRoutineWord (BitVec.ofNat 64 4611686018427387904)
      (BitVec.ofNat 64 4607182418800017408) = BitVec.ofNat 64 4613937818241073152 ∧
    softAddRoutineWord (BitVec.ofNat 64 4607182418800017409)
      (BitVec.ofNat 64 13830554455654793216) = BitVec.ofNat 64 4372995238176751616 ∧
    softAddRoutineWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 13830554455654793216) = 0 ∧
    softAddRoutineWord 1 1 = 2 ∧
    softAddRoutineWord (BitVec.ofNat 64 9218868437227405311)
      (BitVec.ofNat 64 9218868437227405311) = BitVec.ofNat 64 9218868437227405312 ∧
    softAddRoutineWord (BitVec.ofNat 64 4607182418800017408) 1 = BitVec.ofNat 64 4607182418800017408 ∧
    softAddRoutineWord (BitVec.ofNat 64 18442240474082181127) 1 = BitVec.ofNat 64 18442240474082181127 ∧
    softAddRoutineWord (BitVec.ofNat 64 9223372036854775808)
      (BitVec.ofNat 64 9223372036854775808) = BitVec.ofNat 64 9223372036854775808 := by
  decide +kernel

theorem softAddRoutineL_word_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softAddRoutineL d
      (fun j => some (konstWL 4 4607182418800017408 j))
      (fun j => some (konstWL 4 4611686018427387904 j)))
      (BitVec.ofNat 64 4613937818241073152) := by
  have routine : WordCode (L := L) ρ W _ _ := softAddRoutineL_word (L := L) (ρ := ρ) (W := W)
    (WordCode.konst 4607182418800017408 (by decide))
    (WordCode.konst 4611686018427387904 (by decide))
  intro fp K d c top emitted fits m pc pre
  simpa only [show softAddRoutineWord (BitVec.ofNat 64 4607182418800017408)
    (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 4613937818241073152
    from by decide +kernel] using
    routine (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

#print axioms routineFiniteDirectionalL_word
#print axioms softAddRoutineL_word
#print axioms softAddRoutineL_special_ok
#print axioms softAddRoutineWord_zeuge
#print axioms softAddRoutineL_word_zeuge
end Gabbro.Stage0.Senke
