/- Total source-model and emitted-IR correctness for binary64 multiplication.
   The public word theorem has no side conditions on input classes.
   The emitted-code theorem preserves the caller's memory interface.
   Block lowering adds its existing finite-result and range checks. -/
module
public import Stage0.Senke.Gleit.Mul.FiniteModel
public import Stage0.Senke.Gleit.Normal.Model
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Special dispatch and the finite continuation jointly implement the
    kernel operation, with every well-formed pair of inputs admitted. -/
theorem softMulRoutineWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    softMulRoutineWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (mul f64 a b)) := by
  unfold softMulRoutineWord
  rw [softMulSpecialWord_model a b ha hb, ← softMulCore_model]
  cases special : softMulSpecial a b with
  | some r => rw [softMulCore, special]
  | none => exact softMulFiniteWord_model a b ha hb special

/-- Total binary64 word identity, including arbitrary NaN payloads, signed
    zero, gradual underflow and infinity. There is no finite-input premise. -/
theorem softMulRoutine_ok (a b : UInt64) :
    softMulRoutineWord a.toBitVec b.toBitVec = (softMul a b).toBitVec := by
  have model := softMulRoutineWord_model (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  have left := routineWord_decode a.toBitVec
  have right := routineWord_decode b.toBitVec
  simp only [UInt64.toNat_toBitVec] at left right
  change BitVec.ofNat 64 (zuBits f64 (u64ToG a)) = a.toBitVec at left
  change BitVec.ofNat 64 (zuBits f64 (u64ToG b)) = b.toBitVec at right
  rw [left, right] at model
  rw [← softMul_bits] at model
  simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq] using model

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The emitted integer IR computes canonical source multiplication, using
    the same generic memory simulation interface as addition. -/
theorem softMulRoutineL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (zuBits f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (zuBits f64 b))) :
    WordCode (L := L) ρ W (fun d => softMulRoutineL d left right)
      (BitVec.ofNat 64 (zuBits f64 (mul f64 a b))) := by
  rw [← softMulRoutineWord_model a b ha hb]
  exact softMulRoutineL_word hl hr

/-- The total theorem is instantiated at each requested class of example. -/
theorem softMulRoutine_ok_zeuge :
    softMulRoutineWord (4609434218613702656 : UInt64).toBitVec
      (4611686018427387904 : UInt64).toBitVec =
      (softMul 4609434218613702656 4611686018427387904).toBitVec ∧
    softMulRoutineWord (4607182418800017409 : UInt64).toBitVec
      (4607182418800017409 : UInt64).toBitVec =
      (softMul 4607182418800017409 4607182418800017409).toBitVec ∧
    softMulRoutineWord (4503599627370496 : UInt64).toBitVec
      (4602678819172646912 : UInt64).toBitVec =
      (softMul 4503599627370496 4602678819172646912).toBitVec ∧
    softMulRoutineWord 0 (9218868437227405312 : UInt64).toBitVec =
      (softMul 0 9218868437227405312).toBitVec :=
  ⟨softMulRoutine_ok _ _, softMulRoutine_ok _ _, softMulRoutine_ok _ _, softMulRoutine_ok _ _⟩

/-- A closed ordinary product uses the actual emitter simulation, rather
    than a model-only witness of the desired output. -/
theorem softMulRoutineL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softMulRoutineL d
      (fun j => some (konstWL 4 4609434218613702656 j))
      (fun j => some (konstWL 4 4611686018427387904 j)))
      (BitVec.ofNat 64 4613937818241073152) := by
  have run : WordCode (L := L) ρ W _ _ := softMulRoutineL_word (L := L) (ρ := ρ) (W := W)
    (WordCode.konst 4609434218613702656 (by decide))
    (WordCode.konst 4611686018427387904 (by decide))
  intro fp K d c top emitted fits m pc pre
  simpa only [show softMulRoutineWord (BitVec.ofNat 64 4609434218613702656)
    (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 4613937818241073152
    from by decide +kernel] using
    run (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

/-- Invalid multiplication still emits the common routine; source Block
    lowering will reject its NaN result through the ordinary result guard. -/
theorem softMulRoutineL_invalid_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softMulRoutineL d
      (fun j => some ([ci 1 j 0 0], j + 1))
      (fun j => some (konstWL 4 9218868437227405312 j)))
      (BitVec.ofNat 64 9218868437227405313) := by
  have run : WordCode (L := L) ρ W _ _ := softMulRoutineL_word (L := L) (ρ := ρ) (W := W)
    (WordCode.const 0 (by decide)) (WordCode.konst 9218868437227405312 (by decide))
  intro fp K d c top emitted fits m pc pre
  simpa only [show BitVec.ofInt 64 0 = (0 : Runner.W) from rfl,
    show softMulRoutineWord 0 (BitVec.ofNat 64 9218868437227405312) =
    BitVec.ofNat 64 9218868437227405313 from by decide +kernel] using
    run (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

#print axioms softMulRoutineWord_model
#print axioms softMulRoutine_ok
#print axioms softMulRoutineL_ok
#print axioms softMulRoutine_ok_zeuge
#print axioms softMulRoutineL_ok_zeuge
#print axioms softMulRoutineL_invalid_zeuge
end Gabbro.Stage0.Senke
