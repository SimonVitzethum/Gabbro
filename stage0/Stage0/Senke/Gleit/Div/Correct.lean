/- Total kernel-model and emitted-integer-IR correctness for binary64 division. -/
module
public import Stage0.Senke.Gleit.Div.FiniteModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Dispatch and the finite quotient together cover every well-formed pair,
    including NaN payloads, invalid ratios and xor-signed zeros/infinities. -/
theorem softDivRoutineWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    softDivRoutineWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (div f64 a b)) := by
  unfold softDivRoutineWord
  rw [softDivSpecialWord_model a b ha hb, ← softDivCore_model]
  cases special : softDivSpecial a b with
  | some r => rw [softDivCore, special]
  | none => exact softDivFiniteWord_model a b ha hb special

/-- Total word correspondence without a finite-input premise. -/
theorem softDivRoutine_ok (a b : UInt64) :
    softDivRoutineWord a.toBitVec b.toBitVec = (softDiv a b).toBitVec := by
  have model := softDivRoutineWord_model (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  have left := routineWord_decode a.toBitVec
  have right := routineWord_decode b.toBitVec
  simp only [UInt64.toNat_toBitVec] at left right
  change BitVec.ofNat 64 (zuBits f64 (u64ToG a)) = a.toBitVec at left
  change BitVec.ofNat 64 (zuBits f64 (u64ToG b)) = b.toBitVec at right
  rw [left, right] at model
  rw [← softDiv_bits] at model
  simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq] using model

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The finite loop is justified only after the dispatcher's actual flags
    have excluded zero and nonfinite operands. Every emitted branch retains
    the same WordCode memory contract as addition and multiplication. -/
theorem softDivRoutineL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (zuBits f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (zuBits f64 b))) :
    WordCode (L := L) ρ W (fun d => softDivRoutineL d left right)
      (BitVec.ofNat 64 (zuBits f64 (div f64 a b))) := by
  rw [← softDivRoutineWord_model a b ha hb]
  apply softDivSpecialL_word hl hr
  intro nanA nanB infinityFalse zeroFalse
  obtain ⟨an, ai, az⟩ := routineClass_canonical a ha
  obtain ⟨bn, bi, bz⟩ := routineClass_canonical b hb
  rw [an] at nanA
  rw [bn] at nanB
  rw [ai, bz] at infinityFalse
  rw [bi, az] at zeroFalse
  have special : softDivSpecial a b = none := by
    cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
      simp_all [softDivSpecial]
  have finite : WordCode (L := L) ρ W _ _ :=
    softDivFiniteL_model a b ha hb special hl hr
  intro fp K d c top emitted fits m pc pre
  exact finite (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

/-- All requested result classes instantiate the unrestricted word theorem. -/
theorem softDivRoutine_ok_zeuge :
    softDivRoutineWord (4613937818241073152 : UInt64).toBitVec
      (4611686018427387904 : UInt64).toBitVec =
      (softDiv 4613937818241073152 4611686018427387904).toBitVec ∧
    softDivRoutineWord (4607182418800017408 : UInt64).toBitVec
      (4613937818241073152 : UInt64).toBitVec =
      (softDiv 4607182418800017408 4613937818241073152).toBitVec ∧
    softDivRoutineWord (4503599627370496 : UInt64).toBitVec
      (4611686018427387904 : UInt64).toBitVec =
      (softDiv 4503599627370496 4611686018427387904).toBitVec ∧
    softDivRoutineWord (4607182418800017408 : UInt64).toBitVec 0 =
      (softDiv 4607182418800017408 0).toBitVec ∧
    softDivRoutineWord 0 0 = (softDiv 0 0).toBitVec :=
  ⟨softDivRoutine_ok _ _, softDivRoutine_ok _ _, softDivRoutine_ok _ _,
    softDivRoutine_ok _ _, softDivRoutine_ok _ _⟩

/-- A non-degenerate ordinary quotient instantiates the actual emitter's
    simulation theorem, rather than just its mathematical word function. -/
theorem softDivRoutineL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softDivRoutineL d
      (fun j => some (konstWL 4 4613937818241073152 j))
      (fun j => some (konstWL 4 4611686018427387904 j)))
      (BitVec.ofNat 64 4609434218613702656) := by
  have run : WordCode (L := L) ρ W _ _ := softDivRoutineL_ok (L := L) (ρ := ρ) (W := W)
    (⟨false, 1024, 2 ^ 51⟩ : GFloat) (⟨false, 1024, 0⟩ : GFloat)
    (by decide) (by decide)
    (WordCode.konst 4613937818241073152 (by decide))
    (WordCode.konst 4611686018427387904 (by decide))
  intro fp K d c top emitted fits m pc pre
  exact run (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

/-- An invalid ratio still uses the same emitter theorem; its NaN result
    is subsequently rejected by the source Block's ordinary range guard. -/
theorem softDivRoutineL_invalid_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softDivRoutineL d
      (fun j => some ([ci 1 j 0 0], j + 1))
      (fun j => some ([ci 1 j 0 0], j + 1)))
      (BitVec.ofNat 64 9218868437227405313) := by
  exact softDivRoutineL_ok (⟨false, 0, 0⟩ : GFloat) (⟨false, 0, 0⟩ : GFloat)
    (by decide) (by decide) (WordCode.const 0 (by decide)) (WordCode.const 0 (by decide))

#print axioms softDivRoutineWord_model
#print axioms softDivRoutine_ok
#print axioms softDivRoutineL_ok
#print axioms softDivRoutine_ok_zeuge
#print axioms softDivRoutineL_ok_zeuge
#print axioms softDivRoutineL_invalid_zeuge
end Gabbro.Stage0.Senke
