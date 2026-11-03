/- Total correctness of the integer-only binary64 addition routine. -/
module
public import Stage0.Senke.Gleit.Normal.Finite
public import Stage0.Senke.Gleit.Normal.SourceModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

private theorem exactAddComm (u v : Exakt) : exaktAdd u v = exaktAdd v u := by
  rw [floatAdd_align, floatAdd_align]
  by_cases uv : u.zweierExp ≤ v.zweierExp
  · by_cases vu : v.zweierExp ≤ u.zweierExp
    · have same : u.zweierExp = v.zweierExp := by omega
      simp only [if_pos uv, if_pos vu, same, sub_self, Int.toNat_zero,
        Nat.pow_zero, Nat.cast_one, mul_one]
      congr 1
      omega
    · simp only [if_pos uv, if_neg vu]
      congr 1
      omega
  · have vu : v.zweierExp ≤ u.zweierExp := by omega
    simp only [if_neg uv, if_pos vu]
    congr 1
    omega

/-- Compose source alignment, the actual normalization branch and packing.
    Cancellation is selected before sign packing and rounds to positive zero. -/
theorem routineFiniteDirectionalWord_model (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (u v : Exakt)
    (hu : wertExakt f64 a = some u) (hv : wertExakt f64 b = some v)
    (order : floatMag b ≤ floatMag a) :
    routineFiniteDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (rundeExakt f64 (exaktAdd u v))) := by
  let n := softAlignedMagnitude a.sign b.sign (softSig a.bexp a.frac)
    (softSig b.bexp b.frac) (max a.bexp 1 - max b.bexp 1)
  have lb : softSig a.bexp a.frac < 2 ^ 53 := by unfold softSig; split <;> have := ha.2 <;> omega
  have rb : softSig b.bexp b.frac < 2 ^ 53 := by unfold softSig; split <;> have := hb.2 <;> omega
  have indices := routineOrder_indices a b ha hb order
  obtain ⟨equal, different⟩ := routineSource_order a b ha hb order
  have data := softAlignedMagnitude_bounds a.sign b.sign _ _ _ _ lb rb
    (by omega) indices equal different
  have magnitude := routineDirectionalWord_canonical a b ha hb order
  have source := routineSource_sum a b ha hb u v hu hv order
  have index := (routineSigIndex_canonical a ha).2
  have sign := (routineUnpack_canonical a ha).1
  have finite := routineSource_finite a u hu
  have expBound : max a.bexp 1 ≤ 2046 := by have := ha.1; change a.bexp ≤ 2047 at this; omega
  have n64 : n < 2 ^ 64 := by have := data.2.2.1; omega
  rw [magnitude, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n64] at source
  rw [source]
  rcases data.2.2.2.1 with zero | positive
  · have zeroWord : routineDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
        (BitVec.ofNat 64 (zuBits f64 b)) = 0 := by rw [magnitude, zero]; rfl
    rw [routineFiniteDirectionalWord_zero _ _ zeroWord,
      rundeExakt_null f64 _ (by cases a.sign <;> simp only [zero, Int.natCast_zero, neg_zero, ite_self])]
    rfl
  · exact routineFiniteDirectionalWord_exact _ _ a.sign n (max a.bexp 1)
      magnitude index sign positive data.2.2.1 (by omega) expBound

/-- Both operand orders execute the same proved directional continuation. -/
theorem routineFiniteWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (u v : Exakt) (hu : wertExakt f64 a = some u) (hv : wertExakt f64 b = some v) :
    routineFiniteWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (rundeExakt f64 (exaktAdd u v))) := by
  unfold routineFiniteWord
  rw [routineOrder_canonical a b ha hb]
  by_cases order : floatMag a < floatMag b
  · rw [if_pos (by simpa using order)]
    rw [routineFiniteDirectionalWord_model b a hb ha v u hv hu (by omega), exactAddComm v u]
  · rw [if_neg (by simpa using order)]
    exact routineFiniteDirectionalWord_model a b ha hb u v hu hv (by omega)

/-- Special dispatch and both finite branches agree with the canonical adder
    on every well-formed pair, including both signed zeros and all NaNs. -/
theorem softAddRoutineWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    softAddRoutineWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (add f64 a b)) := by
  unfold softAddRoutineWord
  rw [routineSpecialWord_model a b ha hb, floatAddSpecial_model]
  cases special : floatAddSpecial f64 a b with
  | some r => rfl
  | none =>
    obtain ⟨u, v, hu, hv⟩ := floatAddSpecial_none_exact f64 a b special
    rw [hu, hv]
    exact routineFiniteWord_model a b ha hb u v hu hv

/-- Every runner word is exactly the encoding of its canonical decode. -/
theorem routineWord_decode (a : Runner.W) :
    BitVec.ofNat 64 (zuBits f64 (ausBits f64 a.toNat)) = a := by
  have bound := a.isLt
  have bits : zuBits f64 (ausBits f64 a.toNat) = a.toNat := by
    change (if (a.toNat / 2 ^ 63) % 2 == 1 then 2 ^ 63 else 0) +
      ((a.toNat / 2 ^ 52) % 2 ^ 11) * 2 ^ 52 + a.toNat % 2 ^ 52 = a.toNat
    split <;> rename_i sign <;> simp only [beq_iff_eq] at sign <;> omega
  rw [bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Total word identity: the emitted routine implements the composed source
    adder for every pair of binary64 words, with no finite-input premise. -/
theorem softAddRoutine_ok (a b : UInt64) :
    softAddRoutineWord a.toBitVec b.toBitVec = (softAddComposed a b).toBitVec := by
  have model := softAddRoutineWord_model (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  have left := routineWord_decode a.toBitVec
  have right := routineWord_decode b.toBitVec
  simp only [UInt64.toNat_toBitVec] at left right
  change BitVec.ofNat 64 (zuBits f64 (u64ToG a)) = a.toBitVec at left
  change BitVec.ofNat 64 (zuBits f64 (u64ToG b)) = b.toBitVec at right
  rw [left, right] at model
  rw [← softAddComposed_bits] at model
  simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq] using model

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The generic emitted IR simulation now ends in the canonical source sum. -/
theorem softAddRoutineL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (zuBits f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (zuBits f64 b))) :
    WordCode (L := L) ρ W (fun d => softAddRoutineL d left right)
      (BitVec.ofNat 64 (zuBits f64 (add f64 a b))) := by
  rw [← softAddRoutineWord_model a b ha hb]
  exact softAddRoutineL_word hl hr

/-- Both orders, cancellation, the subnormal floor and a gap beyond word
    width instantiate the total word theorem. -/
theorem softAddRoutine_ok_zeuge :
    softAddRoutineWord (4607182418800017408 : UInt64).toBitVec
      (4611686018427387904 : UInt64).toBitVec =
      (softAddComposed 4607182418800017408 4611686018427387904).toBitVec ∧
    softAddRoutineWord (4611686018427387904 : UInt64).toBitVec
      (4607182418800017408 : UInt64).toBitVec =
      (softAddComposed 4611686018427387904 4607182418800017408).toBitVec ∧
    softAddRoutineWord (4607182418800017408 : UInt64).toBitVec
      (13830554455654793216 : UInt64).toBitVec = 0 ∧
    softAddRoutineWord 1 1 = 2 ∧
    softAddRoutineWord (4607182418800017408 : UInt64).toBitVec 1 =
      (4607182418800017408 : UInt64).toBitVec := by
  refine ⟨softAddRoutine_ok _ _, softAddRoutine_ok _ _, ?_⟩
  decide +kernel

#print axioms routineFiniteDirectionalWord_model
#print axioms softAddRoutine_ok
#print axioms softAddRoutineL_ok
#print axioms softAddRoutine_ok_zeuge
end Gabbro.Stage0.Senke
