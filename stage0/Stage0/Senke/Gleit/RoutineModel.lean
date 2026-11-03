/- Connect the emitted special dispatcher to the canonical IEEE dispatcher. -/
module
public import Stage0.Senke.Gleit.RoutineSpecial
public import Stage0.Senke.Ausdruck.Arithmetik.Darstellung.Feldera
public import Stage0.Senke.Ausdruck.Gleit.Schluessel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Reuse the canonical packed-field bridges for the routine's smaller
    extraction fragments. The unmasked sign shift is already one bit wide. -/
theorem routineUnpack_canonical (a : GFloat) (ha : wf f64 a) :
    let w := BitVec.ofNat 64 (zuBits f64 a)
    unpackSignWord w = Runner.IR.bool a.sign ∧
    unpackBexpWord w = BitVec.ofNat 64 a.bexp ∧
    unpackFracWord w = BitVec.ofNat 64 a.frac := by
  obtain ⟨frac, exp⟩ := floatFieldWord_canonical f64 f64_dicht (by decide) a ha
  have bound := zuBits_f64_lt a ha
  have mag := floatMag_lt ha
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [unpackSignWord, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    change zuBits f64 a / 2 ^ 63 = (Runner.IR.bool a.sign).toNat
    rw [float_bits]
    cases a.sign <;> simp only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, show (0 : Runner.W).toNat = 0 by decide,
      show (1 : Runner.W).toNat = 1 by decide] <;> omega
  · have exp' : (unpackBexpWord (BitVec.ofNat 64 (zuBits f64 a))).toNat = a.bexp := by
      exact exp
    have result := congrArg (BitVec.ofNat 64) exp'
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using result
  · have frac' : (unpackFracWord (BitVec.ofNat 64 (zuBits f64 a))).toNat = a.frac := by
      simpa only [floatFieldWord, BitVec.ushiftRight_zero, unpackFracWord,
        show 2 ^ f64.fracBits - 1 = (4503599627370495 : Nat) by decide] using frac
    have result := congrArg (BitVec.ofNat 64) frac'
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using result

/-- Classification flags decide exactly the canonical classes. No finite
    assumption is required: this is also the proof for NaN payload words. -/
theorem routineClass_canonical (a : GFloat) (ha : wf f64 a) :
    let w := BitVec.ofNat 64 (zuBits f64 a)
    routineNanFlag w = decide (klasse f64 a = .nan) ∧
    routineInfFlag w = decide (klasse f64 a = .unendlich) ∧
    routineZeroFlag w = decide (klasse f64 a = .null) := by
  obtain ⟨_, he, hf⟩ := routineUnpack_canonical a ha
  have be : a.bexp < 2 ^ 64 := by have := ha.1; change a.bexp ≤ 2047 at this; omega
  have bf : a.frac < 2 ^ 64 := by have := ha.2; change a.frac < 2 ^ 52 at this; omega
  have maxWord : (BitVec.ofInt 64 2047).toNat = 2047 := by decide
  have zeroWord : (BitVec.ofInt 64 0).toNat = 0 := by decide
  have eqMax : (BitVec.ofNat 64 a.bexp == BitVec.ofInt 64 2047) =
      decide (a.bexp = 2047) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt be, maxWord]
  have eqExpZero : (BitVec.ofNat 64 a.bexp == BitVec.ofInt 64 0) =
      decide (a.bexp = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt be, zeroWord]
  have eqFracZero : (BitVec.ofNat 64 a.frac == BitVec.ofInt 64 0) =
      decide (a.frac = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bf, zeroWord]
  dsimp only
  simp only [routineNanFlag, routineInfFlag, routineZeroFlag, he, hf,
    eqMax, eqExpZero, eqFracZero]
  by_cases hm : a.bexp = 2047 <;> by_cases hz : a.bexp = 0 <;>
    by_cases hfz : a.frac = 0 <;> simp [klasse, show f64.bexpMax = 2047 from rfl, hm, hz, hfz]

private theorem signEq (sa sb : Bool) :
    (Runner.IR.bool sa == Runner.IR.bool sb) = (sa == sb) := by
  cases sa <;> cases sb <;> decide

private theorem zeroPack (sa sb : Bool) :
    packWord (Runner.IR.bool sa &&& Runner.IR.bool sb) 0 0 =
      BitVec.ofNat 64 (zuBits f64 ⟨sa && sb, 0, 0⟩) := by
  cases sa <;> cases sb <;> decide +kernel

/-- The complete emitted dispatcher is the model's dispatcher, independently
    of the finite result supplied by its continuation. -/
theorem routineSpecialWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (finite : Runner.W) :
    routineSpecialWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) finite =
      match floatAddSpecial f64 a b with
      | some r => BitVec.ofNat 64 (zuBits f64 r)
      | none => finite := by
  obtain ⟨asign, _, _⟩ := routineUnpack_canonical a ha
  obtain ⟨bsign, _, _⟩ := routineUnpack_canonical b hb
  obtain ⟨an, ai, az⟩ := routineClass_canonical a ha
  obtain ⟨bn, bi, bz⟩ := routineClass_canonical b hb
  simp only [routineSpecialWord, an, ai, az, bn, bi, bz, asign, bsign,
    signEq, zeroPack]
  by_cases hna : klasse f64 a = .nan
  · simp [floatAddSpecial, hna]
  · by_cases hnb : klasse f64 b = .nan
    · simp [floatAddSpecial, hna, hnb]
    · by_cases hia : klasse f64 a = .unendlich
      · by_cases hib : klasse f64 b = .unendlich
        · cases hs : (a.sign == b.sign) <;>
            simp [floatAddSpecial, hna, hnb, hia, hib, hs, nanQ, zuBits,
              show f64.bexpMax = 2047 from rfl, show f64.fracBits = 52 from rfl]
        · simp [floatAddSpecial, hna, hnb, hia, hib]
      · by_cases hib : klasse f64 b = .unendlich
        · simp [floatAddSpecial, hna, hnb, hia, hib]
        · by_cases hza : klasse f64 a = .null <;>
            by_cases hzb : klasse f64 b = .null <;>
            simp [floatAddSpecial, hna, hnb, hia, hib, hza, hzb]

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The actual integer IR dispatcher simulates the model for arbitrary
    well-formed operands and any proved finite continuation. -/
theorem routineSpecialL_model {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right finite : Nat → Option (List II × Nat)} {fv : Runner.W}
    (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (zuBits f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (zuBits f64 b)))
    (hf : WordCode (L := L) ρ W finite fv) :
    WordCode (L := L) ρ W (fun d => routineSpecialL d left right finite)
      (match floatAddSpecial f64 a b with
       | some r => BitVec.ofNat 64 (zuBits f64 r)
       | none => fv) := by
  rw [← routineSpecialWord_model a b ha hb fv]
  exact routineSpecialL_ok hl hr hf

#print axioms routineUnpack_canonical
#print axioms routineClass_canonical
#print axioms routineSpecialWord_model
#print axioms routineSpecialL_model
end Gabbro.Stage0.Senke
