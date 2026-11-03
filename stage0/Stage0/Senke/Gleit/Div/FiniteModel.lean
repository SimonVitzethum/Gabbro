/- Identify the actual finite division routine with its canonical source ratio. -/
module
public import Stage0.Senke.Gleit.Div.Routine
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Operand normalization and the unsigned quotient comparison identify all
    mathematical inputs of the shared rounding continuation. -/
theorem softDivFiniteWord_model (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (special : softDivSpecial a b = none) :
    softDivFiniteWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (softDivCore a b)) := by
  obtain ⟨fa, fb⟩ := softDivSpecial_none a b special
  obtain ⟨ap, ac, al, ah⟩ := softDiv_operand_bounds a ha fa
  obtain ⟨bp, bc, bl, bh⟩ := softDiv_operand_bounds b hb fb
  let sa := softSig a.bexp a.frac
  let sb := softSig b.bexp b.frac
  let ca := softMulNormalizeCount sa
  let cb := softMulNormalizeCount sb
  let na := sa * 2 ^ ca
  let nb := sb * 2 ^ cb
  let ia := max a.bexp 1 + 64 - ca
  let ib := max b.bexp 1 + 64 - cb
  let k := softDivGuardCount na nb
  let total := ia + 2278 - ib - k
  let n := na * 2 ^ k
  let m := softDivJam n nb
  have count : k = 55 ∨ k = 56 := by unfold k softDivGuardCount; split <;> simp
  have na64 : na < 2 ^ 64 := by omega
  have nb64 : nb < 2 ^ 64 := by omega
  have canonA := softMulNormalizeWord_model a ha ap
  have canonB := softMulNormalizeWord_model b hb bp
  change _ = BitVec.ofNat 64 na ∧ _ = BitVec.ofNat 64 ia at canonA
  change _ = BitVec.ofNat 64 nb ∧ _ = BitVec.ofNat 64 ib at canonB
  have compare : (BitVec.ofNat 64 na).ult (BitVec.ofNat 64 nb) = decide (na < nb) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64]
  have selected : softDivFiniteWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) =
      softDivFiniteDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
        (BitVec.ofNat 64 (zuBits f64 b)) k := by
    unfold softDivFiniteWord
    rw [canonA.1, canonB.1, compare]
    by_cases small : na < nb <;> simp [small, k, softDivGuardCount]
  have ae := ha.1
  have be := hb.1
  change a.bexp ≤ 2047 at ae
  change b.bexp ≤ 2047 at be
  have aip : 1 ≤ max a.bexp 1 := Nat.le_max_right _ _
  have bip : 1 ≤ max b.bexp 1 := Nat.le_max_right _ _
  have indexA : 13 ≤ ia ∧ ia ≤ 2111 := by dsimp only [ia]; omega
  have indexB : 13 ≤ ib ∧ ib ≤ 2111 := by dsimp only [ib]; omega
  have kp : k ≤ 56 := by rcases count with rfl | rfl <;> decide
  have firstSub : ib ≤ ia + 2278 := by omega
  have secondSub : k ≤ ia + 2278 - ib := by omega
  have tb : total < 4400 := by
    have kl : 55 ≤ k := by rcases count with rfl | rfl <;> decide
    dsimp only [total]
    omega
  have totalWord : BitVec.ofNat 64 ia + 2278 - BitVec.ofNat 64 ib - BitVec.ofNat 64 k =
      BitVec.ofNat 64 total := by
    rw [show (2278 : Runner.W) = BitVec.ofNat 64 2278 from rfl,
      ← BitVec.ofNat_add,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) firstSub,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) secondSub]
  have guard := softDivGuard_bounds na nb al ah bl bh
  change 2 ^ 55 * nb ≤ n ∧ n < 2 ^ 56 * nb ∧ n < 2 ^ 128 at guard
  have mb := softDivJam_bounds n nb (by omega) guard.2.2 guard.1 guard.2.1
  have scale : (total : Int) - 2278 =
      ((max a.bexp 1 : Nat) : Int) - max b.bexp 1 - ca + cb - k := by
    dsimp only [total, ia, ib]
    omega
  rw [selected]
  unfold softDivFiniteDirectionalWord
  rw [softMulSignWord_canonical a b ha hb, canonA.1, canonB.1, canonA.2, canonB.2, totalWord]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64]
  rw [softMulRoundWord_model (a.sign != b.sign) total m tb mb.1 mb.2, scale]
  have source := softDivCore_finite a b ha hb special
  exact congrArg (fun g : GFloat => BitVec.ofNat 64 (zuBits f64 g)) source.symm

/-- Integer preconditions for the emitted finite continuation are derived
    from source classification, never assumed from an expected result. -/
theorem softDivFiniteL_model [Kern] {D : Deklaration} {L : Lay D}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (special : softDivSpecial a b = none)
    (hl : WordCode (L := L) ρ W left (BitVec.ofNat 64 (zuBits f64 a)))
    (hr : WordCode (L := L) ρ W right (BitVec.ofNat 64 (zuBits f64 b))) :
    WordCode (L := L) ρ W (fun d => softDivFiniteL d left right)
      (softDivFiniteWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b))) := by
  obtain ⟨fa, fb⟩ := softDivSpecial_none a b special
  obtain ⟨ap, ac, al, ah⟩ := softDiv_operand_bounds a ha fa
  obtain ⟨bp, bc, bl, bh⟩ := softDiv_operand_bounds b hb fb
  apply softDivFiniteL_word hl hr
  · rw [(softMulNormalizeWord_model b hb bp).1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : softSig b.bexp b.frac * 2 ^ softMulNormalizeCount (softSig b.bexp b.frac) < 2 ^ 64)]
    omega
  · rw [(softMulNormalizeWord_model a ha ap).1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : softSig a.bexp a.frac * 2 ^ softMulNormalizeCount (softSig a.bexp a.frac) < 2 ^ 64)]
    exact ah

#print axioms softDivFiniteWord_model
#print axioms softDivFiniteL_model
end Gabbro.Stage0.Senke
