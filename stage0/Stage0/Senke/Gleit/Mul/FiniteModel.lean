/- Identify the actual finite multiplication routine with the source product. -/
module
public import Stage0.Senke.Gleit.Mul.Routine
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Dispatch has removed both zero and nonfinite inputs before normalization. -/
theorem softMulSig_positive (a : GFloat)
    (finite : klasse f64 a = .normal ∨ klasse f64 a = .subnormal) :
    0 < softSig a.bexp a.frac := by
  unfold softSig
  split
  · next zero =>
    have nonzero : a.frac ≠ 0 := by
      intro frac
      rcases finite with finite | finite <;>
        simp [klasse, zero, frac, show f64.bexpMax = 2047 from rfl] at finite
    omega
  · omega

/-- The word xor is the kernel product sign on the canonical encodings. -/
theorem softMulSignWord_canonical (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    unpackSignWord (BitVec.ofNat 64 (zuBits f64 a)) ^^^
      unpackSignWord (BitVec.ofNat 64 (zuBits f64 b)) = Runner.IR.bool (a.sign != b.sign) := by
  rw [(routineUnpack_canonical a ha).1, (routineUnpack_canonical b hb).1]
  cases a.sign <;> cases b.sign <;> rfl

/-- Both possible product leading positions use the same exact-rounding
    argument. The shift bounds refer to the actual normalized word product. -/
theorem softMulFiniteDirectionalWord_model (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (special : softMulSpecial a b = none)
    (k : Nat) (count : k = 49 ∨ k = 50)
    (low : 2 ^ (k + 55) ≤
      (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 a))).toNat *
      (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 b))).toNat)
    (high : (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 a))).toNat *
      (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 b))).toNat < 2 ^ (k + 56)) :
    softMulFiniteDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) k = BitVec.ofNat 64 (zuBits f64 (softMulCore a b)) := by
  obtain ⟨fa, fb⟩ := softMulSpecial_none a b special
  have ap := softMulSig_positive a fa
  have bp := softMulSig_positive b fb
  let sa := softSig a.bexp a.frac
  let sb := softSig b.bexp b.frac
  let ca := softMulNormalizeCount sa
  let cb := softMulNormalizeCount sb
  let na := sa * 2 ^ ca
  let nb := sb * 2 ^ cb
  let ia := max a.bexp 1 + 64 - ca
  let ib := max b.bexp 1 + 64 - cb
  let total := ia + ib + k
  have sigBound (g : GFloat) (hg : wf f64 g) : softSig g.bexp g.frac < 2 ^ 53 := by
    have fraction := hg.2
    change g.frac < 2 ^ 52 at fraction
    unfold softSig
    split <;> omega
  have ab := softMulNormalize_bounds sa ap (sigBound a ha)
  have bb := softMulNormalize_bounds sb bp (sigBound b hb)
  have na64 : na < 2 ^ 64 := by have := ab.2.2.2.2; omega
  have nb64 : nb < 2 ^ 64 := by have := bb.2.2.2.2; omega
  have canonA := softMulNormalizeWord_model a ha ap
  have canonB := softMulNormalizeWord_model b hb bp
  change _ = BitVec.ofNat 64 na ∧ _ = BitVec.ofNat 64 ia at canonA
  change _ = BitVec.ofNat 64 nb ∧ _ = BitVec.ofNat 64 ib at canonB
  rw [canonA.1, canonB.1] at low high
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64] at low high
  have totalBound : total < 4400 := by
    have ae := ha.1
    have be := hb.1
    change a.bexp ≤ 2047 at ae
    change b.bexp ≤ 2047 at be
    dsimp only [total, ia, ib]
    rcases count with rfl | rfl <;> omega
  let m := softShiftJamNat (na * nb) k
  have mb := softMulJam_bounds (na * nb) k count low high
  have pLow : 2 ^ (k + 55) ≤ (BitVec.ofNat 64 na).toNat * (BitVec.ofNat 64 nb).toNat := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64] using low
  have pHigh : (BitVec.ofNat 64 na).toNat * (BitVec.ofNat 64 nb).toNat < 2 ^ (k + 56) := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64] using high
  have compressed := softMulCompressWord_model (BitVec.ofNat 64 na) (BitVec.ofNat 64 nb) k count pLow pHigh
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt na64, Nat.mod_eq_of_lt nb64] at compressed
  unfold softMulFiniteDirectionalWord
  rw [softMulSignWord_canonical a b ha hb, canonA.1, canonB.1, canonA.2, canonB.2,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add, compressed,
    softMulRoundWord_model (a.sign != b.sign) total m totalBound mb.1 mb.2,
    softMul_product a b special]
  apply congrArg (fun g : GFloat => BitVec.ofNat 64 (zuBits f64 g))
  have interval := softMulRound_interval (a.sign != b.sign) m (na * nb) k
    ((total : Int) - 2278) mb.1 mb.2 (by
      rcases softShiftJamNat_interval (na * nb) k with exactValue | jam
      · exact Or.inl exactValue.2
      · exact Or.inr jam)
  rw [← interval]
  have scale : (total : Int) - 2278 - (k : Int) =
      softMulExponent a b - (ca : Int) - (cb : Int) := by
    have cap := ab.2.2.1
    have cbp := bb.2.2.1
    have ae : 1 ≤ max a.bexp 1 := Nat.le_max_right _ _
    have be : 1 ≤ max b.bexp 1 := Nat.le_max_right _ _
    dsimp only [total, ia, ib, softMulExponent]
    omega
  rw [scale]
  exact softMulNormalize_round (a.sign != b.sign) sa sb ca cb (softMulExponent a b) ap bp

/-- The high product limb chooses exactly the two source bounds needed by
    the common directional theorem. This covers products of subnormals too. -/
theorem softMulFiniteWord_model (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (special : softMulSpecial a b = none) :
    softMulFiniteWord (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (softMulCore a b)) := by
  obtain ⟨fa, fb⟩ := softMulSpecial_none a b special
  have normBound (g : GFloat) (hg : wf f64 g)
      (fg : klasse f64 g = .normal ∨ klasse f64 g = .subnormal) :
      2 ^ 52 ≤ (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 g))).toNat ∧
        (softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 g))).toNat < 2 ^ 53 := by
    have positive := softMulSig_positive g fg
    have sigBound : softSig g.bexp g.frac < 2 ^ 53 := by
      have fraction := hg.2
      change g.frac < 2 ^ 52 at fraction
      unfold softSig
      split <;> omega
    have bounds := softMulNormalize_bounds _ positive sigBound
    rw [(softMulNormalizeWord_model g hg positive).1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2.2; omega)]
    exact bounds.2.2.2
  have ab := normBound a ha fa
  have bb := normBound b hb fb
  have lower := Nat.mul_le_mul ab.1 bb.1
  have upper := Nat.mul_lt_mul'' ab.2 bb.2
  let aw := softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 a))
  let bw := softMulNormalizeWord (BitVec.ofNat 64 (zuBits f64 b))
  have high := mulHiW_toNat aw bw
  have compare : (mulHiW aw bw).ult (BitVec.ofNat 64 (2 ^ 41)) =
      decide (aw.toNat * bw.toNat < 2 ^ 105) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 2 ^ 41 < 2 ^ 64), high]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  unfold softMulFiniteWord
  rw [compare]
  by_cases small : aw.toNat * bw.toNat < 2 ^ 105
  · simp only [small, decide_true, ite_true]
    exact softMulFiniteDirectionalWord_model a b ha hb special 49 (Or.inl rfl) lower small
  · simp only [small, decide_false, Bool.false_eq_true, ite_false]
    exact softMulFiniteDirectionalWord_model a b ha hb special 50 (Or.inr rfl) (by omega) upper

#print axioms softMulFiniteDirectionalWord_model
#print axioms softMulFiniteWord_model
end Gabbro.Stage0.Senke
