/- Reuse lossless significand normalization for the finite division path. -/
module
public import Stage0.Senke.Gleit.Div.Replay
public import Stage0.Senke.Gleit.Mul.Correct
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- The shared normalization maps every nonzero finite operand, including
    the smallest subnormal, into the same 53-bit significand interval. -/
theorem softDiv_operand_bounds (a : GFloat) (ha : wf f64 a)
    (finite : klasse f64 a = .normal ∨ klasse f64 a = .subnormal) :
    let sig := softSig a.bexp a.frac
    let count := softMulNormalizeCount sig
    0 < sig ∧ count ≤ 52 ∧ 2 ^ 52 ≤ sig * 2 ^ count ∧ sig * 2 ^ count < 2 ^ 53 := by
  dsimp only
  have positive := softMulSig_positive a finite
  have bound : softSig a.bexp a.frac < 2 ^ 53 := by
    have fraction := ha.2
    change a.frac < 2 ^ 52 at fraction
    unfold softSig
    split <;> omega
  have bounds := softMulNormalize_bounds _ positive bound
  exact ⟨positive, bounds.2.2.1, bounds.2.2.2⟩

/-- Unfold the kernel quotient into a signed Nat ratio, retaining the
    exact exponent alignment on both sides of the denominator. -/
theorem softDivFraction_round (a b : GFloat)
    (ap : 0 < softSig a.bexp a.frac) (bp : 0 < softSig b.bexp b.frac) :
    let ea : Int := ((max a.bexp 1 : Nat) : Int) - 1075
    let eb : Int := ((max b.bexp 1 : Nat) : Int) - 1075
    let t := (ea - min ea eb).toNat
    let j := (eb - min ea eb).toNat
    rundeBruch f64 (softDivFraction a b) =
      rundeBruchBei f64 (a.sign != b.sign)
        (softSig a.bexp a.frac * 2 ^ t) (softSig b.bexp b.frac * 2 ^ j) := by
  dsimp only
  let ea : Int := ((max a.bexp 1 : Nat) : Int) - 1075
  let eb : Int := ((max b.bexp 1 : Nat) : Int) - 1075
  let n := softSig a.bexp a.frac * 2 ^ (ea - min ea eb).toNat
  let d := softSig b.bexp b.frac * 2 ^ (eb - min ea eb).toNat
  have signA : decide ((if a.sign then -(softSig a.bexp a.frac : Int)
      else softSig a.bexp a.frac) < 0) = a.sign := by
    cases a.sign <;> simp [ap]
  have signB : decide ((if b.sign then -(softSig b.bexp b.frac : Int)
      else softSig b.bexp b.frac) < 0) = b.sign := by
    cases b.sign <;> simp [bp]
  have magA : (if a.sign then -(softSig a.bexp a.frac : Int)
      else softSig a.bexp a.frac).natAbs = softSig a.bexp a.frac := by cases a.sign <;> simp
  have magB : (if b.sign then -(softSig b.bexp b.frac : Int)
      else softSig b.bexp b.frac).natAbs = softSig b.bexp b.frac := by cases b.sign <;> simp
  have fraction : softDivFraction a b =
      ⟨if a.sign != b.sign then -(n : Int) else n, d⟩ := by
    unfold softDivFraction divBruch
    dsimp only
    rw [signA, signB, magA, magB] <;> rfl
  have positive : 0 < n :=
    Nat.mul_pos ap (Nat.two_pow_pos _)
  have sign : decide ((if a.sign != b.sign then -(n : Int) else n) < 0) =
      (a.sign != b.sign) := by
    cases (a.sign != b.sign) <;> simp [positive]
  have magnitude : (if a.sign != b.sign then -(n : Int) else n).natAbs = n := by
    cases (a.sign != b.sign) <;> simp
  rw [fraction]
  change rundeBruch f64 ⟨if a.sign != b.sign then -(n : Int) else n, d⟩ =
    rundeBruchBei f64 (a.sign != b.sign) n d
  unfold rundeBruch
  dsimp only
  rw [sign, magnitude]

/-- Source quotient rounding equals rounding its 56-bit guard/sticky word.
    No source significand, remainder or subnormal operand is discarded early. -/
theorem softDivCore_finite (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (special : softDivSpecial a b = none) :
    let sa := softSig a.bexp a.frac
    let sb := softSig b.bexp b.frac
    let ca := softMulNormalizeCount sa
    let cb := softMulNormalizeCount sb
    let k := softDivGuardCount (sa * 2 ^ ca) (sb * 2 ^ cb)
    let m := softDivJam ((sa * 2 ^ ca) * 2 ^ k) (sb * 2 ^ cb)
    let e : Int := ((max a.bexp 1 : Nat) : Int) - max b.bexp 1 - ca + cb - k
    softDivCore a b = rundeExakt f64 ⟨if a.sign != b.sign then -(m : Int) else m, e⟩ := by
  dsimp only
  obtain ⟨fa, fb⟩ := softDivSpecial_none a b special
  obtain ⟨ap, ac, al, ah⟩ := softDiv_operand_bounds a ha fa
  obtain ⟨bp, bc, bl, bh⟩ := softDiv_operand_bounds b hb fb
  let ea : Int := ((max a.bexp 1 : Nat) : Int) - 1075
  let eb : Int := ((max b.bexp 1 : Nat) : Int) - 1075
  let t := (ea - min ea eb).toNat
  let j := (eb - min ea eb).toNat
  have scale : (t : Int) - (j : Int) = ((max a.bexp 1 : Nat) : Int) - max b.bexp 1 := by
    have left := Int.min_le_left ea eb
    have right := Int.min_le_right ea eb
    dsimp only [t, j, ea, eb] at *
    omega
  rw [softDivCore, special, softDivFraction_round a b ap bp]
  have result := softDiv_replay (a.sign != b.sign) (softSig a.bexp a.frac)
    (softSig b.bexp b.frac) (softMulNormalizeCount _) (softMulNormalizeCount _) t j
    ap bp al ah bl bh
  dsimp only at result
  rw [scale] at result
  exact result

/-- The least subnormal and an ordinary normal share the normalization
    theorem despite using opposite ends of its permitted shift range. -/
theorem softDiv_operand_bounds_zeuge :
    softMulNormalizeCount (softSig 0 1) = 52 ∧
    softMulNormalizeCount (softSig 1023 0) = 0 := by
  decide +kernel

#print axioms softDiv_operand_bounds
#print axioms softDivFraction_round
#print axioms softDivCore_finite
#print axioms softDiv_operand_bounds_zeuge
end Gabbro.Stage0.Senke
