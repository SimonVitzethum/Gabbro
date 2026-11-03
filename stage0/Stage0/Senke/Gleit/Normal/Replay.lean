/- General dyadic rounding replay, without a bounded exact-sum numerator. -/
module
public import Stage0.Senke.Gleit.Sticky.Add
public import Stage0.Senke.Gleit.Normal.Exact
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Round a dyadic magnitude at an integer scale. Both shifts are exact;
    the denominator is mathematical and need not fit a runner word. -/
def softRoundDyadic (S : Nat) (scale : Int) : Nat :=
  rundeInt ((S * 2 ^ scale.toNat) / 2 ^ (-scale).toNat)
    ((S * 2 ^ scale.toNat) % 2 ^ (-scale).toNat) (2 ^ (-scale).toNat)

theorem softRound_power_congr (S t₁ j₁ t₂ j₂ : Nat)
    (scale : t₁ + j₂ = t₂ + j₁) :
    rundeInt ((S * 2 ^ t₁) / 2 ^ j₁) ((S * 2 ^ t₁) % 2 ^ j₁) (2 ^ j₁) =
      rundeInt ((S * 2 ^ t₂) / 2 ^ j₂) ((S * 2 ^ t₂) % 2 ^ j₂) (2 ^ j₂) := by
  -- The arithmetic transport has an unused kernel parameter, discharged without an assumption.
  letI : Runner.IR.Kern := ⟨fun _ _ _ _ => False⟩
  apply softRound_congr _ _ _ _ _ _
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.div_add_mod', Nat.div_add_mod', Nat.mul_assoc, ← Nat.pow_add,
    Nat.mul_assoc, ← Nat.pow_add, scale]

theorem softRoundDyadic_scale (S t j : Nat) (scale : Int)
    (hs : scale = (t : Int) - (j : Int)) :
    rundeInt ((S * 2 ^ t) / 2 ^ j) ((S * 2 ^ t) % 2 ^ j) (2 ^ j) =
      softRoundDyadic S scale := by
  exact softRound_power_congr _ _ _ _ _ (by omega)

/-- Arbitrarily wide exact sums and left-normalized small sums share this
    normal significand decision. Neither a 54-bit bound nor a set hidden
    bit is a premise. -/
theorem softRound_normQ_dyadic (S t j p : Nat) (E : Int)
    (position : E = (bitlen S : Int) + (t : Int) - 1 - (j : Int)) :
    normQ p E (S * 2 ^ t) (2 ^ j) = softRoundDyadic S ((p : Int) - bitlen S) := by
  unfold normQ normQD
  split
  · next up =>
    dsimp only
    rw [Nat.mul_assoc, ← Nat.pow_add]
    apply softRoundDyadic_scale
    omega
  · next down =>
    dsimp only
    rw [← Nat.pow_add]
    apply softRoundDyadic_scale
    omega

theorem softRound_subQ_dyadic (S t j : Nat) :
    subQ f64 (S * 2 ^ t) (2 ^ j) =
      softRoundDyadic S ((t : Int) - (j : Int) + 1074) := by
  change rundeInt (((S * 2 ^ t) * 2 ^ 1074) / 2 ^ j)
    (((S * 2 ^ t) * 2 ^ 1074) % 2 ^ j) (2 ^ j) = _
  rw [Nat.mul_assoc, ← Nat.pow_add]
  apply softRoundDyadic_scale
  omega

/-- Replay every kernel output branch after positioning the exponent. The
    normal and subnormal significands are computed from exact dyadic scales. -/
theorem softRound_replay_fraction (s : Bool) (S t j : Nat) (e : Int)
    (scale : e = (t : Int) - (j : Int)) :
    let E := e + (bitlen S : Int) - 1
    let normal := softRoundDyadic S (53 - (bitlen S : Int))
    let sub := softRoundDyadic S (e + 1074)
    rundeBruchKern f64 s (S * 2 ^ t) (2 ^ j) E =
      if (f64.emax : Int) < E then ⟨s, f64.bexpMax, 0⟩
      else if E < f64.emin - (f64.p : Int) then ⟨s, 0, 0⟩
      else if f64.emin ≤ E then
        if normal < 2 ^ f64.p then ⟨s, (E - f64.emin + 1).toNat, normal - 2 ^ (f64.p - 1)⟩
        else if E < (f64.emax : Int) then ⟨s, (E - f64.emin + 2).toNat, 0⟩
        else ⟨s, f64.bexpMax, 0⟩
      else if sub < 2 ^ (f64.p - 1) then ⟨s, 0, sub⟩ else ⟨s, 1, 0⟩ := by
  dsimp only
  have normal := softRound_normQ_dyadic S t j 53 (e + (bitlen S : Int) - 1) (by omega)
  simp only [show ((53 : Nat) : Int) = (53 : Int) from rfl] at normal
  have sub := softRound_subQ_dyadic S t j
  rw [← scale] at sub
  unfold rundeBruchKern
  rw [show f64.p = 53 from rfl, normal, sub]

/-- General exact replay: large alignment gaps, cancellation, subnormal
    output, and overflow all use the same kernel rounding branches. The only
    separate case is an exactly zero numerator, whose result is positive zero. -/
theorem softRound_replay_all (z : Int) (e : Int) (nonzero : z ≠ 0) :
    let S := z.natAbs
    let s := decide (z < 0)
    let E := e + (bitlen S : Int) - 1
    let normal := softRoundDyadic S (53 - (bitlen S : Int))
    let sub := softRoundDyadic S (e + 1074)
    rundeExakt f64 ⟨z, e⟩ =
      if (f64.emax : Int) < E then ⟨s, f64.bexpMax, 0⟩
      else if E < f64.emin - (f64.p : Int) then ⟨s, 0, 0⟩
      else if f64.emin ≤ E then
        if normal < 2 ^ f64.p then ⟨s, (E - f64.emin + 1).toNat, normal - 2 ^ (f64.p - 1)⟩
        else if E < (f64.emax : Int) then ⟨s, (E - f64.emin + 2).toNat, 0⟩
        else ⟨s, f64.bexpMax, 0⟩
      else if sub < 2 ^ (f64.p - 1) then ⟨s, 0, sub⟩ else ⟨s, 1, 0⟩ := by
  dsimp only
  have positive : 0 < z.natAbs := by omega
  unfold rundeExakt exaktBruch
  by_cases ep : 0 ≤ e
  · rw [if_pos ep]
    have power : (0 : Int) < (2 ^ e.toNat : Nat) := by exact_mod_cast Nat.two_pow_pos e.toNat
    have sign : (z * (2 ^ e.toNat : Nat) < 0) ↔ z < 0 := by
      constructor
      · intro h
        by_contra hz
        have := Int.mul_nonneg (show 0 ≤ z by omega) (le_of_lt power)
        omega
      · intro hz
        exact Int.mul_neg_of_neg_of_pos hz power
    have signDecision : decide (z * (2 ^ e.toNat : Nat) < 0) = decide (z < 0) := by
      simp only [sign]
    unfold rundeBruch rundeBruchBei
    dsimp only
    rw [signDecision, Int.natAbs_mul, Int.natAbs_natCast,
      if_neg (by decide : ¬ (1 : Nat) = 0),
      if_neg (ne_of_gt (Nat.mul_pos positive (Nat.two_pow_pos _)))]
    have exponent : findeExp (z.natAbs * 2 ^ e.toNat) 1 = e + (bitlen z.natAbs : Int) - 1 := by
      have position := findeExp_scaled z.natAbs e.toNat 0 positive
      simp only [Nat.pow_zero] at position
      rw [position]
      omega
    rw [exponent]
    have replay := softRound_replay_fraction (decide (z < 0)) z.natAbs e.toNat 0 e (by omega)
    simpa only [Nat.pow_zero] using replay
  · rw [if_neg ep]
    unfold rundeBruch rundeBruchBei
    dsimp only
    rw [if_neg (ne_of_gt (Nat.two_pow_pos _)), if_neg (by omega : z.natAbs ≠ 0)]
    have exponent : findeExp z.natAbs (2 ^ (-e).toNat) = e + (bitlen z.natAbs : Int) - 1 := by
      have position := findeExp_scaled z.natAbs 0 (-e).toNat positive
      simp only [Nat.pow_zero, Nat.mul_one] at position
      rw [position]
      omega
    rw [exponent]
    have replay := softRound_replay_fraction (decide (z < 0)) z.natAbs 0 (-e).toNat e (by omega)
    simpa only [Nat.pow_zero, Nat.mul_one] using replay

/-- Joint boundaries include an exact numerator wider than any machine word,
    the smallest nonzero cancellation result, subnormal output, and overflow. -/
theorem softRound_replay_all_zeuge :
    rundeExakt f64 ⟨1 + 2 ^ 1074, -1074⟩ = ⟨false, 1023, 0⟩ ∧
    rundeExakt f64 ⟨1, -52⟩ = ⟨false, 971, 0⟩ ∧
    rundeExakt f64 ⟨2, -1074⟩ = ⟨false, 0, 2⟩ ∧
    rundeExakt f64 ⟨2 ^ 54 - 2, 971⟩ = ⟨false, 2047, 0⟩ := by
  decide +kernel

#print axioms softRoundDyadic_scale
#print axioms softRound_normQ_dyadic
#print axioms softRound_subQ_dyadic
#print axioms softRound_replay_all
#print axioms softRound_replay_all_zeuge
end Gabbro.Stage0.Senke
