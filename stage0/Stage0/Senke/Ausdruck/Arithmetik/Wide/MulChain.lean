/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/MulChain.lean
  Subject:   One multiplier limb times a run of multiplicand limbs, accumulated with a carry.

  `mulRow n X Y R c t` adds `x * (y_0 + y_1 B + ...)` into the `n` digits from `R`, where `x` is the
  word in slot `X`, with one carry slot `c`. `mulChain_run` expresses the digits and the carry by the
  same `sumDig`/`carryAt` chain as addition, with the multiplicand digits scaled by `x`.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.MulBlock
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

@[simp] theorem mulRow_length (n X Y R c t : Nat) : (mulRow n X Y R c t).length = 31 * n := by
  induction n generalizing Y R with
  | zero => rfl
  | succ n ih => simp only [mulRow, List.length_append, mulLimbC_length, ih]; omega

/-- The multiplicand digits scaled by the multiplier digit. -/
def ymd (s : Nat → Runner.W) (X Y : Nat) : Nat → Nat := fun i => (s X).toNat * (s (Y + i)).toNat

theorem mulChain_run (n : Nat) : ∀ (X Y R c t : Nat) (s : Nat → Runner.W),
    X < Y → Y + n ≤ R → R + n ≤ c → c < t →
    (∀ j, j < n → aluRun (mulRow n X Y R c t) s (R + j) =
      BitVec.ofNat 64 (sumDig (xd s R) (ymd s X Y) (s c).toNat j)) ∧
    (aluRun (mulRow n X Y R c t) s c).toNat = carryAt (xd s R) (ymd s X Y) (s c).toNat n ∧
    (∀ j, (j < R ∨ R + n ≤ j) → j ≠ c → (j < t ∨ t + 15 < j) →
      aluRun (mulRow n X Y R c t) s j = s j) := by
  induction n with
  | zero =>
    intro X Y R c t s _ _ _ _
    exact ⟨fun j hj => absurd hj (by omega), rfl, fun j _ _ _ => rfl⟩
  | succ n ih =>
    intro X Y R c t s h1 h2 h3 h4
    obtain ⟨b1, b2, bf⟩ := mulLimb_value s X Y R c t (by omega) (by omega) (by omega) (by omega) (by omega)
    set s1 := aluRun (mulLimbC X Y R c t) s with hs1
    have hs : aluRun (mulRow (n + 1) X Y R c t) s = aluRun (mulRow n X (Y + 1) (R + 1) c t) s1 := by
      simp only [mulRow, aluRun_append, hs1]
    have spec := mulStepW_spec (s R) (s X) (s Y) (s c)
    have xa : xd s R 0 = (s R).toNat := by simp [xd]
    have ya : ymd s X Y 0 = (s X).toNat * (s Y).toNat := by simp [ymd]
    have carry1 : (s1 c).toNat = carryAt (xd s R) (ymd s X Y) (s c).toNat 1 := by
      rw [b2, spec.2, carryAt_succ, carryAt_zero, xa, ya]
    obtain ⟨i1, i2, i3⟩ := ih X (Y + 1) (R + 1) c t s1 (by omega) (by omega) (by omega) h4
    have fx : ∀ i, i < n → xd s1 (R + 1) i = xd s R (i + 1) := by
      intro i hi
      simp only [xd]
      rw [bf (R + 1 + i) (by omega) (by omega) (by omega), show R + (i + 1) = R + 1 + i by omega]
    have fy : ∀ i, i < n → ymd s1 X (Y + 1) i = ymd s X Y (i + 1) := by
      intro i hi
      simp only [ymd]
      rw [bf X (by omega) (by omega) (by omega), bf (Y + 1 + i) (by omega) (by omega) (by omega),
        show Y + (i + 1) = Y + 1 + i by omega]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hs]
      cases j with
      | zero =>
        show aluRun (mulRow n X (Y + 1) (R + 1) c t) s1 R = _
        rw [i3 R (by omega) (by omega) (by omega), b1]
        apply BitVec.eq_of_toNat_eq
        rw [spec.1, BitVec.toNat_ofNat]
        simp only [sumDig, carryAt_zero, xd, ymd, Nat.add_zero]
        rw [Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
      | succ j =>
        rw [show R + (j + 1) = R + 1 + j by omega, i1 j (by omega), ← sumDig_shift, ← carry1]
        congr 1
        apply sumDig_congr
        · intro i hi; exact fx i (by omega)
        · intro i hi; exact fy i (by omega)
    · rw [hs, i2, ← carryAt_shift, ← carry1]
      apply carryAt_congr
      · intro i hi; exact fx i hi
      · intro i hi; exact fy i hi
    · intro j hj hjc hjt
      rw [hs, i3 j (by omega) hjc hjt, bf j (by omega) hjc hjt]

end Gabbro.Stage0.Senke
