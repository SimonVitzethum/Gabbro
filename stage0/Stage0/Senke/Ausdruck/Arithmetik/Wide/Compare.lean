/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Compare.lean
  Subject:   Exact multiword comparison from the subtraction chain.

  `x < y` is the sign bit of `x - y` over `n + 1` limbs, provided the difference lies in the signed
  range of those limbs; operands extended by one limb always satisfy it. Equality is the OR of all
  limbs of the difference being zero, provided `|x - y| < 2^(64 (n+1))`. The result is a Boolean word
  in the first operand's slot `a`.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Add
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Subtraction leaves the canonical limbs of `x - y`. -/
theorem wideSub_value (k a : Nat) (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < k → s (a + j) = lmb x j) (hy : ∀ j, j < k → s (a + k + j) = lmb y j) :
    (∀ j, j < k → aluRun (wideAddC k a (-1) 1) s (a + j) = lmb (x - y) j) ∧
    (∀ j, (j < a ∨ a + 2 * k + 7 ≤ j ∨ (a + k ≤ j ∧ j < a + 2 * k)) →
      aluRun (wideAddC k a (-1) 1) s j = s j) := by
  obtain ⟨v1, v2⟩ := wideAddC_value k a (-1) 1 (Or.inr rfl) s x y hx hy
  exact ⟨fun j hj => by
    rw [v1 j hj]
    exact lmb_of_dval (chainDig_lt x y (-1) 1) (x - y) k (chainDig_sub x y k) j hj, v2⟩

theorem wideAdd_value (k a : Nat) (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < k → s (a + j) = lmb x j) (hy : ∀ j, j < k → s (a + k + j) = lmb y j) :
    (∀ j, j < k → aluRun (wideAddC k a 0 0) s (a + j) = lmb (x + y) j) ∧
    (∀ j, (j < a ∨ a + 2 * k + 7 ≤ j ∨ (a + k ≤ j ∧ j < a + 2 * k)) →
      aluRun (wideAddC k a 0 0) s j = s j) := by
  obtain ⟨v1, v2⟩ := wideAddC_value k a 0 0 (Or.inl rfl) s x y hx hy
  exact ⟨fun j hj => by
    rw [v1 j hj]
    exact lmb_of_dval (chainDig_lt x y 0 0) (x + y) k (chainDig_add x y k) j hj, v2⟩

/-- The top bit of the top limb is the sign, inside the signed range. -/
theorem sign_limb (n : Nat) (v : Int) (h1 : -(2 ^ 63 * 2 ^ (64 * n)) ≤ v) (h2 : v < 2 ^ 63 * 2 ^ (64 * n)) :
    lmb v n >>> ((BitVec.ofInt 64 63).toNat % 64) = Runner.IR.bool (decide (v < 0)) := by
  have hP : (0 : Int) < 2 ^ (64 * n) := by positivity
  have q1 : -2 ^ 63 ≤ v / 2 ^ (64 * n) := Int.le_ediv_of_mul_le hP (by omega)
  have q2 : v / 2 ^ (64 * n) < 2 ^ 63 := Int.ediv_lt_of_lt_mul hP (by omega)
  have q3 : v / 2 ^ (64 * n) < 0 ↔ v < 0 := by
    rw [Int.ediv_lt_iff_lt_mul hP]; omega
  apply BitVec.eq_of_toNat_eq
  have e63 : (BitVec.ofInt 64 63).toNat % 64 = 63 := by simp
  rw [e63, BitVec.toNat_ushiftRight, lmb_toNat, Nat.shiftRight_eq_div_pow]
  by_cases hv : v < 0
  · have hq : v / 2 ^ (64 * n) < 0 := q3.mpr hv
    have hb : (Runner.IR.bool (decide (v < 0))).toNat = 1 := by simp [Runner.IR.bool, hv]
    rw [hb]
    omega
  · have hq : ¬ v / 2 ^ (64 * n) < 0 := fun h => hv (q3.mp h)
    have hb : (Runner.IR.bool (decide (v < 0))).toNat = 0 := by simp [Runner.IR.bool, hv]
    rw [hb]
    omega

theorem wideLt_value (n a : Nat) (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < n + 1 → s (a + j) = lmb x j)
    (hy : ∀ j, j < n + 1 → s (a + (n + 1) + j) = lmb y j)
    (hr1 : -(2 ^ 63 * 2 ^ (64 * n)) ≤ x - y) (hr2 : x - y < 2 ^ 63 * 2 ^ (64 * n)) :
    aluRun (wideLtC n a) s a = Runner.IR.bool (decide (x < y)) := by
  obtain ⟨v1, v2⟩ := wideSub_value (n + 1) a s x y hx hy
  have top := v1 n (by omega)
  simp only [wideLtC, aluRun_append]
  generalize aluRun (wideAddC (n + 1) a (-1) 1) s = s1 at top ⊢
  simp (disch := omega) only [signTail, aluRun_cons, aluRun_nil, aluStep, aluVal, cn, ci, aluFn,
    Int.toNat_natCast, slotUpd_same, slotUpd_other, ite_true, ite_false, OfNat.ofNat_ne_one,
    Nat.reduceEqDiff, ne_eq, not_false_eq_true]
  rw [top, sign_limb n (x - y) hr1 hr2]
  congr 2
  apply propext
  omega

/-! ## Equality -/

theorem orChain_value (a : Nat) : ∀ (n j : Nat) (s : Nat → Runner.W), 1 ≤ j →
    (aluRun (orChain n a j) s a = 0 ↔ s a = 0 ∧ ∀ i, j ≤ i → i < j + n → s (a + i) = 0) ∧
    (∀ i, i ≠ a → aluRun (orChain n a j) s i = s i)
  | 0, j, s, _ => ⟨by
      simp only [orChain, aluRun_nil]
      exact ⟨fun h => ⟨h, fun i h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩, fun i _ => rfl⟩
  | n + 1, j, s, hj => by
    obtain ⟨ih1, ih2⟩ := orChain_value a n (j + 1) (slotUpd s a (s a ||| s (a + j))) (by omega)
    have step : aluRun (orChain (n + 1) a j) s = aluRun (orChain n a (j + 1)) (slotUpd s a (s a ||| s (a + j))) := by
      simp only [orChain, aluRun_cons, aluStep, aluVal, cn, ci, aluFn, Int.toNat_natCast]
      rfl
    rw [step]
    refine ⟨?_, fun i hi => (ih2 i hi).trans (slotUpd_other _ _ hi)⟩
    rw [ih1]
    have e1 : slotUpd s a (s a ||| s (a + j)) a = s a ||| s (a + j) := slotUpd_same _ _ _
    have e2 : ∀ i, 1 ≤ i → slotUpd s a (s a ||| s (a + j)) (a + i) = s (a + i) :=
      fun i hi => slotUpd_other _ _ (by omega)
    have hor : ∀ x y : Runner.W, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun x y => BitVec.or_eq_zero_iff
    rw [e1, hor]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun i hi1 hi2 => ?_⟩
      by_cases e : i = j
      · subst e; exact h2
      · have := h3 i (by omega) (by omega); rwa [e2 i (by omega)] at this
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, h3 j (Nat.le_refl _) (by omega)⟩, fun i hi1 hi2 => ?_⟩
      rw [e2 i (by omega)]
      exact h3 i (by omega) (by omega)

theorem dval_zero_seq (k : Nat) : dval (fun _ => 0) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dval_succ, ih]; simp

theorem limbs_zero_iff (n : Nat) (v : Int) (h1 : -(2 ^ (64 * (n + 1))) < v) (h2 : v < 2 ^ (64 * (n + 1))) :
    (∀ j, j < n + 1 → lmb v j = 0) ↔ v = 0 := by
  constructor
  · intro h
    have hz : dval (fun j => (lmb v j).toNat) (n + 1) = 0 := by
      rw [dval_congr (y := fun _ => 0) (fun j hj => by rw [h j hj]; rfl), dval_zero_seq]
    rw [dval_lmb] at hz
    have hM : (0 : Int) < 2 ^ (64 * (n + 1)) := by positivity
    have hmod : v % 2 ^ (64 * (n + 1)) = 0 := by
      have := Int.emod_nonneg v hM.ne'
      omega
    have e := Int.mul_ediv_add_emod v (2 ^ (64 * (n + 1)))
    rw [hmod] at e
    by_contra hne
    have hq : v / 2 ^ (64 * (n + 1)) ≠ 0 := by
      intro hq; rw [hq] at e; omega
    rcases Int.lt_or_gt_of_ne hq with hl | hg
    · have : 2 ^ (64 * (n + 1)) * (v / 2 ^ (64 * (n + 1))) ≤ 2 ^ (64 * (n + 1)) * (-1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) hM.le
      omega
    · have : 2 ^ (64 * (n + 1)) * 1 ≤ 2 ^ (64 * (n + 1)) * (v / 2 ^ (64 * (n + 1))) :=
        Int.mul_le_mul_of_nonneg_left (by omega) hM.le
      omega
  · rintro rfl j _
    simp [lmb]

theorem wideEq_value (n a : Nat) (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < n + 1 → s (a + j) = lmb x j)
    (hy : ∀ j, j < n + 1 → s (a + (n + 1) + j) = lmb y j)
    (hr1 : -(2 ^ (64 * (n + 1))) < x - y) (hr2 : x - y < 2 ^ (64 * (n + 1))) :
    aluRun (wideEqC n a) s a = Runner.IR.bool (decide (x = y)) := by
  obtain ⟨v1, v2⟩ := wideSub_value (n + 1) a s x y hx hy
  simp only [wideEqC, aluRun_append]
  generalize h1 : aluRun (wideAddC (n + 1) a (-1) 1) s = s1 at v1
  obtain ⟨o1, o2⟩ := orChain_value a n 1 s1 (Nat.le_refl _)
  generalize h2 : aluRun (orChain n a 1) s1 = s2 at o1 o2
  have key : s2 a = 0 ↔ x = y := by
    rw [o1]
    have hz := limbs_zero_iff n (x - y) hr1 hr2
    constructor
    · rintro ⟨h, hall⟩
      have : ∀ j, j < n + 1 → lmb (x - y) j = 0 := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hp
        · rw [← v1 0 (by omega)]; simpa using h
        · rw [← v1 j hj]
          simpa using hall j hp (by omega)
      have := hz.mp this
      omega
    · intro h
      have hd : x - y = 0 := by omega
      have all0 := hz.mpr hd
      have z0 := v1 0 (by omega)
      rw [Nat.add_zero, all0 0 (by omega)] at z0
      refine ⟨z0, fun i hi1 hi2 => ?_⟩
      rw [v1 i (by omega)]
      exact all0 i (by omega)
  simp (disch := omega) only [eqTail, aluRun_cons, aluRun_nil, aluStep, aluVal, cn, ci, aluFn,
    Int.toNat_natCast, slotUpd_same, slotUpd_other, ite_true, ite_false, OfNat.ofNat_ne_one,
    Nat.reduceEqDiff, ne_eq, not_false_eq_true]
  have h0 : BitVec.ofInt 64 0 = 0 := BitVec.eq_of_toNat_eq (by simp)
  rw [h0]
  congr 1
  by_cases hxy : x = y
  · simp [key.mpr hxy, hxy]
  · have : s2 a ≠ 0 := fun h => hxy (key.mp h)
    simp [hxy]
    exact this

end Gabbro.Stage0.Senke
