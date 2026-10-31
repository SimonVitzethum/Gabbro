/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/AddChain.lean
  Subject:   Multiword addition and subtraction as one carry chain over frame slots.

  Layout, for `k` limbs: the first operand (and the result) in `a .. a+k-1`, the second operand in
  `a+k .. a+2k-1`, the mask in `a+2k`, the carry in `a+2k+1` and five scratch slots from `a+2k+2`.
  Every limb computes `A := A + (B xor mask) + carry`. Mask 0 and carry 0 add; mask all ones and
  carry 1 subtract (`x + ~y + 1`), both modulo `2^(64k)`.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Limbs

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Instructions over natural slot numbers. -/
abbrev cn (o a b c : Nat) : II := ci o a b c

/-- One limb: `tb := B ^ m`, `A := A + tb + c`, the new carry from both partial additions. -/
def addLimbC (A B m c t : Nat) : List II :=
  [cn 10 t B m, cn 3 (t + 1) A t, cn 27 (t + 2) (t + 1) A, cn 3 (t + 3) (t + 1) c,
   cn 27 (t + 4) (t + 3) (t + 1), cn 2 A (t + 3) 0, cn 9 c (t + 2) (t + 4)]

def addChain : Nat → Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _, _ => []
  | n + 1, a, b, m, c, t => addLimbC a b m c t ++ addChain n (a + 1) (b + 1) m c t

/-- Add (`mask = 0`, `carry = 0`) or subtract (`mask = -1`, `carry = 1`). -/
def wideAddC (k a : Nat) (mask carry : Int) : List II :=
  [ci 1 (a + 2 * k : Nat) mask 0, ci 1 (a + 2 * k + 1 : Nat) carry 0] ++
    addChain k a (a + k) (a + 2 * k) (a + 2 * k + 1) (a + 2 * k + 2)

theorem addLimbC_length (A B m c t : Nat) : (addLimbC A B m c t).length = 7 := rfl

@[simp] theorem addChain_length (n a b m c t : Nat) : (addChain n a b m c t).length = 7 * n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [addChain, List.length_append, addLimbC_length, ih]; omega

theorem wideAddC_length (k a : Nat) (mask carry : Int) : (wideAddC k a mask carry).length = 7 * k + 2 := by
  simp only [wideAddC, List.length_append, addChain_length, List.length_cons, List.length_nil]; omega

/-! ## The word facts -/

theorem carry_word (a t c : Runner.W) (hc : c.toNat ≤ 1) :
    (Runner.IR.bool ((a + t).ult a) ||| Runner.IR.bool (((a + t) + c).ult (a + t))).toNat =
      (a.toNat + t.toNat + c.toNat) / 2 ^ 64 := by
  have ha := a.isLt
  have ht := t.isLt
  have hcc := c.isLt
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  have key : ∀ p q : Bool, (Runner.IR.bool p ||| Runner.IR.bool q).toNat = if p = true ∨ q = true then 1 else 0 := by
    intro p q; cases p <;> cases q <;> rfl
  rw [key]
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  split <;> omega

theorem sum_word (a t c : Runner.W) :
    (a + t) + c = BitVec.ofNat 64 ((a.toNat + t.toNat + c.toNat) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## One limb -/

/-- The slots one limb block touches, and what they then hold. -/
theorem addLimb_run (s : Nat → Runner.W) (A B m c t : Nat)
    (hAB : A ≠ B) (hAm : A ≠ m) (hAc : A ≠ c) (hBm : B ≠ m) (hBc : B ≠ c) (hmc : m ≠ c)
    (hA : A < t ∨ t + 4 < A) (hB : B < t ∨ t + 4 < B) (hm : m < t ∨ t + 4 < m)
    (hc : c < t ∨ t + 4 < c) :
    aluRun (addLimbC A B m c t) s A = (s A + (s B ^^^ s m)) + s c ∧
    aluRun (addLimbC A B m c t) s c =
      Runner.IR.bool ((s A + (s B ^^^ s m)).ult (s A)) |||
        Runner.IR.bool (((s A + (s B ^^^ s m)) + s c).ult (s A + (s B ^^^ s m))) ∧
    ∀ j, j ≠ A → j ≠ c → (j < t ∨ t + 4 < j) → aluRun (addLimbC A B m c t) s j = s j := by
  simp only [addLimbC, aluRun_cons, aluRun_nil, aluStep, aluVal, aluFn, cn, ci, Int.toNat_natCast,
    ite_true, ite_false, Nat.reduceEqDiff, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, ne_eq,
    Nat.succ_ne_self, not_false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) only [slotUpd_same, slotUpd_other]
  · simp (disch := omega) only [slotUpd_same, slotUpd_other]
  · intro j h1 h2 h3
    simp (disch := omega) only [slotUpd_same, slotUpd_other]

/-! ## The chain -/

/-- The digits of the first operand, and of the second operand after the mask. -/
def xd (s : Nat → Runner.W) (a : Nat) : Nat → Nat := fun i => (s (a + i)).toNat
def yd (s : Nat → Runner.W) (b m : Nat) : Nat → Nat := fun i => (s (b + i) ^^^ s m).toNat

theorem xd_lt (s : Nat → Runner.W) (a j : Nat) : xd s a j < 2 ^ 64 := (s (a + j)).isLt
theorem yd_lt (s : Nat → Runner.W) (b m j : Nat) : yd s b m j < 2 ^ 64 := (s (b + j) ^^^ s m).isLt

theorem addChain_run (n : Nat) : ∀ (a b m c t : Nat) (s : Nat → Runner.W),
    a + n ≤ b → b + n ≤ m → m < c → c < t → (s c).toNat ≤ 1 →
    (∀ j, j < n → aluRun (addChain n a b m c t) s (a + j) =
      BitVec.ofNat 64 (sumDig (xd s a) (yd s b m) (s c).toNat j)) ∧
    (aluRun (addChain n a b m c t) s c).toNat = carryAt (xd s a) (yd s b m) (s c).toNat n ∧
    aluRun (addChain n a b m c t) s m = s m ∧
    (∀ j, (j < a ∨ a + n ≤ j) → j ≠ c → (j < t ∨ t + 4 < j) →
      aluRun (addChain n a b m c t) s j = s j) := by
  induction n with
  | zero =>
    intro a b m c t s _ _ _ _ _
    exact ⟨fun j hj => absurd hj (by omega), rfl, rfl, fun j _ _ _ => rfl⟩
  | succ n ih =>
    intro a b m c t s h1 h2 h3 h4 hc
    obtain ⟨hA, hC, hF⟩ := addLimb_run s a b m c t (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    set s1 := aluRun (addLimbC a b m c t) s with hs1
    have hs : aluRun (addChain (n + 1) a b m c t) s = aluRun (addChain n (a + 1) (b + 1) m c t) s1 := by
      simp only [addChain, aluRun_append, hs1]
    have ya : yd s b m 0 = (s b ^^^ s m).toNat := by simp [yd]
    have xa : xd s a 0 = (s a).toNat := by simp [xd]
    have carry1 : (s1 c).toNat = carryAt (xd s a) (yd s b m) (s c).toNat 1 := by
      rw [hC, carry_word _ _ _ hc, carryAt_succ, carryAt_zero, xa, ya]
    have bound1 : (s1 c).toNat ≤ 1 := by
      rw [carry1]
      exact carryAt_le (xd_lt s a) (yd_lt s b m) hc 1
    obtain ⟨i1, i2, i3, i4⟩ := ih (a + 1) (b + 1) m c t s1 (by omega) (by omega) h3 h4 bound1
    have fx : ∀ i, i < n → xd s1 (a + 1) i = xd s a (i + 1) := by
      intro i hi
      simp only [xd]
      rw [hF (a + 1 + i) (by omega) (by omega) (by omega), show a + (i + 1) = a + 1 + i by omega]
    have fy : ∀ i, i < n → yd s1 (b + 1) m i = yd s b m (i + 1) := by
      intro i hi
      simp only [yd]
      have e1 := hF (b + 1 + i) (by omega) (by omega) (by omega)
      have e2 := hF m (by omega) (by omega) (by omega)
      rw [e1, e2, show b + (i + 1) = b + 1 + i by omega]
    have cc : (s1 c).toNat = carryAt (xd s a) (yd s b m) (s c).toNat 1 := carry1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hs]
      cases j with
      | zero =>
        show aluRun (addChain n (a + 1) (b + 1) m c t) s1 a = _
        rw [i4 a (by omega) (by omega) (by omega), hA, sum_word]
        simp only [sumDig, carryAt_zero, xd, yd, Nat.add_zero]
      | succ j =>
        rw [show a + (j + 1) = a + 1 + j by omega, i1 j (by omega), ← sumDig_shift, cc]
        congr 1
        apply sumDig_congr
        · intro i hi; exact fx i (by omega)
        · intro i hi; exact fy i (by omega)
    · rw [hs, i2, ← carryAt_shift, ← cc]
      apply carryAt_congr
      · intro i hi; exact fx i hi
      · intro i hi; exact fy i hi
    · rw [hs, i3, hF m (by omega) (by omega) (by omega)]
    · intro j hj hjc hjt
      rw [hs, i4 j (by omega) hjc hjt, hF j (by omega) hjc hjt]

end Gabbro.Stage0.Senke
