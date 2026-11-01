/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/MulBlock.lean
  Subject:   The emitted multiply-accumulate limb step.

  `mulLimbC X Y R c t` multiplies the words in slots `X` and `Y`, adds the product and the carry in
  slot `c` to the digit in slot `R`, and leaves the new digit in `R` and the new carry in `c`;
  `t .. t+15` are scratch. `mulLimb_run` proves its effect equals `mulStepW` on the slot words.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.MulWord
import Stage0.Senke.Ausdruck.Arithmetik.Wide.AddChain

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Low product and high word (into `t` and `t+11`), scratch `t .. t+15`. -/
def mulHiC (X Y t : Nat) : List II :=
  [cn 5 t X Y, ci 1 (t + 1 : Nat) 32 0, ci 1 (t + 2 : Nat) 1 0,
   cn 11 (t + 3) (t + 2) (t + 1), cn 4 (t + 3) (t + 3) (t + 2),
   cn 12 (t + 4) X (t + 1), cn 8 (t + 5) X (t + 3), cn 12 (t + 6) Y (t + 1), cn 8 (t + 7) Y (t + 3),
   cn 5 (t + 8) (t + 5) (t + 7), cn 5 (t + 9) (t + 4) (t + 7),
   cn 5 (t + 10) (t + 5) (t + 6), cn 5 (t + 11) (t + 4) (t + 6),
   cn 12 (t + 12) (t + 8) (t + 1), cn 8 (t + 13) (t + 9) (t + 3), cn 3 (t + 12) (t + 12) (t + 13),
   cn 8 (t + 13) (t + 10) (t + 3), cn 3 (t + 12) (t + 12) (t + 13),
   cn 12 (t + 13) (t + 12) (t + 1), cn 12 (t + 14) (t + 9) (t + 1), cn 12 (t + 15) (t + 10) (t + 1),
   cn 3 (t + 11) (t + 11) (t + 14), cn 3 (t + 11) (t + 11) (t + 15), cn 3 (t + 11) (t + 11) (t + 13)]

/-- Add the product (low word in `t`, high word in `t+11`) and the carry into the digit. -/
def mulAccC (R c t : Nat) : List II :=
  [cn 3 (t + 1) R t, cn 27 (t + 2) (t + 1) t, cn 3 (t + 3) (t + 1) c, cn 27 (t + 4) (t + 3) (t + 1),
   cn 2 R (t + 3) 0, cn 3 c (t + 11) (t + 2), cn 3 c c (t + 4)]

def mulLimbC (X Y R c t : Nat) : List II := mulHiC X Y t ++ mulAccC R c t

theorem mulHiC_length (X Y t : Nat) : (mulHiC X Y t).length = 24 := rfl
theorem mulAccC_length (R c t : Nat) : (mulAccC R c t).length = 7 := rfl
theorem mulLimbC_length (X Y R c t : Nat) : (mulLimbC X Y R c t).length = 31 := rfl

theorem ofInt_shift32 : (BitVec.ofInt 64 32).toNat % 64 = 32 := by simp
theorem one_shl_sub : (BitVec.ofInt 64 1) <<< 32 - BitVec.ofInt 64 1 = m32 := by
  apply BitVec.eq_of_toNat_eq
  simp [m32, BitVec.toNat_ofNat]

theorem mulHi_value (s : Nat → Runner.W) (X Y t : Nat)
    (hX : X < t ∨ t + 15 < X) (hY : Y < t ∨ t + 15 < Y) :
    aluRun (mulHiC X Y t) s t = s X * s Y ∧
    aluRun (mulHiC X Y t) s (t + 11) = mulHiW (s X) (s Y) ∧
    ∀ j, (j < t ∨ t + 15 < j) → aluRun (mulHiC X Y t) s j = s j := by
  obtain ⟨s1, h1⟩ : ∃ s', s' = aluStep (cn 5 (t) (X) (Y)) s := ⟨_, rfl⟩
  have o1 : ∀ j, j ≠ t → s1 j = s j := fun j hj => by rw [h1]; exact slotUpd_other _ _ hj
  have d1 : s1 (t) = aluVal (cn 5 (t) (X) (Y)) s := by rw [h1]; exact slotUpd_same _ _ _
  obtain ⟨s2, h2⟩ : ∃ s', s' = aluStep (ci 1 (t + 1 : Nat) 32 0) s1 := ⟨_, rfl⟩
  have o2 : ∀ j, j ≠ t + 1 → s2 j = s1 j := fun j hj => by rw [h2]; exact slotUpd_other _ _ hj
  have d2 : s2 (t + 1) = aluVal (ci 1 (t + 1 : Nat) 32 0) s1 := by rw [h2]; exact slotUpd_same _ _ _
  obtain ⟨s3, h3⟩ : ∃ s', s' = aluStep (ci 1 (t + 2 : Nat) 1 0) s2 := ⟨_, rfl⟩
  have o3 : ∀ j, j ≠ t + 2 → s3 j = s2 j := fun j hj => by rw [h3]; exact slotUpd_other _ _ hj
  have d3 : s3 (t + 2) = aluVal (ci 1 (t + 2 : Nat) 1 0) s2 := by rw [h3]; exact slotUpd_same _ _ _
  obtain ⟨s4, h4⟩ : ∃ s', s' = aluStep (cn 11 (t + 3) (t + 2) (t + 1)) s3 := ⟨_, rfl⟩
  have o4 : ∀ j, j ≠ t + 3 → s4 j = s3 j := fun j hj => by rw [h4]; exact slotUpd_other _ _ hj
  have d4 : s4 (t + 3) = aluVal (cn 11 (t + 3) (t + 2) (t + 1)) s3 := by rw [h4]; exact slotUpd_same _ _ _
  obtain ⟨s5, h5⟩ : ∃ s', s' = aluStep (cn 4 (t + 3) (t + 3) (t + 2)) s4 := ⟨_, rfl⟩
  have o5 : ∀ j, j ≠ t + 3 → s5 j = s4 j := fun j hj => by rw [h5]; exact slotUpd_other _ _ hj
  have d5 : s5 (t + 3) = aluVal (cn 4 (t + 3) (t + 3) (t + 2)) s4 := by rw [h5]; exact slotUpd_same _ _ _
  obtain ⟨s6, h6⟩ : ∃ s', s' = aluStep (cn 12 (t + 4) (X) (t + 1)) s5 := ⟨_, rfl⟩
  have o6 : ∀ j, j ≠ t + 4 → s6 j = s5 j := fun j hj => by rw [h6]; exact slotUpd_other _ _ hj
  have d6 : s6 (t + 4) = aluVal (cn 12 (t + 4) (X) (t + 1)) s5 := by rw [h6]; exact slotUpd_same _ _ _
  obtain ⟨s7, h7⟩ : ∃ s', s' = aluStep (cn 8 (t + 5) (X) (t + 3)) s6 := ⟨_, rfl⟩
  have o7 : ∀ j, j ≠ t + 5 → s7 j = s6 j := fun j hj => by rw [h7]; exact slotUpd_other _ _ hj
  have d7 : s7 (t + 5) = aluVal (cn 8 (t + 5) (X) (t + 3)) s6 := by rw [h7]; exact slotUpd_same _ _ _
  obtain ⟨s8, h8⟩ : ∃ s', s' = aluStep (cn 12 (t + 6) (Y) (t + 1)) s7 := ⟨_, rfl⟩
  have o8 : ∀ j, j ≠ t + 6 → s8 j = s7 j := fun j hj => by rw [h8]; exact slotUpd_other _ _ hj
  have d8 : s8 (t + 6) = aluVal (cn 12 (t + 6) (Y) (t + 1)) s7 := by rw [h8]; exact slotUpd_same _ _ _
  obtain ⟨s9, h9⟩ : ∃ s', s' = aluStep (cn 8 (t + 7) (Y) (t + 3)) s8 := ⟨_, rfl⟩
  have o9 : ∀ j, j ≠ t + 7 → s9 j = s8 j := fun j hj => by rw [h9]; exact slotUpd_other _ _ hj
  have d9 : s9 (t + 7) = aluVal (cn 8 (t + 7) (Y) (t + 3)) s8 := by rw [h9]; exact slotUpd_same _ _ _
  obtain ⟨s10, h10⟩ : ∃ s', s' = aluStep (cn 5 (t + 8) (t + 5) (t + 7)) s9 := ⟨_, rfl⟩
  have o10 : ∀ j, j ≠ t + 8 → s10 j = s9 j := fun j hj => by rw [h10]; exact slotUpd_other _ _ hj
  have d10 : s10 (t + 8) = aluVal (cn 5 (t + 8) (t + 5) (t + 7)) s9 := by rw [h10]; exact slotUpd_same _ _ _
  obtain ⟨s11, h11⟩ : ∃ s', s' = aluStep (cn 5 (t + 9) (t + 4) (t + 7)) s10 := ⟨_, rfl⟩
  have o11 : ∀ j, j ≠ t + 9 → s11 j = s10 j := fun j hj => by rw [h11]; exact slotUpd_other _ _ hj
  have d11 : s11 (t + 9) = aluVal (cn 5 (t + 9) (t + 4) (t + 7)) s10 := by rw [h11]; exact slotUpd_same _ _ _
  obtain ⟨s12, h12⟩ : ∃ s', s' = aluStep (cn 5 (t + 10) (t + 5) (t + 6)) s11 := ⟨_, rfl⟩
  have o12 : ∀ j, j ≠ t + 10 → s12 j = s11 j := fun j hj => by rw [h12]; exact slotUpd_other _ _ hj
  have d12 : s12 (t + 10) = aluVal (cn 5 (t + 10) (t + 5) (t + 6)) s11 := by rw [h12]; exact slotUpd_same _ _ _
  obtain ⟨s13, h13⟩ : ∃ s', s' = aluStep (cn 5 (t + 11) (t + 4) (t + 6)) s12 := ⟨_, rfl⟩
  have o13 : ∀ j, j ≠ t + 11 → s13 j = s12 j := fun j hj => by rw [h13]; exact slotUpd_other _ _ hj
  have d13 : s13 (t + 11) = aluVal (cn 5 (t + 11) (t + 4) (t + 6)) s12 := by rw [h13]; exact slotUpd_same _ _ _
  obtain ⟨s14, h14⟩ : ∃ s', s' = aluStep (cn 12 (t + 12) (t + 8) (t + 1)) s13 := ⟨_, rfl⟩
  have o14 : ∀ j, j ≠ t + 12 → s14 j = s13 j := fun j hj => by rw [h14]; exact slotUpd_other _ _ hj
  have d14 : s14 (t + 12) = aluVal (cn 12 (t + 12) (t + 8) (t + 1)) s13 := by rw [h14]; exact slotUpd_same _ _ _
  obtain ⟨s15, h15⟩ : ∃ s', s' = aluStep (cn 8 (t + 13) (t + 9) (t + 3)) s14 := ⟨_, rfl⟩
  have o15 : ∀ j, j ≠ t + 13 → s15 j = s14 j := fun j hj => by rw [h15]; exact slotUpd_other _ _ hj
  have d15 : s15 (t + 13) = aluVal (cn 8 (t + 13) (t + 9) (t + 3)) s14 := by rw [h15]; exact slotUpd_same _ _ _
  obtain ⟨s16, h16⟩ : ∃ s', s' = aluStep (cn 3 (t + 12) (t + 12) (t + 13)) s15 := ⟨_, rfl⟩
  have o16 : ∀ j, j ≠ t + 12 → s16 j = s15 j := fun j hj => by rw [h16]; exact slotUpd_other _ _ hj
  have d16 : s16 (t + 12) = aluVal (cn 3 (t + 12) (t + 12) (t + 13)) s15 := by rw [h16]; exact slotUpd_same _ _ _
  obtain ⟨s17, h17⟩ : ∃ s', s' = aluStep (cn 8 (t + 13) (t + 10) (t + 3)) s16 := ⟨_, rfl⟩
  have o17 : ∀ j, j ≠ t + 13 → s17 j = s16 j := fun j hj => by rw [h17]; exact slotUpd_other _ _ hj
  have d17 : s17 (t + 13) = aluVal (cn 8 (t + 13) (t + 10) (t + 3)) s16 := by rw [h17]; exact slotUpd_same _ _ _
  obtain ⟨s18, h18⟩ : ∃ s', s' = aluStep (cn 3 (t + 12) (t + 12) (t + 13)) s17 := ⟨_, rfl⟩
  have o18 : ∀ j, j ≠ t + 12 → s18 j = s17 j := fun j hj => by rw [h18]; exact slotUpd_other _ _ hj
  have d18 : s18 (t + 12) = aluVal (cn 3 (t + 12) (t + 12) (t + 13)) s17 := by rw [h18]; exact slotUpd_same _ _ _
  obtain ⟨s19, h19⟩ : ∃ s', s' = aluStep (cn 12 (t + 13) (t + 12) (t + 1)) s18 := ⟨_, rfl⟩
  have o19 : ∀ j, j ≠ t + 13 → s19 j = s18 j := fun j hj => by rw [h19]; exact slotUpd_other _ _ hj
  have d19 : s19 (t + 13) = aluVal (cn 12 (t + 13) (t + 12) (t + 1)) s18 := by rw [h19]; exact slotUpd_same _ _ _
  obtain ⟨s20, h20⟩ : ∃ s', s' = aluStep (cn 12 (t + 14) (t + 9) (t + 1)) s19 := ⟨_, rfl⟩
  have o20 : ∀ j, j ≠ t + 14 → s20 j = s19 j := fun j hj => by rw [h20]; exact slotUpd_other _ _ hj
  have d20 : s20 (t + 14) = aluVal (cn 12 (t + 14) (t + 9) (t + 1)) s19 := by rw [h20]; exact slotUpd_same _ _ _
  obtain ⟨s21, h21⟩ : ∃ s', s' = aluStep (cn 12 (t + 15) (t + 10) (t + 1)) s20 := ⟨_, rfl⟩
  have o21 : ∀ j, j ≠ t + 15 → s21 j = s20 j := fun j hj => by rw [h21]; exact slotUpd_other _ _ hj
  have d21 : s21 (t + 15) = aluVal (cn 12 (t + 15) (t + 10) (t + 1)) s20 := by rw [h21]; exact slotUpd_same _ _ _
  obtain ⟨s22, h22⟩ : ∃ s', s' = aluStep (cn 3 (t + 11) (t + 11) (t + 14)) s21 := ⟨_, rfl⟩
  have o22 : ∀ j, j ≠ t + 11 → s22 j = s21 j := fun j hj => by rw [h22]; exact slotUpd_other _ _ hj
  have d22 : s22 (t + 11) = aluVal (cn 3 (t + 11) (t + 11) (t + 14)) s21 := by rw [h22]; exact slotUpd_same _ _ _
  obtain ⟨s23, h23⟩ : ∃ s', s' = aluStep (cn 3 (t + 11) (t + 11) (t + 15)) s22 := ⟨_, rfl⟩
  have o23 : ∀ j, j ≠ t + 11 → s23 j = s22 j := fun j hj => by rw [h23]; exact slotUpd_other _ _ hj
  have d23 : s23 (t + 11) = aluVal (cn 3 (t + 11) (t + 11) (t + 15)) s22 := by rw [h23]; exact slotUpd_same _ _ _
  obtain ⟨s24, h24⟩ : ∃ s', s' = aluStep (cn 3 (t + 11) (t + 11) (t + 13)) s23 := ⟨_, rfl⟩
  have o24 : ∀ j, j ≠ t + 11 → s24 j = s23 j := fun j hj => by rw [h24]; exact slotUpd_other _ _ hj
  have d24 : s24 (t + 11) = aluVal (cn 3 (t + 11) (t + 11) (t + 13)) s23 := by rw [h24]; exact slotUpd_same _ _ _
  have run : aluRun (mulHiC X Y t) s = s24 := by
    simp only [mulHiC, aluRun_cons, aluRun_nil, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15, ← h16, ← h17, ← h18, ← h19, ← h20, ← h21, ← h22, ← h23, ← h24]
  rw [run]
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) only [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, aluVal, aluFn, cn, ci, Int.toNat_natCast, ite_true, ite_false, OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true]
  · simp (disch := omega) only [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, aluVal, aluFn, cn, ci, Int.toNat_natCast, ite_true, ite_false, OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true, ofInt_shift32, one_shl_sub, mulHiW]
  · intro j hj
    simp (disch := omega) only [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24]

theorem mulLimb_value (s : Nat → Runner.W) (X Y R c t : Nat)
    (hX : X < t ∨ t + 15 < X) (hY : Y < t ∨ t + 15 < Y) (hR : R < t ∨ t + 15 < R)
    (hc : c < t ∨ t + 15 < c) (hRc : R ≠ c) :
    aluRun (mulLimbC X Y R c t) s R = (mulStepW (s R) (s X) (s Y) (s c)).1 ∧
    aluRun (mulLimbC X Y R c t) s c = (mulStepW (s R) (s X) (s Y) (s c)).2 ∧
    ∀ j, j ≠ R → j ≠ c → (j < t ∨ t + 15 < j) → aluRun (mulLimbC X Y R c t) s j = s j := by
  obtain ⟨v0, v11, vf⟩ := mulHi_value s X Y t hX hY
  generalize hs1 : aluRun (mulHiC X Y t) s = s1 at v0 v11 vf
  have sR : s1 R = s R := vf R (by omega)
  have sc : s1 c = s c := vf c (by omega)
  obtain ⟨a1, ah1⟩ : ∃ s', s' = aluStep (cn 3 (t + 1) (R) (t)) s1 := ⟨_, rfl⟩
  have ao1 : ∀ j, j ≠ t + 1 → a1 j = s1 j := fun j hj => by rw [ah1]; exact slotUpd_other _ _ hj
  have ad1 : a1 (t + 1) = aluVal (cn 3 (t + 1) (R) (t)) s1 := by rw [ah1]; exact slotUpd_same _ _ _
  obtain ⟨a2, ah2⟩ : ∃ s', s' = aluStep (cn 27 (t + 2) (t + 1) (t)) a1 := ⟨_, rfl⟩
  have ao2 : ∀ j, j ≠ t + 2 → a2 j = a1 j := fun j hj => by rw [ah2]; exact slotUpd_other _ _ hj
  have ad2 : a2 (t + 2) = aluVal (cn 27 (t + 2) (t + 1) (t)) a1 := by rw [ah2]; exact slotUpd_same _ _ _
  obtain ⟨a3, ah3⟩ : ∃ s', s' = aluStep (cn 3 (t + 3) (t + 1) (c)) a2 := ⟨_, rfl⟩
  have ao3 : ∀ j, j ≠ t + 3 → a3 j = a2 j := fun j hj => by rw [ah3]; exact slotUpd_other _ _ hj
  have ad3 : a3 (t + 3) = aluVal (cn 3 (t + 3) (t + 1) (c)) a2 := by rw [ah3]; exact slotUpd_same _ _ _
  obtain ⟨a4, ah4⟩ : ∃ s', s' = aluStep (cn 27 (t + 4) (t + 3) (t + 1)) a3 := ⟨_, rfl⟩
  have ao4 : ∀ j, j ≠ t + 4 → a4 j = a3 j := fun j hj => by rw [ah4]; exact slotUpd_other _ _ hj
  have ad4 : a4 (t + 4) = aluVal (cn 27 (t + 4) (t + 3) (t + 1)) a3 := by rw [ah4]; exact slotUpd_same _ _ _
  obtain ⟨a5, ah5⟩ : ∃ s', s' = aluStep (cn 2 (R) (t + 3) 0) a4 := ⟨_, rfl⟩
  have ao5 : ∀ j, j ≠ R → a5 j = a4 j := fun j hj => by rw [ah5]; exact slotUpd_other _ _ hj
  have ad5 : a5 (R) = aluVal (cn 2 (R) (t + 3) 0) a4 := by rw [ah5]; exact slotUpd_same _ _ _
  obtain ⟨a6, ah6⟩ : ∃ s', s' = aluStep (cn 3 (c) (t + 11) (t + 2)) a5 := ⟨_, rfl⟩
  have ao6 : ∀ j, j ≠ c → a6 j = a5 j := fun j hj => by rw [ah6]; exact slotUpd_other _ _ hj
  have ad6 : a6 (c) = aluVal (cn 3 (c) (t + 11) (t + 2)) a5 := by rw [ah6]; exact slotUpd_same _ _ _
  obtain ⟨a7, ah7⟩ : ∃ s', s' = aluStep (cn 3 (c) (c) (t + 4)) a6 := ⟨_, rfl⟩
  have ao7 : ∀ j, j ≠ c → a7 j = a6 j := fun j hj => by rw [ah7]; exact slotUpd_other _ _ hj
  have ad7 : a7 (c) = aluVal (cn 3 (c) (c) (t + 4)) a6 := by rw [ah7]; exact slotUpd_same _ _ _
  have run : aluRun (mulLimbC X Y R c t) s = a7 := by
    unfold mulLimbC mulAccC
    rw [aluRun_append, hs1, aluRun_cons, ← ah1, aluRun_cons, ← ah2, aluRun_cons, ← ah3, aluRun_cons, ← ah4, aluRun_cons, ← ah5, aluRun_cons, ← ah6, aluRun_cons, ← ah7, aluRun_nil]
  rw [run]
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) only [ad1, ad2, ad3, ad4, ad5, ad6, ad7, ao1, ao2, ao3, ao4, ao5, ao6, ao7, aluVal, aluFn, cn, ci, Int.toNat_natCast, ite_true, ite_false, OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true, v0, v11, sR, sc, mulStepW]
  · simp (disch := omega) only [ad1, ad2, ad3, ad4, ad5, ad6, ad7, ao1, ao2, ao3, ao4, ao5, ao6, ao7, aluVal, aluFn, cn, ci, Int.toNat_natCast, ite_true, ite_false, OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true, v0, v11, sR, sc, mulStepW]
  · intro j h1 h2 h3
    simp (disch := omega) only [ao1, ao2, ao3, ao4, ao5, ao6, ao7, vf j h3]

end Gabbro.Stage0.Senke
