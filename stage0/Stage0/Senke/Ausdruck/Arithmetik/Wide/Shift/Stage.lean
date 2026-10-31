/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Stage.lean
  Subject:   One barrel-shifter stage: move every limb by `2^idx` positions when bit `idx` of the limb count is set.

  Frame layout above the operand `a .. a+k-1` (all slots from `a` on are the executor's destinations):
  `a+k` count, `+1` limb count `q`, `+2` bit count `r`, `+3` `63 - r`, `+4` one, `+5` zero, `+6` mask,
  `+7`/`+8` temporaries, `+9` stage constant. The stage computes `mask := 0 - ((q >> idx) & 1)` and
  selects, limb by limb in an order that never reads a written limb, the source slot or the limb itself.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Limb

namespace Gabbro.Stage0.Senke
open Runner.IR

def stgPre (k a idx : Nat) : List II :=
  [ci 1 (a + k + 9 : Nat) idx 0, cn 12 (a + k + 7) (a + k + 1) (a + k + 9),
   cn 8 (a + k + 7) (a + k + 7) (a + k + 4), cn 4 (a + k + 6) (a + k + 5) (a + k + 7)]

def stgC (k a idx : Nat) (src : Nat → Nat) (l : List Nat) : List II :=
  stgPre k a idx ++ seqC (fun j => selP (src j) (a + k + 6) (a + k + 7) a j) l

theorem stgC_length (k a idx : Nat) (src : Nat → Nat) (l : List Nat) :
    (stgC k a idx src l).length = 4 + 3 * l.length := by
  simp only [stgC, List.length_append, stgPre, List.length_cons, List.length_nil,
    seqC_length _ 3 (fun j => selP_length _ _ _ _ j)]

/-- The word mask of a bit: all ones or zero. -/
theorem mask_word (q idx : Nat) (hq : q < 2 ^ 64) (hidx : idx < 64) :
    (0 : Runner.W) - ((BitVec.ofNat 64 q >>> ((BitVec.ofInt 64 (idx : Int)).toNat % 64)) &&& 1) =
      if q.testBit idx then BitVec.allOnes 64 else 0 := by
  have hi : (BitVec.ofInt 64 (idx : Int)).toNat % 64 = idx := by
    simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    omega
  rw [hi]
  have key : (BitVec.ofNat 64 q >>> idx) &&& 1 = if q.testBit idx then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq,
      Nat.shiftRight_eq_div_pow]
    have : (1 : Runner.W).toNat = 1 := rfl
    rw [this, Nat.and_one_is_mod]
    have hb := Nat.testBit_eq_decide_div_mod_eq (x := q) (i := idx)
    have h01 := Nat.mod_two_eq_zero_or_one (q / 2 ^ idx)
    by_cases h : q.testBit idx = true
    · simp only [h, ite_true]
      rw [h] at hb
      have := of_decide_eq_true hb.symm
      omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
      simp only [Bool.not_eq_true] at h
      rw [h] at hb
      have := of_decide_eq_false hb.symm
      have z0 : (0 : Runner.W).toNat = 0 := rfl
      rw [z0]
      omega
  rw [key]
  split <;> decide

theorem stgPre_run (k a idx q : Nat) (hidx : idx < 64) (hq : q < 2 ^ 64) (s : Nat → Runner.W)
    (hQ : s (a + k + 1) = BitVec.ofNat 64 q) (hO : s (a + k + 4) = 1) (hZ : s (a + k + 5) = 0) :
    aluRun (stgPre k a idx) s (a + k + 6) = (if q.testBit idx then BitVec.allOnes 64 else 0) ∧
    ∀ i, i ≠ a + k + 9 → i ≠ a + k + 7 → i ≠ a + k + 6 → aluRun (stgPre k a idx) s i = s i := by
  have e : aluRun (stgPre k a idx) s =
      slotUpd (slotUpd (slotUpd (slotUpd s (a + k + 9) (BitVec.ofInt 64 (idx : Int))) (a + k + 7)
        (BitVec.ofNat 64 q >>> ((BitVec.ofInt 64 (idx : Int)).toNat % 64))) (a + k + 7)
        ((BitVec.ofNat 64 q >>> ((BitVec.ofInt 64 (idx : Int)).toNat % 64)) &&& 1)) (a + k + 6)
        (0 - ((BitVec.ofNat 64 q >>> ((BitVec.ofInt 64 (idx : Int)).toNat % 64)) &&& 1)) := by
    funext i
    simp only [stgPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub,
      slotUpd]
    by_cases h1 : i = a + k + 6 <;> by_cases h2 : i = a + k + 7 <;> by_cases h3 : i = a + k + 9 <;>
      simp [h1, h2, h3, hQ, hO, hZ]
  rw [e]
  refine ⟨?_, fun i h1 h2 h3 => ?_⟩
  · simp only [slotUpd, ite_true]
    exact mask_word q idx hq hidx
  · simp [slotUpd, h1, h2, h3]

theorem sel_zero (x y : Runner.W) : x ^^^ ((x ^^^ y) &&& 0) = x := by
  ext i
  simp

theorem sel_ones (x y : Runner.W) : x ^^^ ((x ^^^ y) &&& BitVec.allOnes 64) = y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_allOnes]
  cases x[i] <;> cases y[i] <;> rfl

/-- One stage: the limbs of the sequence `l` become their source slot when bit `idx` of `q` is set. -/
theorem stgC_value (k a idx q : Nat) (hidx : idx < 64) (hq : q < 2 ^ 64) (src : Nat → Nat) (l : List Nat)
    (hlk : ∀ j ∈ l, j < k) (hsrc : ∀ j, j < k → src j < a + k ∨ src j = a + k + 5)
    (hpw : l.Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ src j)) (s : Nat → Runner.W)
    (hQ : s (a + k + 1) = BitVec.ofNat 64 q) (hO : s (a + k + 4) = 1) (hZ : s (a + k + 5) = 0) :
    (∀ j ∈ l, aluRun (stgC k a idx src l) s (a + j) = if q.testBit idx then s (src j) else s (a + j)) ∧
    (∀ i, i ≠ a + k + 9 → i ≠ a + k + 7 → i ≠ a + k + 6 → (∀ j ∈ l, i ≠ a + j) →
      aluRun (stgC k a idx src l) s i = s i) := by
  obtain ⟨m1, m2⟩ := stgPre_run k a idx q hidx hq s hQ hO hZ
  have run : aluRun (stgC k a idx src l) s =
      aluRun (seqC (fun j => selP (src j) (a + k + 6) (a + k + 7) a j) l) (aluRun (stgPre k a idx) s) := by
    simp only [stgC, aluRun_append]
  have hnd : l.Nodup := hpw.imp (fun h => h.1)
  have hpw' : l.Pairwise (fun j' j => ¬ (a + j' = a + j ∨ a + j' = src j ∨ a + j' = a + k + 6)) :=
    hpw.imp_of_mem (fun {j' j} hj' _ h => by
      have := hlk j' hj'
      omega)
  obtain ⟨v1, v2⟩ := seqC_value (fun j => selP (src j) (a + k + 6) (a + k + 7) a j)
    (selF src (a + k + 6) a) (fun j i => i = a + j ∨ i = src j ∨ i = a + k + 6) (fun i => i = a + k + 7)
    (fun j => j < k) a
    (fun j hj s => (selP_run (src j) (a + k + 6) (a + k + 7) a j (by omega) (by omega) s).1)
    (fun j hj s i h1 h2 => (selP_run (src j) (a + k + 6) (a + k + 7) a j (by omega) (by omega) s).2 i h1 h2)
    (fun j hj s s' h => by
      simp only [selF]
      rw [h (a + j) (Or.inl rfl), h (src j) (Or.inr (Or.inl rfl)), h (a + k + 6) (Or.inr (Or.inr rfl))])
    (fun j hj i h => by
      have := hsrc j hj
      omega)
    (fun j hj => by omega) l hlk hnd hpw' (aluRun (stgPre k a idx) s)
  refine ⟨fun j hj => ?_, fun i h1 h2 h3 h4 => ?_⟩
  · have hjk := hlk j hj
    rw [run, v1 j hj]
    have hs := hsrc j hjk
    have e1 := m2 (a + j) (by omega) (by omega) (by omega)
    have e2 := m2 (src j) (by omega) (by omega) (by omega)
    simp only [selF]
    rw [e1, e2, m1]
    by_cases hb : q.testBit idx = true
    · simp only [hb, ite_true]; exact sel_ones _ _
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact sel_zero _ _
  · rw [run, v2 i (by omega) h4]
    exact m2 i h1 h2 h3

end Gabbro.Stage0.Senke
