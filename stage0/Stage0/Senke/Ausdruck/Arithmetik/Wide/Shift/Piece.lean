/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Piece.lean
  Subject:   The per-limb pieces of a multiword shift and their effect on the slot valuation.

  `selP` selects between a limb and a source slot under a full-word mask:
  `A := A ^ ((A ^ src) & M)`. With `M = 0` the limb stays, with `M = -1` it becomes `src`.
  `bitP` combines the shifted limb with the bits carried over from a neighbouring limb.
  Both write exactly the limb slot and their temporaries.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Seq

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem aluStep_cn {o a b c : Nat} {f : Runner.W → Runner.W → Runner.W} (hf : aluFn o = some f)
    (ho1 : o ≠ 1) (ho2 : o ≠ 2) (s : Nat → Runner.W) :
    aluStep (cn o a b c) s = slotUpd s a (f (s b) (s c)) := by
  simp only [aluStep, aluVal, cn, ci, Int.toNat_natCast, hf, ho1, ho2, ite_false]

theorem aluStep_const (a : Nat) (k : Int) (s : Nat → Runner.W) :
    aluStep (ci 1 a k 0) s = slotUpd s a (BitVec.ofInt 64 k) := by
  simp only [aluStep, aluVal, ci, Int.toNat_natCast, ite_true]

theorem aluStep_xor (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 10 a b c) s = slotUpd s a (s b ^^^ s c) := aluStep_cn (f := fun a b => a ^^^ b) rfl (by decide) (by decide) s
theorem aluStep_and (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 8 a b c) s = slotUpd s a (s b &&& s c) := aluStep_cn (f := fun a b => a &&& b) rfl (by decide) (by decide) s
theorem aluStep_or (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 9 a b c) s = slotUpd s a (s b ||| s c) := aluStep_cn (f := fun a b => a ||| b) rfl (by decide) (by decide) s
theorem aluStep_sub (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 4 a b c) s = slotUpd s a (s b - s c) := aluStep_cn (f := fun a b => a - b) rfl (by decide) (by decide) s
theorem aluStep_shl (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 11 a b c) s = slotUpd s a (s b <<< ((s c).toNat % 64)) :=
  aluStep_cn (f := fun a b => a <<< (b.toNat % 64)) rfl (by decide) (by decide) s
theorem aluStep_shr (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 12 a b c) s = slotUpd s a (s b >>> ((s c).toNat % 64)) :=
  aluStep_cn (f := fun a b => a >>> (b.toNat % 64)) rfl (by decide) (by decide) s

/-! ## Selection under a mask -/

def selP (src M T a j : Nat) : List II :=
  [cn 10 T (a + j) src, cn 8 T T M, cn 10 (a + j) (a + j) T]

@[simp] theorem selP_length (src M T a j : Nat) : (selP src M T a j).length = 3 := rfl

def selF (src : Nat → Nat) (M a : Nat) (j : Nat) (s : Nat → Runner.W) : Runner.W :=
  s (a + j) ^^^ ((s (a + j) ^^^ s (src j)) &&& s M)

theorem selP_run (src M T a j : Nat) (h1 : T ≠ a + j) (h3 : T ≠ M) (s : Nat → Runner.W) :
    aluRun (selP src M T a j) s (a + j) = s (a + j) ^^^ ((s (a + j) ^^^ s src) &&& s M) ∧
    ∀ i, i ≠ a + j → i ≠ T → aluRun (selP src M T a j) s i = s i := by
  have e : aluRun (selP src M T a j) s =
      slotUpd (slotUpd (slotUpd s T (s (a + j) ^^^ s src)) T
        ((s (a + j) ^^^ s src) &&& s M)) (a + j)
        (s (a + j) ^^^ ((s (a + j) ^^^ s src) &&& s M)) := by
    funext i
    simp only [selP, aluRun_cons, aluRun_nil, aluStep_xor, aluStep_and, slotUpd]
    by_cases hi1 : i = a + j <;> by_cases hi2 : i = T <;> simp [hi1, hi2, h1, h1.symm, Ne.symm h3]
  rw [e]
  refine ⟨?_, fun i hi1 hi2 => ?_⟩
  · simp [slotUpd]
  · simp [slotUpd, hi1, hi2]

/-! ## Bit shift with carry from a neighbour -/

def bitP (oM oX src Rr O W T T2 a j : Nat) : List II :=
  [cn oM T (a + j) Rr, cn oX T2 src O, cn oX T2 T2 W, cn 9 (a + j) T T2]

@[simp] theorem bitP_length (oM oX src Rr O W T T2 a j : Nat) : (bitP oM oX src Rr O W T T2 a j).length = 4 := rfl

theorem bitP_run (oM oX : Nat) (fM fX : Runner.W → Runner.W → Runner.W)
    (hM : aluFn oM = some fM) (hX : aluFn oX = some fX) (hM1 : oM ≠ 1) (hM2 : oM ≠ 2)
    (hX1 : oX ≠ 1) (hX2 : oX ≠ 2) (src Rr O W T T2 a j : Nat)
    (hT : T ≠ a + j) (hT2 : T2 ≠ a + j) (hTT : T ≠ T2) (hs : T ≠ src ∧ T2 ≠ src)
    (hr : T ≠ Rr ∧ T2 ≠ Rr) (ho : T ≠ O ∧ T2 ≠ O) (hw : T ≠ W ∧ T2 ≠ W) (s : Nat → Runner.W) :
    aluRun (bitP oM oX src Rr O W T T2 a j) s (a + j) =
      fM (s (a + j)) (s Rr) ||| fX (fX (s src) (s O)) (s W) ∧
    ∀ i, i ≠ a + j → i ≠ T → i ≠ T2 → aluRun (bitP oM oX src Rr O W T T2 a j) s i = s i := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ho1, ho2⟩ := ho
  obtain ⟨hw1, hw2⟩ := hw
  have e : aluRun (bitP oM oX src Rr O W T T2 a j) s =
      slotUpd (slotUpd (slotUpd (slotUpd s T (fM (s (a + j)) (s Rr))) T2 (fX (s src) (s O))) T2
        (fX (fX (s src) (s O)) (s W))) (a + j)
        (fM (s (a + j)) (s Rr) ||| fX (fX (s src) (s O)) (s W)) := by
    funext i
    simp only [bitP, aluRun_cons, aluRun_nil, aluStep_cn hM hM1 hM2, aluStep_cn hX hX1 hX2, aluStep_or, slotUpd]
    by_cases hi1 : i = a + j <;> by_cases hi2 : i = T <;> by_cases hi3 : i = T2 <;>
      simp [hi1, hi2, hi3, hT, hT2, hTT, Ne.symm hs1, Ne.symm ho1, Ne.symm hw1, Ne.symm hw2]
  rw [e]
  refine ⟨?_, fun i hi1 hi2 hi3 => ?_⟩
  · simp [slotUpd]
  · simp [slotUpd, hi1, hi2, hi3]

end Gabbro.Stage0.Senke
