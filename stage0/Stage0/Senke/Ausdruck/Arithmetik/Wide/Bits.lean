/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Bits.lean
  Subject:   Multiword bitwise operations, limb by limb.

  The source forms `&`, `|` and `^` are defined on the natural numbers of nonnegative operands.
  The limbs of `x op y` are the word operations on the limbs of `x` and `y`, so the chain needs no
  carry and no scratch: `A_j := A_j op B_j` for every limb.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

def bitChain (o : Nat) : Nat → Nat → Nat → List II
  | 0, _, _ => []
  | n + 1, A, B => cn o A A B :: bitChain o n (A + 1) (B + 1)

@[simp] theorem bitChain_length (o n A B : Nat) : (bitChain o n A B).length = n := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih => simp [bitChain, ih]

theorem bitChain_value (o : Nat) (f : Runner.W → Runner.W → Runner.W) (hf : aluFn o = some f)
    (ho1 : o ≠ 1) (ho2 : o ≠ 2) : ∀ (n A B : Nat) (s : Nat → Runner.W), A + n ≤ B →
    (∀ j, j < n → aluRun (bitChain o n A B) s (A + j) = f (s (A + j)) (s (B + j))) ∧
    (∀ j, (j < A ∨ A + n ≤ j) → aluRun (bitChain o n A B) s j = s j)
  | 0, A, B, s, _ => ⟨fun j hj => absurd hj (by omega), fun j _ => rfl⟩
  | n + 1, A, B, s, h => by
    obtain ⟨i1, i2⟩ := bitChain_value o f hf ho1 ho2 n (A + 1) (B + 1) (aluStep (cn o A A B) s) (by omega)
    have st : ∀ j, j ≠ A → aluStep (cn o A A B) s j = s j := fun j hj => slotUpd_other _ _ hj
    have sa : aluStep (cn o A A B) s A = f (s A) (s B) := by
      show slotUpd s A (aluVal (cn o A A B) s) A = _
      rw [slotUpd_same]
      simp only [aluVal, cn, ci, Int.toNat_natCast, hf, ho1, ho2, ite_false]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp only [bitChain, aluRun_cons]
      cases j with
      | zero =>
        show aluRun (bitChain o n (A + 1) (B + 1)) (aluStep (cn o A A B) s) A = _
        rw [i2 A (by omega), sa]
        rfl
      | succ j =>
        rw [show A + (j + 1) = A + 1 + j by omega, i1 j (by omega), st _ (by omega), st _ (by omega)]
        rw [show B + (j + 1) = B + 1 + j by omega]
    · simp only [bitChain, aluRun_cons]
      rw [i2 j (by omega), st j (by omega)]

/-! ## The limbs of a bitwise result -/

theorem lmb_natCast_toNat (n j : Nat) : (lmb (n : Int) j).toNat = n / 2 ^ (64 * j) % 2 ^ 64 := by
  rw [lmb_toNat]
  have : ((n : Int) / 2 ^ (64 * j)) % 2 ^ 64 = ((n / 2 ^ (64 * j) % 2 ^ 64 : Nat) : Int) := by
    push_cast
    rfl
  rw [this, Int.toNat_natCast]

theorem lmb_and (x y j : Nat) : lmb ((x &&& y : Nat) : Int) j = lmb (x : Int) j &&& lmb (y : Int) j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, lmb_natCast_toNat, lmb_natCast_toNat, lmb_natCast_toNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 64 <;> simp [hi]

theorem lmb_or (x y j : Nat) : lmb ((x ||| y : Nat) : Int) j = lmb (x : Int) j ||| lmb (y : Int) j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, lmb_natCast_toNat, lmb_natCast_toNat, lmb_natCast_toNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 64 <;> simp [hi]

theorem lmb_xor (x y j : Nat) : lmb ((x ^^^ y : Nat) : Int) j = lmb (x : Int) j ^^^ lmb (y : Int) j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, lmb_natCast_toNat, lmb_natCast_toNat, lmb_natCast_toNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 64 <;> simp [hi]

/-! ## Execution -/

def wideBitC (o k a : Nat) : List II := bitChain o k a (a + k)

theorem bitChain_aluIns {K d : Nat} (o : Nat) (f : Runner.W → Runner.W → Runner.W) (hf : aluFn o = some f) :
    ∀ (n A B : Nat), d ≤ A → A + n ≤ K → B + n ≤ K → ∀ i ∈ bitChain o n A B, AluIns K d i
  | 0, _, _, _, _, _, i, hi => by simp [bitChain] at hi
  | n + 1, A, B, hd, h1, h2, i, hi => by
    simp only [bitChain, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact AluIns.bin o A A B f hf hd (by omega) (by omega) (by omega)
    · exact bitChain_aluIns o f hf n (A + 1) (B + 1) (by omega) (by omega) (by omega) i hi

variable [Kern]

theorem wideBit_run {o : Nat} {f : Runner.W → Runner.W → Runner.W} (hf : aluFn o = some f)
    (ho1 : o ≠ 1) (ho2 : o ≠ 2) (g : Nat → Nat → Nat)
    (law : ∀ x y j, lmb ((g x y : Nat) : Int) j = f (lmb (x : Int) j) (lmb (y : Int) j))
    {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k ≤ K)
    (hc : CodeAt m pc (wideBitC o k a)) (hfar : CodeFar pc (wideBitC o k a).length fp K) (x y : Nat)
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hy : WordsAt m fp (a + k) (integerEncoding k (y : Int))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideBitC o k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((g x y : Nat) : Int)) ∧
      WordsAt m' fp (a + k) (integerEncoding k (y : Int)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar
    (fun i hi => bitChain_aluIns o f hf k a (a + k) (Nat.le_refl _) (by omega) (by omega) i hi)
    (slotVal m fp) hv
  have hxs := slotVal_words hF (by omega) (x : Int) hx
  have hys : ∀ j, j < k → slotVal m fp (a + k + j) = lmb (y : Int) j :=
    slotVal_words hF (by omega) (y : Int) hy
  obtain ⟨v1, v2⟩ := bitChain_value o f hf ho1 ho2 k a (a + k) (slotVal m fp) (by omega)
  refine ⟨m', st, ag, words_of_slotVal _ (by omega) _ rd (fun j hj => ?_), ?_⟩
  · show aluRun (bitChain o k a (a + k)) (slotVal m fp) (a + j) = _
    rw [v1 j hj, hxs j hj, hys j hj, law]
  · exact words_of_slotVal (y : Int) (by omega) _ rd (fun j hj => by
      show aluRun (bitChain o k a (a + k)) (slotVal m fp) (a + k + j) = _
      rw [v2 (a + k + j) (Or.inr (by omega))]; exact hys j hj)

theorem wideAnd_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k ≤ K)
    (hc : CodeAt m pc (wideBitC 8 k a)) (hfar : CodeFar pc (wideBitC 8 k a).length fp K) (x y : Nat)
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hy : WordsAt m fp (a + k) (integerEncoding k (y : Int))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideBitC 8 k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x &&& y : Nat) : Int)) ∧
      WordsAt m' fp (a + k) (integerEncoding k (y : Int)) :=
  wideBit_run (f := fun a b => a &&& b) rfl (by decide) (by decide) (· &&& ·) lmb_and hF hK hKa hc hfar x y hx hy

theorem wideOr_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k ≤ K)
    (hc : CodeAt m pc (wideBitC 9 k a)) (hfar : CodeFar pc (wideBitC 9 k a).length fp K) (x y : Nat)
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hy : WordsAt m fp (a + k) (integerEncoding k (y : Int))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideBitC 9 k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x ||| y : Nat) : Int)) ∧
      WordsAt m' fp (a + k) (integerEncoding k (y : Int)) :=
  wideBit_run (f := fun a b => a ||| b) rfl (by decide) (by decide) (· ||| ·) lmb_or hF hK hKa hc hfar x y hx hy

theorem wideXor_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k ≤ K)
    (hc : CodeAt m pc (wideBitC 10 k a)) (hfar : CodeFar pc (wideBitC 10 k a).length fp K) (x y : Nat)
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hy : WordsAt m fp (a + k) (integerEncoding k (y : Int))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideBitC 10 k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x ^^^ y : Nat) : Int)) ∧
      WordsAt m' fp (a + k) (integerEncoding k (y : Int)) :=
  wideBit_run (f := fun a b => a ^^^ b) rfl (by decide) (by decide) (· ^^^ ·) lmb_xor hF hK hKa hc hfar x y hx hy

end Gabbro.Stage0.Senke
