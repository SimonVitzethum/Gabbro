/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/Extend.lean
  Subject:   In-place sign and zero extension of canonical multiword integers.

  The low j limbs survive; limbs j .. k-1 receive the extension word. Three scratch slots follow
  the k-limb destination. Signed extension uses the sign of the original top limb and ext_word;
  unsigned extension writes zero, including when the original top bit is set.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Eng

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

/-- The complete signed or unsigned domain of k limbs. -/
def WideFits (signed : Bool) (k : Nat) (x : Int) : Prop :=
  if signed then -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x ∧ x < 2 ^ 63 * 2 ^ (64 * (k - 1))
  else 0 ≤ x ∧ x < 2 ^ (64 * k)

theorem wideFits_mono {signed : Bool} {j k : Nat} {x : Int} (hjk : j ≤ k)
    (hx : WideFits signed j x) : WideFits signed k x := by
  have hp : (2 : Int) ^ (64 * j) ≤ 2 ^ (64 * k) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show 64 * j ≤ 64 * k by omega)
  have hs : (2 : Int) ^ (64 * (j - 1)) ≤ 2 ^ (64 * (k - 1)) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show 64 * (j - 1) ≤ 64 * (k - 1) by omega)
  cases signed <;> simp only [WideFits, Bool.false_eq_true, ↓reduceIte] at hx ⊢ <;> constructor <;> omega

/-- Every limb above a representable operand is its sign word or zero. -/
theorem extend_limb (signed : Bool) (j i : Nat) (x : Int) (hj : 1 ≤ j) (hji : j ≤ i)
    (hx : WideFits signed j x) :
    lmb x i = if signed then 0 - Runner.IR.bool (decide (x < 0)) else 0 := by
  have hi : 1 ≤ i := by omega
  have hx' := wideFits_mono hji hx
  cases signed with
  | false =>
    simp only [WideFits, Bool.false_eq_true, ↓reduceIte] at hx'
    simp only [Bool.false_eq_true, ↓reduceIte, lmb, Int.ediv_eq_zero_of_lt hx'.1 hx'.2]
    rfl
  | true => exact ext_word x i hi hx'.1 hx'.2

theorem extendPre_value (signed : Bool) (j k a : Nat) (x : Int) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hx : WideFits signed j x) (s : Nat → Runner.W) (hX : s (a + (j - 1)) = lmb x (j - 1)) :
    aluRun (extendPre signed j k a) s (a + k + 2) =
      (if signed then 0 - Runner.IR.bool (decide (x < 0)) else 0) ∧
    (∀ i, i < a + k ∨ a + k + 3 ≤ i → aluRun (extendPre signed j k a) s i = s i) := by
  cases signed with
  | false =>
    simp only [extendPre, Bool.false_eq_true, ↓reduceIte, aluRun_cons, aluRun_nil, aluStep_const]
    exact ⟨by simp only [slotUpd_same]; rfl, fun i hi => slotUpd_other _ _ (by omega)⟩
  | true =>
    have sl := sign_limb (j - 1) x hx.1 hx.2
    have hs : (BitVec.ofInt 64 63).toNat % 64 = 63 := by decide
    rw [hs] at sl
    simp only [extendPre, ↓reduceIte, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_sub]
    constructor
    · have h1 : a + (j - 1) ≠ a + k + 1 := by omega
      have h2 : j - 1 ≠ k := by omega
      simp [slotUpd, hX, h1, h2, sl]
    · intro i hi
      have h1 : i ≠ a + k := by omega
      have h2 : i ≠ a + k + 1 := by omega
      have h3 : i ≠ a + k + 2 := by omega
      simp only [slotUpd, h1, h2, h3, ↓reduceIte]

theorem wideExtend_value (signed : Bool) (j k a : Nat) (x : Int) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hx : WideFits signed j x) (s : Nat → Runner.W) (hX : ∀ i, i < j → s (a + i) = lmb x i) :
    (∀ i, i < k → aluRun (wideExtendC signed j k a) s (a + i) = lmb x i) ∧
    (∀ i, i < a ∨ a + k + 3 ≤ i → aluRun (wideExtendC signed j k a) s i = s i) := by
  obtain ⟨p1, p2⟩ := extendPre_value signed j k a x hj hjk hx s (hX (j - 1) (by omega))
  let l := List.range' j (k - j)
  have mem : ∀ i, i ∈ l ↔ j ≤ i ∧ i < k := by
    intro i
    simp only [l, List.mem_range'_1]
    omega
  obtain ⟨v1, v2⟩ := seqC_value (fun i => [ci 2 (a + i : Nat) (a + k + 2 : Nat) 0])
    (fun _ s => s (a + k + 2)) (fun _ i => i = a + k + 2) (fun _ => False) (fun i => i < k) a
    (fun i hi s => by simp only [aluRun_cons, aluRun_nil, aluStep_mov, slotUpd_same])
    (fun i hi s b hb _ => by simp only [aluRun_cons, aluRun_nil, aluStep_mov, slotUpd_other _ _ hb])
    (fun _ _ s s' h => h _ rfl) (fun _ _ _ _ h => h) (fun _ _ h => h) l
    (fun i hi => ((mem i).mp hi).2) List.nodup_range'
    (List.pairwise_of_forall_mem_list (fun i hi _ _ => by have := ((mem i).mp hi).2; omega))
    (aluRun (extendPre signed j k a) s)
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [wideExtendC, aluRun_append]
    by_cases hji : j ≤ i
    · rw [v1 i ((mem i).mpr ⟨hji, hi⟩), p1, extend_limb signed j i x hj hji hx]
    · rw [v2 _ (fun h => h) (fun b hb => by have := ((mem b).mp hb).1; omega),
        p2 _ (Or.inl (by omega)), hX i (by omega)]
  · simp only [wideExtendC, aluRun_append]
    rw [v2 _ (fun h => h) (fun b hb => by have := ((mem b).mp hb).2; omega), p2 i (by omega)]

theorem wideExtendC_aluIns {K d j k a : Nat} (signed : Bool) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hd : d ≤ a) (hK : a + k + 3 ≤ K) : ∀ i ∈ wideExtendC signed j k a, AluIns K d i := by
  intro i hi
  simp only [wideExtendC, List.mem_append] at hi
  rcases hi with hi | hi
  · cases signed <;> simp only [extendPre, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hi
    · subst hi; exact AluIns.const _ 0 (by omega) (by omega) (by decide)
    · rcases hi with rfl | rfl | rfl | rfl
      · exact AluIns.const _ 0 (by omega) (by omega) (by decide)
      · exact AluIns.const _ 63 (by omega) (by omega) (by decide)
      · exact AluIns.bin 12 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
      · exact AluIns.bin 4 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact seqC_aluIns _ _ (fun b hb ins hins => by
      have hb' := List.mem_range'_1.mp hb
      simp only [List.mem_singleton] at hins
      subst hins
      exact AluIns.mov _ _ (by omega) (by omega) (by omega)) i hi

variable [Kern]

/-- Extend in place over actual code and memory, preserving every slot below a and outside the frame. -/
theorem wideExtend_run {m : Runner.Mem} {pc fp : Runner.W} {K j k a : Nat} (signed : Bool)
    (x : Int) (hj : 1 ≤ j) (hjk : j ≤ k) (hx : WideFits signed j x)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + k + 3 ≤ K)
    (hc : CodeAt m pc (wideExtendC signed j k a)) (hfar : CodeFar pc (wideExtendC signed j k a).length fp K)
    (hX : WordsAt m fp a (integerEncoding j x)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideExtendC signed j k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k x) := by
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar
    (wideExtendC_aluIns signed hj hjk (Nat.le_refl _) hKa) (slotVal m fp) (fun i hi => slotVal_rd hF hi)
  have value := (wideExtend_value signed j k a x hj hjk hx (slotVal m fp)
    (slotVal_words hF (by omega) x hX)).1
  exact ⟨m', st, ag, words_of_slotVal x (by omega) _ rd value⟩

end Gabbro.Stage0.Senke
