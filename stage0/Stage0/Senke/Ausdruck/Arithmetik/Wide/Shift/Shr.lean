/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Shr.lean
  Subject:   Multiword `shr` by a runtime count, on the canonical limbs.

  `Zahl.shr` is `a / 2^b` for nonnegative operands with the count typed below the storage width;
  no runtime stop path exists. The kernel is exact for every count `n < 64 k` and every operand
  below `2^(64 k)`: `x / 2^n`. Limb stages run in ascending limb order, so a limb is read before it
  is overwritten; a source beyond the top limb is the zero slot, which is what the limb is.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Shl

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem wideShrC_length (k S a : Nat) : (wideShrC k S a).length = 7 + S * (4 + 3 * k) + 4 * k := by
  simp only [wideShrC, List.length_append, shPre_length, stagesC_length, bitC_length, shrOrder,
    List.length_range]

theorem shrOrder_mem {k j : Nat} : j ∈ shrOrder k ↔ j < k := by
  simp only [shrOrder, List.mem_range]

theorem shrSrc_lt (k a c j : Nat) (hj : j < k) : shrSrc k a c j < a + k ∨ shrSrc k a c j = a + k + 5 := by
  unfold shrSrc; split <;> omega

theorem shrSrcB_lt (k a j : Nat) (hj : j < k) : shrSrcB k a j < a + k ∨ shrSrcB k a j = a + k + 5 := by
  unfold shrSrcB; split <;> omega

theorem shr_pw (k a c : Nat) (hc : 1 ≤ c) :
    (shrOrder k).Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ shrSrc k a c j) := by
  unfold shrOrder
  refine (List.pairwise_lt_range (n := k)).imp_of_mem (fun {x y} hx hy h => ?_)
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  unfold shrSrc
  split <;> omega

theorem shrB_pw (k a : Nat) :
    (shrOrder k).Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ shrSrcB k a j) := by
  unfold shrOrder
  refine (List.pairwise_lt_range (n := k)).imp_of_mem (fun {x y} hx hy h => ?_)
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  unfold shrSrcB
  split <;> omega

theorem wideShr_value (k S a n x : Nat) (hn : n < 64 * k) (hS : k ≤ 2 ^ S) (hS63 : S ≤ 63)
    (hk : 64 * k < 2 ^ 64) (hxk : x < 2 ^ (64 * k)) (s : Nat → Runner.W)
    (hN : s (a + k) = BitVec.ofNat 64 n) (hx : ∀ j, j < k → s (a + j) = lmb (x : Int) j) :
    ∀ j, j < k → aluRun (wideShrC k S a) s (a + j) = lmb ((x / 2 ^ n : Nat) : Int) j := by
  intro j hj
  have hn64 : n < 2 ^ 64 := by omega
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := shPre_run k a n hn64 s hN
  have hlim : ∀ m c (s' : Nat → Runner.W), 1 ≤ c → s' (a + k + 5) = 0 →
      (∀ j, j < k → s' (a + j) = lmb ((x / 2 ^ (64 * m) : Nat) : Int) j) →
      ∀ j, j < k → s' (shrSrc k a c j) = lmb ((x / 2 ^ (64 * (m + c)) : Nat) : Int) j := by
    intro m c s' hc hz hl j hj
    have e : x / 2 ^ (64 * (m + c)) = x / 2 ^ (64 * m) / 2 ^ (64 * c) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.div_div_eq_div_mul]
    rw [e, lmb_shr_limbs]
    by_cases hcj : j + c < k
    · simp only [shrSrc, hcj, ite_true]
      exact hl (j + c) hcj
    · simp only [shrSrc, hcj, ite_false]
      rw [hz, lmb_high _ k _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxk) (by omega)]
  have hl : ∀ j, j < k → j ∈ shrOrder k := fun j hj => shrOrder_mem.mpr hj
  have hlk : ∀ j ∈ shrOrder k, j < k := fun j hj => shrOrder_mem.mp hj
  obtain ⟨st1, st2⟩ := stagesC_value k a (n / 64) (by omega) (shrSrc k a) (shrOrder k)
    (fun m => x / 2 ^ (64 * m)) hl hlk (fun c j hj => shrSrc_lt k a c j hj) (fun c hc => shr_pw k a c hc)
    hlim (aluRun (shPre k a) s) p1 p4 p5
    (fun j hj => by
      rw [p6 (a + j) (Or.inl (by omega)), hx j hj]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one])
    S hS63
  have hq : n / 64 % 2 ^ S = n / 64 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hS)
  rw [hq] at st1
  set s2 := aluRun (stagesC k a (shrSrc k a) (shrOrder k) S) (aluRun (shPre k a) s) with hs2
  have o2 : s2 (a + k + 2) = BitVec.ofNat 64 (n % 64) := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p2
  have o3 : s2 (a + k + 3) = BitVec.ofNat 64 (63 - n % 64) := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p3
  have o4 : s2 (a + k + 4) = 1 := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p4
  have o5 : s2 (a + k + 5) = 0 := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p5
  obtain ⟨b1, b2⟩ := bitC_value k a 12 11 (fun a b => a >>> (b.toNat % 64)) (fun a b => a <<< (b.toNat % 64))
    rfl rfl (by decide) (by decide) (by decide) (by decide) (shrSrcB k a) (shrOrder k) hlk
    (fun j hj => shrSrcB_lt k a j hj) (shrB_pw k a) s2
  have run : aluRun (wideShrC k S a) s = aluRun (bitC k a 12 11 (shrSrcB k a) (shrOrder k)) s2 := by
    simp only [wideShrC, aluRun_append]
    rfl
  rw [run, b1 j (shrOrder_mem.mpr hj)]
  have hrn : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have hX' : x / 2 ^ (64 * (n / 64)) < 2 ^ (64 * k) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxk
  have hp : s2 (shrSrcB k a j) = lmb ((x / 2 ^ (64 * (n / 64)) : Nat) : Int) (j + 1) := by
    by_cases h0 : j + 1 < k
    · simp only [shrSrcB, h0, ite_true]; exact st1 (j + 1) h0
    · simp only [shrSrcB, h0, ite_false]
      rw [o5, lmb_high _ k _ hX' (by omega)]
  rw [st1 j hj, hp, o2, o3, o4]
  have w := shrBit_word (x / 2 ^ (64 * (n / 64))) (n % 64) j hrn (BitVec.ofNat 64 (n % 64)) 1
    (BitVec.ofNat 64 (63 - n % 64)) (by rw [BitVec.toNat_ofNat]; omega) rfl
    (by rw [BitVec.toNat_ofNat]; omega)
  rw [← w]
  congr 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

theorem wideShrC_aluIns {K : Nat} (k S a : Nat) (hK : a + k + 10 ≤ K) (hS : S < 2 ^ 31) :
    ∀ i ∈ wideShrC k S a, AluIns K a i := by
  intro i hi
  simp only [wideShrC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact shPre_aluIns k a hK i hi
  · exact stagesC_aluIns k a (shrSrc k a) (shrOrder k) hK (fun j hj => shrOrder_mem.mp hj)
      (fun c j hj => shrSrc_lt k a c j hj) S hS i hi
  · exact bitC_aluIns k a 12 11 _ _ rfl rfl (shrSrcB k a) (shrOrder k) hK (fun j hj => shrOrder_mem.mp hj)
      (fun j hj => shrSrcB_lt k a j hj) i hi

variable [Kern]

/-- Multiword `x >> n` for a runtime count `n < 64 k` in the word after the operand. -/
theorem wideShr_run {m : Runner.Mem} {pc fp : Runner.W} {K k S a n : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + k + 10 ≤ K) (hn : n < 64 * k) (hS : k ≤ 2 ^ S)
    (hS63 : S ≤ 63) (hc : CodeAt m pc (wideShrC k S a))
    (hfar : CodeFar pc (wideShrC k S a).length fp K) (x : Nat) (hxk : x < 2 ^ (64 * k))
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hN : m.rd64 (slot fp (BitVec.ofNat 64 (a + k))) = some (BitVec.ofNat 64 n)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideShrC k S a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x / 2 ^ n : Nat) : Int)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideShrC_aluIns k S a hKa (by omega)) (slotVal m fp) hv
  have hN' : slotVal m fp (a + k) = BitVec.ofNat 64 n := by
    have := hv (a + k) (by omega)
    rw [hN] at this
    exact (Option.some.inj this).symm
  exact ⟨m', st, ag, words_of_slotVal _ (by omega) _ rd
    (wideShr_value k S a n x hn hS hS63 (by omega) hxk (slotVal m fp) hN'
      (fun j hj => slotVal_words hF (by omega) (x : Int) hx j hj))⟩

end Gabbro.Stage0.Senke
