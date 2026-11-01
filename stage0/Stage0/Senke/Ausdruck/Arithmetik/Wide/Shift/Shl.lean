/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Shl.lean
  Subject:   Multiword `shl` by a runtime count, on the canonical limbs.

  `Zahl.shl` is `a * 2^b` for nonnegative operands with the count typed below the storage width
  (`hw2 : h2 < w`): there is no runtime stop path, a count at or above the width is excluded by
  the type. The kernel is exact for every count `n < 64 k`: `x * 2^n` modulo `2^(64 k)`, which is the
  canonical encoding `integerEncoding k (x * 2^n)`. Layout: operand in `a ..< a+k`, count word at
  `a+k`, scratch above (`K ≥ a+k+10`). Limb stages run in descending limb order, so a limb is read
  before it is overwritten.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Code
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem wideShlC_length (k S a : Nat) : (wideShlC k S a).length = 7 + S * (4 + 3 * k) + 4 * k := by
  simp only [wideShlC, List.length_append, shPre_length, stagesC_length, bitC_length, shlOrder,
    List.length_reverse, List.length_range]

theorem shlOrder_mem {k j : Nat} : j ∈ shlOrder k ↔ j < k := by
  simp only [shlOrder, List.mem_reverse, List.mem_range]

theorem shlSrc_lt (k a c j : Nat) (hj : j < k) : shlSrc k a c j < a + k ∨ shlSrc k a c j = a + k + 5 := by
  unfold shlSrc; split <;> omega

theorem shlSrcB_lt (k a j : Nat) (hj : j < k) : shlSrcB k a j < a + k ∨ shlSrcB k a j = a + k + 5 := by
  unfold shlSrcB; split <;> omega

theorem shl_pw (k a c : Nat) (hc : 1 ≤ c) :
    (shlOrder k).Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ shlSrc k a c j) := by
  unfold shlOrder
  rw [List.pairwise_reverse]
  refine (List.pairwise_lt_range (n := k)).imp_of_mem (fun {x y} hx hy h => ?_)
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  unfold shlSrc
  split <;> omega

theorem shlB_pw (k a : Nat) :
    (shlOrder k).Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ shlSrcB k a j) := by
  unfold shlOrder
  rw [List.pairwise_reverse]
  refine (List.pairwise_lt_range (n := k)).imp_of_mem (fun {x y} hx hy h => ?_)
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  unfold shlSrcB
  split <;> omega

theorem wideShl_value (k S a n x : Nat) (hn : n < 64 * k) (hS : k ≤ 2 ^ S) (hS63 : S ≤ 63)
    (hk : 64 * k < 2 ^ 64) (s : Nat → Runner.W) (hN : s (a + k) = BitVec.ofNat 64 n)
    (hx : ∀ j, j < k → s (a + j) = lmb (x : Int) j) :
    ∀ j, j < k → aluRun (wideShlC k S a) s (a + j) = lmb ((x * 2 ^ n : Nat) : Int) j := by
  intro j hj
  have hn64 : n < 2 ^ 64 := by omega
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := shPre_run k a n hn64 s hN
  have hlim : ∀ m c (s' : Nat → Runner.W), 1 ≤ c → s' (a + k + 5) = 0 →
      (∀ j, j < k → s' (a + j) = lmb ((x * 2 ^ (64 * m) : Nat) : Int) j) →
      ∀ j, j < k → s' (shlSrc k a c j) = lmb ((x * 2 ^ (64 * (m + c)) : Nat) : Int) j := by
    intro m c s' hc hz hl j hj
    have e : x * 2 ^ (64 * (m + c)) = x * 2 ^ (64 * m) * 2 ^ (64 * c) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_assoc]
    rw [e, lmb_shl_limbs]
    by_cases hcj : c ≤ j
    · simp only [shlSrc, hcj, ite_true]
      exact hl (j - c) (by omega)
    · simp only [shlSrc, hcj, ite_false]
      exact hz
  have hl : ∀ j, j < k → j ∈ shlOrder k := fun j hj => shlOrder_mem.mpr hj
  have hlk : ∀ j ∈ shlOrder k, j < k := fun j hj => shlOrder_mem.mp hj
  obtain ⟨st1, st2⟩ := stagesC_value k a (n / 64) (by omega) (shlSrc k a) (shlOrder k)
    (fun m => x * 2 ^ (64 * m)) hl hlk (fun c j hj => shlSrc_lt k a c j hj) (fun c hc => shl_pw k a c hc)
    hlim (aluRun (shPre k a) s) p1 p4 p5
    (fun j hj => by
      rw [p6 (a + j) (Or.inl (by omega)), hx j hj]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one])
    S hS63
  have hq : n / 64 % 2 ^ S = n / 64 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hS)
  rw [hq] at st1
  set s2 := aluRun (stagesC k a (shlSrc k a) (shlOrder k) S) (aluRun (shPre k a) s) with hs2
  have o2 : s2 (a + k + 2) = BitVec.ofNat 64 (n % 64) := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p2
  have o3 : s2 (a + k + 3) = BitVec.ofNat 64 (63 - n % 64) := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p3
  have o4 : s2 (a + k + 4) = 1 := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p4
  have o5 : s2 (a + k + 5) = 0 := by
    rw [st2 _ (by omega) (by omega) (by omega) (Or.inr (by omega))]; exact p5
  obtain ⟨b1, b2⟩ := bitC_value k a 11 12 (fun a b => a <<< (b.toNat % 64)) (fun a b => a >>> (b.toNat % 64))
    rfl rfl (by decide) (by decide) (by decide) (by decide) (shlSrcB k a) (shlOrder k) hlk
    (fun j hj => shlSrcB_lt k a j hj) (shlB_pw k a) s2
  have run : aluRun (wideShlC k S a) s = aluRun (bitC k a 11 12 (shlSrcB k a) (shlOrder k)) s2 := by
    simp only [wideShlC, aluRun_append]
    rfl
  rw [run, b1 j (shlOrder_mem.mpr hj)]
  have hrn : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have hp : s2 (shlSrcB k a j) = if j = 0 then 0 else lmb ((x * 2 ^ (64 * (n / 64)) : Nat) : Int) (j - 1) := by
    by_cases h0 : j = 0
    · simp only [shlSrcB, h0, ite_true]; exact o5
    · simp only [shlSrcB, h0, ite_false]; exact st1 (j - 1) (by omega)
  rw [st1 j hj, hp, o2, o3, o4]
  have w := shlBit_word (x * 2 ^ (64 * (n / 64))) (n % 64) j hrn (BitVec.ofNat 64 (n % 64)) 1
    (BitVec.ofNat 64 (63 - n % 64)) (if j = 0 then 0 else lmb ((x * 2 ^ (64 * (n / 64)) : Nat) : Int) (j - 1))
    (by rw [BitVec.toNat_ofNat]; omega) rfl (by rw [BitVec.toNat_ofNat]; omega) rfl
  rw [← w]
  congr 2
  rw [Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

theorem wideShlC_aluIns {K : Nat} (k S a : Nat) (hK : a + k + 10 ≤ K) (hS : S < 2 ^ 31) :
    ∀ i ∈ wideShlC k S a, AluIns K a i := by
  intro i hi
  simp only [wideShlC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact shPre_aluIns k a hK i hi
  · exact stagesC_aluIns k a (shlSrc k a) (shlOrder k) hK (fun j hj => shlOrder_mem.mp hj)
      (fun c j hj => shlSrc_lt k a c j hj) S hS i hi
  · exact bitC_aluIns k a 11 12 _ _ rfl rfl (shlSrcB k a) (shlOrder k) hK (fun j hj => shlOrder_mem.mp hj)
      (fun j hj => shlSrcB_lt k a j hj) i hi

variable [Kern]

/-- Multiword `x << n` for a runtime count `n < 64 k` in the word after the operand. -/
theorem wideShl_run {m : Runner.Mem} {pc fp : Runner.W} {K k S a n : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + k + 10 ≤ K) (hn : n < 64 * k) (hS : k ≤ 2 ^ S)
    (hS63 : S ≤ 63) (hc : CodeAt m pc (wideShlC k S a))
    (hfar : CodeFar pc (wideShlC k S a).length fp K) (x : Nat)
    (hx : WordsAt m fp a (integerEncoding k (x : Int)))
    (hN : m.rd64 (slot fp (BitVec.ofNat 64 (a + k))) = some (BitVec.ofNat 64 n)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideShlC k S a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x * 2 ^ n : Nat) : Int)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideShlC_aluIns k S a hKa (by omega)) (slotVal m fp) hv
  have hN' : slotVal m fp (a + k) = BitVec.ofNat 64 n := by
    have := hv (a + k) (by omega)
    rw [hN] at this
    exact (Option.some.inj this).symm
  exact ⟨m', st, ag, words_of_slotVal _ (by omega) _ rd
    (wideShl_value k S a n x hn hS hS63 (by omega) (slotVal m fp) hN'
      (fun j hj => slotVal_words hF (by omega) (x : Int) hx j hj))⟩

end Gabbro.Stage0.Senke
