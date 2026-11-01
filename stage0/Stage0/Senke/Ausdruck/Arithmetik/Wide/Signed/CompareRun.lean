/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/CompareRun.lean
  Subject:   Mixed signedness multiword comparisons execute on actual code and memory.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Compare
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem wideMixedC_aluIns {K k a : Nat} (leftSigned : Bool) (mode : WideCompare) (hk : 1 ≤ k)
    (hK : a + 2 * k + 2 * (k + 1) + 7 ≤ K) : ∀ i ∈ wideMixedC leftSigned mode k a, AluIns K a i := by
  intro i hi
  cases mode with
  | lt =>
    simp only [wideMixedC, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact wideComparePrep_aluIns _ _ hk (by omega) (by omega) (by omega) (by omega) i hi
    · exact (wideLtC_aluIns hK i hi).mono (by omega)
    · simp only [List.mem_singleton] at hi
      subst hi
      exact .mov _ _ (by omega) (by omega) (by omega)
  | eq =>
    simp only [wideMixedC, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact wideComparePrep_aluIns _ _ hk (by omega) (by omega) (by omega) (by omega) i hi
    · exact (wideEqC_aluIns hK i hi).mono (by omega)
    · simp only [List.mem_singleton] at hi
      subst hi
      exact .mov _ _ (by omega) (by omega) (by omega)
  | le =>
    simp only [wideMixedC, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact wideComparePrep_aluIns _ _ hk (by omega) (by omega) (by omega) (by omega) i hi
    · exact (wideLtC_aluIns hK i hi).mono (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact .const _ 1 (by omega) (by omega) (by decide)
      · exact .bin 10 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)

variable [Kern]

/-- One signed and one unsigned k-limb input, either order; the exact Boolean result replaces slot a. -/
theorem wideMixed_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (leftSigned : Bool) (mode : WideCompare) (x y : Int) (hk : 1 ≤ k)
    (hx : WideFits leftSigned k x) (hy : WideFits (!leftSigned) k y)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k + 2 * (k + 1) + 7 ≤ K)
    (hc : CodeAt m pc (wideMixedC leftSigned mode k a)) (hfar : CodeFar pc (wideMixedC leftSigned mode k a).length fp K)
    (hX : WordsAt m fp a (integerEncoding k x)) (hY : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideMixedC leftSigned mode k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 a)) = some (Runner.IR.bool (wideCompareResult mode x y)) := by
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideMixedC_aluIns leftSigned mode hk hKa)
    (slotVal m fp) (fun i hi => slotVal_rd hF hi)
  refine ⟨m', st, ag, ?_⟩
  rw [rd a (by omega), wideMixed_value leftSigned mode k a x y hk hx hy _
    (slotVal_words hF (by omega) x hX) (slotVal_words hF (by omega) y hY)]

end Gabbro.Stage0.Senke
