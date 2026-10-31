/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/CompareRun.lean
  Subject:   Execution of the multiword comparisons on actual memory.

  `wideLt_run` and `wideEq_run`: from two canonical `n+1`-limb operands the actual code leaves the
  Boolean word of `x < y` resp. `x = y` in slot `a`, changing only frame slots from `a` on. The
  difference must lie in the signed range of the limbs (`<`) resp. below `2^(64 (n+1))` in absolute
  value (`=`); operands extended by one limb always do.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Compare
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem orChain_aluIns {K a : Nat} (ha : a < K) :
    ∀ (n j : Nat), a + j + n ≤ K → ∀ i ∈ orChain n a j, AluIns K a i
  | 0, _, _, i, hi => by simp [orChain] at hi
  | n + 1, j, h, i, hi => by
    simp only [orChain, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact AluIns.bin 9 a a (a + j) _ rfl (Nat.le_refl _) ha ha (by omega)
    · exact orChain_aluIns ha n (j + 1) (by omega) i hi

theorem wideLtC_aluIns {K n a : Nat} (hK : a + 2 * (n + 1) + 7 ≤ K) :
    ∀ i ∈ wideLtC n a, AluIns K a i := by
  intro i hi
  simp only [wideLtC, List.mem_append] at hi
  rcases hi with hi | hi
  · exact wideAddC_aluIns (by decide) (by decide) hK i hi
  · simp only [signTail, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · exact AluIns.const (a + 2 * (n + 1)) 63 (by omega) (by omega) (by decide)
    · exact AluIns.bin 12 a (a + n) (a + 2 * (n + 1)) _ rfl (Nat.le_refl _) (by omega) (by omega) (by omega)

theorem wideEqC_aluIns {K n a : Nat} (hK : a + 2 * (n + 1) + 7 ≤ K) :
    ∀ i ∈ wideEqC n a, AluIns K a i := by
  intro i hi
  simp only [wideEqC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact wideAddC_aluIns (by decide) (by decide) hK i hi
  · exact orChain_aluIns (by omega) n 1 (by omega) i hi
  · simp only [eqTail, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · exact AluIns.const (a + 2 * (n + 1)) 0 (by omega) (by omega) (by decide)
    · exact AluIns.bin 14 a a (a + 2 * (n + 1)) _ rfl (Nat.le_refl _) (by omega) (by omega) (by omega)

variable [Kern]

theorem wideLt_run {m : Runner.Mem} {pc fp : Runner.W} {K n a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * (n + 1) + 7 ≤ K)
    (hc : CodeAt m pc (wideLtC n a)) (hfar : CodeFar pc (wideLtC n a).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding (n + 1) x))
    (hy : WordsAt m fp (a + (n + 1)) (integerEncoding (n + 1) y))
    (hr1 : -(2 ^ 63 * 2 ^ (64 * n)) ≤ x - y) (hr2 : x - y < 2 ^ 63 * 2 ^ (64 * n)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideLtC n a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 a)) = some (Runner.IR.bool (decide (x < y))) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideLtC_aluIns hKa) (slotVal m fp) hv
  refine ⟨m', st, ag, ?_⟩
  have h := rd a (by omega)
  rw [h, wideLt_value n a (slotVal m fp) x y (slotVal_words hF (by omega) x hx)
    (slotVal_words hF (by omega) y hy) hr1 hr2]

theorem wideEq_run {m : Runner.Mem} {pc fp : Runner.W} {K n a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * (n + 1) + 7 ≤ K)
    (hc : CodeAt m pc (wideEqC n a)) (hfar : CodeFar pc (wideEqC n a).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding (n + 1) x))
    (hy : WordsAt m fp (a + (n + 1)) (integerEncoding (n + 1) y))
    (hr1 : -(2 ^ (64 * (n + 1))) < x - y) (hr2 : x - y < 2 ^ (64 * (n + 1))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideEqC n a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 a)) = some (Runner.IR.bool (decide (x = y))) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideEqC_aluIns hKa) (slotVal m fp) hv
  refine ⟨m', st, ag, ?_⟩
  have h := rd a (by omega)
  rw [h, wideEq_value n a (slotVal m fp) x y (slotVal_words hF (by omega) x hx)
    (slotVal_words hF (by omega) y hy) hr1 hr2]

end Gabbro.Stage0.Senke
