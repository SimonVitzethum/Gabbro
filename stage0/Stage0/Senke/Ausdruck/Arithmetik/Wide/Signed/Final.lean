/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Final.lean
  Subject:   Signed multiword division and remainder on actual memory.

  Operands `x` at slot `a` and `y` at `a+k` as canonical two's-complement limbs, `y ≠ 0`, both in
  the signed `k`-limb range; the quotient `Int.tdiv x y` replaces `x` and the remainder `Int.tmod x y`
  replaces `y`, modulo `2^(64k)` (the quotient of the minimum by `-1` keeps the minimum's encoding).
  `Zahl.sdiv` / `Zahl.srem` exclude a zero divisor by type (`1 ≤ l2 ∨ h2 ≤ -1`). Slots from `a` to
  `a+4k+25` are the kernel's.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Value

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem condNegC_aluIns {K d : Nat} (k p c F MS TA Z : Nat) (hd : d ≤ p) (hpc : p + k ≤ c) (hK : c + 2 * k + 7 ≤ K)
    (hF : F < K) (hMS : MS < K) (hTA : TA < K) (hZ : Z < K) (hdMS : d ≤ MS) (hpTA : p ≤ TA) :
    ∀ i ∈ condNegC k p c F MS TA Z, AluIns K d i := by
  intro i hi
  simp only [condNegC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | hi) | rfl) | hi
  · exact copyWords_aluIns k c p (by omega) (by omega) (by omega) i hi
  · exact (wideNegC_aluIns (K := K) (k := k) (a := c) hK i hi).mono (by omega)
  · exact AluIns.bin 4 MS Z F _ rfl hdMS hMS hZ hF
  · exact selSeq_aluIns p c MS TA k hd (by omega) (by omega) hpTA hMS hTA i hi

theorem wideSdivC_aluIns {K : Nat} (k a : Nat) (hk : 1 ≤ k) (hK : a + 4 * k + 25 ≤ K) :
    ∀ i ∈ wideSdivC k a, AluIns K a i := by
  intro i hi
  simp only [wideSdivC, sdSign, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((((((rfl | rfl | rfl | rfl) | hi) | hi) | rfl) | hi) | hi) | hi
  · exact AluIns.const (a + 4 * k + 18 + 2) 63 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + 4 * k + 18 + 5) 0 (by omega) (by omega) (by decide)
  · exact AluIns.bin 12 (a + 4 * k + 18) (a + (k - 1)) (a + 4 * k + 18 + 2) _ rfl (by omega) (by omega)
      (by omega) (by omega)
  · exact AluIns.bin 12 (a + 4 * k + 18 + 1) (a + k + (k - 1)) (a + 4 * k + 18 + 2) _ rfl (by omega) (by omega)
      (by omega) (by omega)
  · exact condNegC_aluIns k a (a + 2 * k) _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) i hi
  · exact condNegC_aluIns k (a + k) (a + 2 * k) _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) i hi
  · exact AluIns.bin 10 (a + 4 * k + 18 + 6) (a + 4 * k + 18) (a + 4 * k + 18 + 1) _ rfl (by omega) (by omega)
      (by omega) (by omega)
  · exact (wideDivC_aluIns (K := K) k a hk (by omega) i hi)
  · exact condNegC_aluIns k a (a + 2 * k) _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) i hi
  · exact condNegC_aluIns k (a + k) (a + 2 * k) _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) i hi

variable [Kern]

/-- Multiword `Int.tdiv x y` and `Int.tmod x y`: the quotient replaces `x`, the remainder replaces `y`. -/
theorem wideSdiv_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 4 * k + 25 ≤ K) (hk : 1 ≤ k)
    (hc : CodeAt m pc (wideSdivC k a)) (hfar : CodeFar pc (wideSdivC k a).length fp K) (x y : Int)
    (hy0 : y ≠ 0) (hx1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x) (hx2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hy1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ y) (hy2 : y < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hxm : WordsAt m fp a (integerEncoding k x)) (hym : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideSdivC k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k (x.tdiv y)) ∧
      WordsAt m' fp (a + k) (integerEncoding k (x.tmod y)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideSdivC_aluIns k a hk hKa) (slotVal m fp) hv
  obtain ⟨v1, v2⟩ := wideSdiv_value k a hk x y hy0 hx1 hx2 hy1 hy2 (slotVal m fp)
    (fun j hj => slotVal_words hF (by omega) x hxm j hj) (fun j hj => slotVal_words hF (by omega) y hym j hj)
  exact ⟨m', st, ag, words_of_slotVal _ (by omega) _ rd v1, words_of_slotVal _ (by omega) _ rd v2⟩

end Gabbro.Stage0.Senke
