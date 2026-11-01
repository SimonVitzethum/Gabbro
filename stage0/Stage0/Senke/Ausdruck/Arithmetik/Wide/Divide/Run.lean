/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Run.lean
  Subject:   Unsigned multiword division and remainder on actual memory.

  Layout for `k` limbs at slot `a`: the dividend at `a ..< a+k`, the divisor at `a+k ..< a+2k`, scratch
  above (`K ≥ a+4k+18`). The quotient replaces the dividend, the remainder the divisor. `Zahl.div`
  and `Zahl.rem` require a divisor range of `1 ≤ l2`, so the divisor is nonzero by type: there is no
  runtime stop path to define, `0 < y` is the typed range (the kernel is stated under it).
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Code
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem wideDiv_value (k a x y : Nat) (hk : 1 ≤ k) (hy0 : 0 < y) (hy : y < 2 ^ (64 * k))
    (hx : x < 2 ^ (64 * k)) (s : Nat → Runner.W) (hX : ∀ j, j < k → s (a + j) = lmb (x : Int) j)
    (hD : ∀ j, j < k → s (a + k + j) = lmb (y : Int) j) :
    (∀ j, j < k → aluRun (wideDivC k a) s (a + j) = lmb ((x / y : Nat) : Int) j) ∧
    (∀ j, j < k → aluRun (wideDivC k a) s (a + k + j) = lmb ((x % y : Nat) : Int) j) := by
  have h1 := dvPre_value k a y x hy s hX hD
  have h2 := dvLoop_value k a (a + 4 * k + 10) y x hk rfl hy0 hy hx _ h1 (64 * k) (Nat.le_refl _)
  obtain ⟨iR, iX⟩ := dvIter_spec k y x hy0 hx hk (64 * k) (Nat.le_refl _)
  have e : aluRun (wideDivC k a) s = aluRun (dvLoop k a (a + 4 * k + 10) (64 * k)) (aluRun (dvPre k a) s) := by
    simp only [wideDivC, aluRun_append]
  obtain ⟨d1, d2, _⟩ := h2
  rw [e]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [d1 j hj, iX, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.mul_comm x, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]
  · rw [d2 j (by omega), iR, Nat.sub_self, Nat.pow_zero, Nat.div_one]

theorem wideDivC_aluIns {K : Nat} (k a : Nat) (hk : 1 ≤ k) (hK : a + 4 * k + 18 ≤ K) :
    ∀ i ∈ wideDivC k a, AluIns K a i := by
  intro i hi
  simp only [wideDivC, List.mem_append] at hi
  rcases hi with hi | hi
  · exact dvPre_aluIns k a hK i hi
  · exact dvLoop_aluIns k a _ hk rfl hK _ i hi

variable [Kern]

/-- Multiword `x / y` and `x % y`: the quotient replaces the dividend, the remainder the divisor. -/
theorem wideDiv_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 4 * k + 18 ≤ K) (hk : 1 ≤ k)
    (hc : CodeAt m pc (wideDivC k a)) (hfar : CodeFar pc (wideDivC k a).length fp K) (x y : Nat)
    (hy0 : 0 < y) (hy : y < 2 ^ (64 * k)) (hx : x < 2 ^ (64 * k))
    (hxm : WordsAt m fp a (integerEncoding k (x : Int)))
    (hym : WordsAt m fp (a + k) (integerEncoding k (y : Int))) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideDivC k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k ((x / y : Nat) : Int)) ∧
      WordsAt m' fp (a + k) (integerEncoding k ((x % y : Nat) : Int)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideDivC_aluIns k a hk hKa) (slotVal m fp) hv
  obtain ⟨v1, v2⟩ := wideDiv_value k a x y hk hy0 hy hx (slotVal m fp)
    (fun j hj => slotVal_words hF (by omega) (x : Int) hxm j hj)
    (fun j hj => slotVal_words hF (by omega) (y : Int) hym j hj)
  exact ⟨m', st, ag, words_of_slotVal _ (by omega) _ rd v1, words_of_slotVal _ (by omega) _ rd v2⟩

end Gabbro.Stage0.Senke
