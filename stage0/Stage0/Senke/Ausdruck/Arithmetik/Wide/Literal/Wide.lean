/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/Wide.lean
  Subject:   Multiword literal materialization on the canonical limbs.

  Limb `j` of the literal `v` is the word `lmb v j = BitVec.ofInt 64 (v / 2^(64 j))`, materialized with the
  shared word materializer into slot `a+j`; ascending order lets limb `j`'s second scratch slot be the
  not yet written limb `j+1`. The last limb leaves one scratch slot above the literal.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Word
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem wideLitFrom_value (a : Nat) (v : Int) : ∀ (n j0 : Nat) (s : Nat → Runner.W),
    (∀ j, j0 ≤ j → j < j0 + n → aluRun (wideLitFrom a v j0 n) s (a + j) = lmb v j) ∧
    (∀ i, (i < a + j0 ∨ a + j0 + n + 1 ≤ i) → aluRun (wideLitFrom a v j0 n) s i = s i)
  | 0, j0, s => ⟨fun j h1 h2 => by omega, fun i _ => rfl⟩
  | n + 1, j0, s => by
    obtain ⟨w1, w2⟩ := wordConstant_run (a + j0) (v / 2 ^ (64 * j0)) s
    obtain ⟨r1, r2⟩ := wideLitFrom_value a v n (j0 + 1) (aluRun (wordConstant (a + j0) (v / 2 ^ (64 * j0))).1 s)
    refine ⟨fun j h1 h2 => ?_, fun i hi => ?_⟩
    · simp only [wideLitFrom, aluRun_append]
      by_cases hj : j = j0
      · subst hj
        rw [r2 _ (Or.inl (by omega)), w1]
        rfl
      · exact r1 j (by omega) (by omega)
    · simp only [wideLitFrom, aluRun_append]
      rw [r2 i (by omega), w2 i (by omega) (by omega)]

theorem konstWL_aluIns {K d : Nat} (dl : Nat) : ∀ (k n : Nat), dl ≤ d → d + 2 ≤ K →
    ∀ i ∈ (konstWL k n d).1, AluIns K dl i
  | 0, n, h1, h2, i, hi => by
    simp only [konstWL, List.mem_singleton] at hi
    subst hi
    exact AluIns.const d 0 h1 (by omega) (by decide)
  | k + 1, n, h1, h2, i, hi => by
    simp only [konstWL, bin2, ci_succ_bin, ci_succ_const, List.append_assoc, List.mem_append, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | rfl | rfl | rfl | rfl
    · exact konstWL_aluIns dl k (n / 65536) h1 h2 i hi
    · exact AluIns.const (d + 1) 65536 (by omega) (by omega) (by decide)
    · exact AluIns.bin 5 d d (d + 1) _ rfl h1 (by omega) (by omega) (by omega)
    · exact AluIns.const (d + 1) (n % 65536 : Nat) (by omega) (by omega) (lit32_nat (by omega))
    · exact AluIns.bin 3 d d (d + 1) _ rfl h1 (by omega) (by omega) (by omega)

theorem wordConstant_aluIns {K dl d : Nat} (n : Int) (h1 : dl ≤ d) (h2 : d + 2 ≤ K) :
    ∀ i ∈ (wordConstant d n).1, AluIns K dl i := by
  intro i hi
  unfold wordConstant at hi
  by_cases small : lit32 n = true
  · simp only [small, ↓reduceIte, List.mem_singleton] at hi
    subst hi
    exact AluIns.const d n h1 (by omega) small
  · simp only [small, Bool.false_eq_true, ↓reduceIte] at hi
    exact konstWL_aluIns dl 4 _ h1 h2 i hi

theorem wideLitFrom_aluIns {K dl a : Nat} (v : Int) (hdl : dl ≤ a) : ∀ (n j0 : Nat), a + j0 + n + 1 ≤ K →
    ∀ i ∈ wideLitFrom a v j0 n, AluIns K dl i
  | 0, j0, _, i, hi => by simp [wideLitFrom] at hi
  | n + 1, j0, hK, i, hi => by
    simp only [wideLitFrom, List.mem_append] at hi
    rcases hi with hi | hi
    · exact wordConstant_aluIns _ (by omega) (by omega) i hi
    · exact wideLitFrom_aluIns v hdl n (j0 + 1) (by omega) i hi

variable [Kern]

/-- A `k`-limb literal: the canonical limbs of `v`, one scratch slot above them. -/
theorem wideLit_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat} (v : Int)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + k + 1 ≤ K)
    (hc : CodeAt m pc (wideLitC k a v)) (hfar : CodeFar pc (wideLitC k a v).length fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideLitC k a v).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k v) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideLitFrom_aluIns (K := K) (dl := a) v (Nat.le_refl _) k 0
    (by omega)) (slotVal m fp) hv
  obtain ⟨v1, _⟩ := wideLitFrom_value a v k 0 (slotVal m fp)
  exact ⟨m', st, ag, words_of_slotVal v (by omega) _ rd (fun j hj => v1 j (by omega) (by omega))⟩

end Gabbro.Stage0.Senke
