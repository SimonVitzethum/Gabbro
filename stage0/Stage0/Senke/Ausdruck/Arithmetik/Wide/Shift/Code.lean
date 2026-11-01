/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Code.lean
  Subject:   The shifter's instructions are admitted by the straight-line executor.

  Every destination lies in `a ..< K`, every operand inside the frame, and every constant is a
  32-bit literal.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Count
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

theorem selP_aluIns {K a : Nat} (src M T j : Nat) (hj : a + j < K) (hT : a ≤ T) (hTK : T < K) (hs : src < K)
    (hM : M < K) : ∀ i ∈ selP src M T a j, AluIns K a i := by
  intro i hi
  simp only [selP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact AluIns.bin 10 T (a + j) src _ rfl hT hTK hj hs
  · exact AluIns.bin 8 T T M _ rfl hT hTK hTK hM
  · exact AluIns.bin 10 (a + j) (a + j) T _ rfl (by omega) hj hj hTK

theorem bitP_aluIns {K a : Nat} (oM oX : Nat) (fM fX : Runner.W → Runner.W → Runner.W)
    (hM : aluFn oM = some fM) (hX : aluFn oX = some fX) (src Rr O W T T2 j : Nat) (hj : a + j < K)
    (hT : a ≤ T) (hTK : T < K) (hT2 : a ≤ T2) (hT2K : T2 < K) (hs : src < K) (hr : Rr < K) (ho : O < K)
    (hw : W < K) : ∀ i ∈ bitP oM oX src Rr O W T T2 a j, AluIns K a i := by
  intro i hi
  simp only [bitP, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact AluIns.bin oM T (a + j) Rr fM hM hT hTK hj hr
  · exact AluIns.bin oX T2 src O fX hX hT2 hT2K hs ho
  · exact AluIns.bin oX T2 T2 W fX hX hT2 hT2K hT2K hw
  · exact AluIns.bin 9 (a + j) T T2 _ rfl (by omega) hj hTK hT2K

theorem stgC_aluIns {K : Nat} (k a idx : Nat) (src : Nat → Nat) (l : List Nat) (hK : a + k + 10 ≤ K)
    (hidx : idx < 2 ^ 31) (hlk : ∀ j ∈ l, j < k) (hsrc : ∀ j, j < k → src j < a + k ∨ src j = a + k + 5) :
    ∀ i ∈ stgC k a idx src l, AluIns K a i := by
  intro i hi
  simp only [stgC, List.mem_append] at hi
  rcases hi with hi | hi
  · simp only [stgPre, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact AluIns.const (a + k + 9) idx (by omega) (by omega) (by simp only [lit32]; simp; omega)
    · exact AluIns.bin 12 (a + k + 7) (a + k + 1) (a + k + 9) _ rfl (by omega) (by omega) (by omega) (by omega)
    · exact AluIns.bin 8 (a + k + 7) (a + k + 7) (a + k + 4) _ rfl (by omega) (by omega) (by omega) (by omega)
    · exact AluIns.bin 4 (a + k + 6) (a + k + 5) (a + k + 7) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact seqC_aluIns _ l (fun j hj => selP_aluIns _ _ _ j (by have := hlk j hj; omega) (by omega) (by omega)
      (by have := hsrc j (hlk j hj); omega) (by omega)) i hi

theorem stagesC_aluIns {K : Nat} (k a : Nat) (src : Nat → Nat → Nat) (l : List Nat) (hK : a + k + 10 ≤ K)
    (hlk : ∀ j ∈ l, j < k) (hsrc : ∀ c j, j < k → src c j < a + k ∨ src c j = a + k + 5) :
    ∀ S, S < 2 ^ 31 → ∀ i ∈ stagesC k a src l S, AluIns K a i
  | 0, _, i, hi => by simp [stagesC] at hi
  | S + 1, hS, i, hi => by
    simp only [stagesC, List.mem_append] at hi
    rcases hi with hi | hi
    · exact stagesC_aluIns k a src l hK hlk hsrc S (by omega) i hi
    · exact stgC_aluIns k a S (src (2 ^ S)) l hK (by omega) hlk (hsrc _) i hi

theorem bitC_aluIns {K : Nat} (k a oM oX : Nat) (fM fX : Runner.W → Runner.W → Runner.W)
    (hM : aluFn oM = some fM) (hX : aluFn oX = some fX) (srcB : Nat → Nat) (l : List Nat)
    (hK : a + k + 10 ≤ K) (hlk : ∀ j ∈ l, j < k) (hsrc : ∀ j, j < k → srcB j < a + k ∨ srcB j = a + k + 5) :
    ∀ i ∈ bitC k a oM oX srcB l, AluIns K a i := by
  exact seqC_aluIns _ l (fun j hj => bitP_aluIns oM oX fM fX hM hX _ _ _ _ _ _ j
    (by have := hlk j hj; omega) (by omega) (by omega) (by omega) (by omega)
    (by have := hsrc j (hlk j hj); omega) (by omega) (by omega) (by omega))

theorem shPre_aluIns {K : Nat} (k a : Nat) (hK : a + k + 10 ≤ K) : ∀ i ∈ shPre k a, AluIns K a i := by
  intro i hi
  simp only [shPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AluIns.const (a + k + 8) 6 (by omega) (by omega) (by decide)
  · exact AluIns.bin 12 (a + k + 1) (a + k) (a + k + 8) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.const (a + k + 7) 63 (by omega) (by omega) (by decide)
  · exact AluIns.bin 8 (a + k + 2) (a + k) (a + k + 7) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 4 (a + k + 3) (a + k + 7) (a + k + 2) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.const (a + k + 4) 1 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + k + 5) 0 (by omega) (by omega) (by decide)

end Gabbro.Stage0.Senke
