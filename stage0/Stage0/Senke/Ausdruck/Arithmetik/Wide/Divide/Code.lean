/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Code.lean
  Subject:   The division code is admitted by the straight-line executor.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Loop
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Code
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

theorem AluIns.mono {K d d' : Nat} {i : II} (h : AluIns K d i) (hd : d' ≤ d) : AluIns K d' i := by
  cases h with
  | const a k h1 h2 hk => exact AluIns.const a k (by omega) h2 hk
  | mov a b h1 h2 h3 => exact AluIns.mov a b (by omega) h2 h3
  | bin o a b c f hf h1 h2 h3 h4 => exact AluIns.bin o a b c f hf (by omega) h2 h3 h4

theorem shl1C_aluIns {K d : Nat} (p n O W TB TA TB2 : Nat) (hp : d ≤ p) (hpn : p + n ≤ K) (hpTA : p ≤ TA)
    (hpTB2 : p ≤ TB2) (hTAK : TA < K) (hTB2K : TB2 < K) (hO : O < K) (hW : W < K) (hTB : TB < K) :
    ∀ i ∈ shl1C p n O W TB TA TB2, AluIns K d i := by
  apply seqC_aluIns
  intro j hj i hi
  have hjn : j < n := by simpa [List.mem_reverse, List.mem_range] using hj
  unfold shl1P at hi
  by_cases h0 : j = 0
  · simp only [h0, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact AluIns.bin 11 TA p O _ rfl (by omega) hTAK (by omega) hO
    · exact AluIns.bin 9 p TA TB _ rfl hp (by omega) hTAK hTB
  · simp only [h0, ite_false] at hi
    exact (bitP_aluIns (K := K) (a := p) 11 12 _ _ rfl rfl _ _ _ _ _ _ j (by omega) hpTA hTAK hpTB2 hTB2K
      (by omega) hO hO hW i hi).mono hp

theorem flagC_aluIns {K d : Nat} (c Tk : Nat) (hd : d ≤ c + 4) (hK : c + 6 ≤ K) (hTk : Tk < K) :
    ∀ i ∈ flagC c Tk, AluIns K d i := by
  intro i hi
  simp only [flagC, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact AluIns.bin 12 (c + 4) Tk (c + 3) _ rfl hd (by omega) hTk (by omega)
  · exact AluIns.bin 4 (c + 4) (c + 1) (c + 4) _ rfl hd (by omega) (by omega) (by omega)
  · exact AluIns.bin 4 (c + 5) c (c + 4) _ rfl (by omega) (by omega) (by omega) (by omega)

theorem selSeq_aluIns {K d : Nat} (R T MS TA n : Nat) (hR : d ≤ R) (hRn : R + n ≤ K) (hTn : T + n ≤ K)
    (hRT : R ≤ TA) (hMS : MS < K) (hTA : TA < K) :
    ∀ i ∈ selSeq R T MS TA n, AluIns K d i := by
  apply seqC_aluIns
  intro j hj i hi
  have hjn : j < n := by simpa [List.mem_reverse, List.mem_range] using hj
  exact (selP_aluIns (K := K) (a := R) (T + j) MS TA j (by omega) hRT hTA (by omega) hMS i hi).mono hR

theorem dvStep_aluIns {K : Nat} (k a c : Nat) (hk : 1 ≤ k) (hc : c = a + 4 * k + 10) (hK : a + 4 * k + 18 ≤ K) :
    ∀ i ∈ dvStep k a c, AluIns K a i := by
  subst hc
  intro i hi
  simp only [dvStep, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (((((rfl | hi) | hi) | hi) | hi) | hi) | hi
  · exact AluIns.bin 12 (a + 4 * k + 10 + 4) (a + (k - 1)) (a + 4 * k + 10 + 3) _ rfl (by omega) (by omega)
      (by omega) (by omega)
  · exact shl1C_aluIns _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) i hi
  · exact copyWords_aluIns (k + 1) (a + 2 * k + 1) (a + k) (by omega) (by omega) (by omega) i hi
  · exact (wideAddC_aluIns (K := K) (k := k + 1) (a := a + 2 * k + 1) (mask := -1) (carry := 1) (by decide)
      (by decide) (by omega) i hi).mono (by omega)
  · exact flagC_aluIns _ _ (by omega) (by omega) (by omega) i hi
  · exact selSeq_aluIns _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) i hi
  · exact shl1C_aluIns _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) i hi

theorem dvLoop_aluIns {K : Nat} (k a c : Nat) (hk : 1 ≤ k) (hc : c = a + 4 * k + 10) (hK : a + 4 * k + 18 ≤ K) :
    ∀ n, ∀ i ∈ dvLoop k a c n, AluIns K a i
  | 0, i, hi => by simp [dvLoop] at hi
  | n + 1, i, hi => by
    simp only [dvLoop, List.mem_append] at hi
    rcases hi with hi | hi
    · exact dvLoop_aluIns k a c hk hc hK n i hi
    · exact dvStep_aluIns k a c hk hc hK i hi

theorem dvPre_aluIns {K : Nat} (k a : Nat) (hK : a + 4 * k + 18 ≤ K) : ∀ i ∈ dvPre k a, AluIns K a i := by
  intro i hi
  simp only [dvPre, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | rfl) | hi) | rfl | rfl | rfl | rfl
  · exact copyWords_aluIns k (a + 3 * k + 2) (a + k) (by omega) (by omega) (by omega) i hi
  · exact AluIns.const (a + 4 * k + 2) 0 (by omega) (by omega) (by decide)
  · exact zeroSlots_aluIns (k + 1) (a + k) (by omega) (by omega) i hi
  · exact AluIns.const (a + 4 * k + 10) 0 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + 4 * k + 11) 1 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + 4 * k + 12) 62 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + 4 * k + 13) 63 (by omega) (by omega) (by decide)

end Gabbro.Stage0.Senke
