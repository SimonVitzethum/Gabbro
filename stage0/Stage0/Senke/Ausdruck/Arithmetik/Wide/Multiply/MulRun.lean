/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/MulRun.lean
  Subject:   Execution of the multiword product on actual memory.

  `wideMul_run`: from two canonical `k`-limb operands (`WordsAt` of `integerEncoding k x` at `a` and
  `integerEncoding k y` at `a+k`) the actual IR code `wideMulC k a` leaves `integerEncoding k (x*y)` in
  the first operand's limbs, i.e. the product modulo `2^(64k)`, exactly the canonical result when the
  declared product range fits `k` limbs. Only frame slots from `a` on change; `a + 3k + 17 <= K`.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Multiply.MulRows
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem mulLimbC_aluIns {K d X Y R c t : Nat} (hX : X < K) (hY : Y < K) (hR : R < K) (hc : c < K)
    (hdR : d ≤ R) (hdc : d ≤ c) (hdt : d ≤ t) (ht : t + 15 < K) :
    ∀ i ∈ mulLimbC X Y R c t, AluIns K d i := by
  intro i hi
  simp only [mulLimbC, mulHiC, mulAccC, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact AluIns.bin _ _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
    | exact AluIns.mov _ _ (by omega) (by omega) (by omega)
    | exact AluIns.const _ _ (by omega) (by omega) (by decide)

theorem mulRow_aluIns {K d c t : Nat} (hc : c < K) (hdc : d ≤ c) (hdt : d ≤ t) (ht : t + 15 < K) :
    ∀ (n X Y R : Nat), X < K → Y + n ≤ K → R + n ≤ K → d ≤ R →
      ∀ i ∈ mulRow n X Y R c t, AluIns K d i
  | 0, _, _, _, _, _, _, _, i, hi => by simp [mulRow] at hi
  | n + 1, X, Y, R, hX, hY, hR, hdR, i, hi => by
    simp only [mulRow, List.mem_append] at hi
    rcases hi with hi | hi
    · exact mulLimbC_aluIns hX (by omega) (by omega) hc hdR hdc hdt ht i hi
    · exact mulRow_aluIns hc hdc hdt ht n X (Y + 1) (R + 1) hX (by omega) (by omega) (by omega) i hi

theorem mulRows_aluIns {K k a : Nat} (hK : a + 3 * k + 17 ≤ K) :
    ∀ (m i : Nat), m + i = k → ∀ ins ∈ mulRows k a m i, AluIns K a ins
  | 0, _, _, ins, hi => by simp [mulRows] at hi
  | m + 1, i, hmi, ins, hi => by
    simp only [mulRows, mulRowC, List.mem_append, List.mem_cons] at hi
    rcases hi with (rfl | hi) | hi
    · exact AluIns.const (a + 3 * k) 0 (by omega) (by omega) (by decide)
    · exact mulRow_aluIns (K := K) (d := a) (by omega) (by omega) (by omega) (by omega) (m + 1) (a + i)
        (a + k) (a + 2 * k + i) (by omega) (by omega) (by omega) (by omega) ins hi
    · exact mulRows_aluIns hK m (i + 1) (by omega) ins hi

theorem zeroSlots_aluIns {K d : Nat} : ∀ (n r : Nat), d ≤ r → r + n ≤ K → ∀ i ∈ zeroSlotsC n r, AluIns K d i
  | 0, _, _, _, i, hi => by simp [zeroSlotsC] at hi
  | n + 1, r, hd, hK, i, hi => by
    simp only [zeroSlotsC, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact AluIns.const r 0 hd (by omega) (by decide)
    · exact zeroSlots_aluIns n (r + 1) (by omega) (by omega) i hi

theorem copyWords_aluIns {K d : Nat} : ∀ (n dst src : Nat), d ≤ dst → dst + n ≤ K → src + n ≤ K →
    ∀ i ∈ copyWords n dst src, AluIns K d i
  | 0, _, _, _, _, _, i, hi => by simp [copyWords] at hi
  | n + 1, dst, src, hd, h1, h2, i, hi => by
    simp only [copyWords, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact AluIns.mov dst src hd (by omega) (by omega)
    · exact copyWords_aluIns n (dst + 1) (src + 1) (by omega) (by omega) (by omega) i hi

theorem wideMulC_aluIns {K k a : Nat} (hK : a + 3 * k + 17 ≤ K) :
    ∀ i ∈ wideMulC k a, AluIns K a i := by
  intro i hi
  simp only [wideMulC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact zeroSlots_aluIns k (a + 2 * k) (by omega) (by omega) i hi
  · exact mulRows_aluIns hK k 0 (by omega) i hi
  · exact copyWords_aluIns k a (a + 2 * k) (Nat.le_refl _) (by omega) (by omega) i hi

variable [Kern]

theorem wideMul_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 3 * k + 17 ≤ K)
    (hc : CodeAt m pc (wideMulC k a)) (hfar : CodeFar pc (wideMulC k a).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding k x)) (hy : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideMulC k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k (x * y)) ∧
      WordsAt m' fp (a + k) (integerEncoding k y) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideMulC_aluIns hKa) (slotVal m fp) hv
  have hxs := slotVal_words hF (by omega) x hx
  have hys : ∀ j, j < k → slotVal m fp (a + k + j) = lmb y j := slotVal_words hF (by omega) y hy
  obtain ⟨v1, v2⟩ := wideMul_value k a (slotVal m fp) x y hxs hys
  refine ⟨m', st, ag, words_of_slotVal (x * y) (by omega) _ rd v1, ?_⟩
  exact words_of_slotVal y (by omega) _ rd (fun j hj => by
    rw [v2 (a + k + j) ⟨by omega, by omega⟩]; exact hys j hj)

end Gabbro.Stage0.Senke
