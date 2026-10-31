/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/Eng.lean
  Subject:   The narrowing test of a multiword value against literal bounds.

  `wideOutC k a lo hi` leaves the word `1` in slot `a+k+3` iff the value `x` of the `k`-limb operand at `a`
  lies outside `lo ≤ x ≤ hi`, and `0` otherwise; the operand is preserved. The operand is sign-extended by
  one limb (the difference of two `k`-limb values always fits `k+1` limbs), compared signed against the
  materialized bounds with the exact multiword `<`, and the two flags are or-ed. Layout from `a`: the
  operand, zero, 63, the extension word, the flag, the first comparison's frame at `r1 = a+k+4`, the
  second at `r2 = r1 + 2(k+1) + 7`.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Wide
import Stage0.Senke.Ausdruck.Arithmetik.Wide.CompareRun

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

def wideOutC (k a : Nat) (lo hi : Int) : List II :=
  [ci 1 (a + k : Nat) 0 0, ci 1 (a + k + 1 : Nat) 63 0, cn 12 (a + k + 2) (a + (k - 1)) (a + k + 1),
   cn 4 (a + k + 2) (a + k) (a + k + 2)] ++
  copyWords k (a + k + 4) a ++ [ci 2 (a + k + 4 + k : Nat) (a + k + 2 : Nat) 0] ++
  wideLitC (k + 1) (a + k + 4 + (k + 1)) lo ++ wideLtC k (a + k + 4) ++
  wideLitC (k + 1) (a + k + 4 + (2 * (k + 1) + 7)) hi ++
  copyWords k (a + k + 4 + (2 * (k + 1) + 7) + (k + 1)) a ++
  [ci 2 (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k : Nat) (a + k + 2 : Nat) 0] ++
  wideLtC k (a + k + 4 + (2 * (k + 1) + 7)) ++
  [cn 9 (a + k + 3) (a + k + 4) (a + k + 4 + (2 * (k + 1) + 7))]

theorem ext_word (x : Int) (k : Nat) (hk : 1 ≤ k) (h1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x)
    (h2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1))) :
    lmb x k = 0 - Runner.IR.bool (decide (x < 0)) := by
  have hP : (2 : Int) ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * (k - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hP0 : (0 : Int) < 2 ^ (64 * k) := by positivity
  have q1 : -1 ≤ x / 2 ^ (64 * k) := Int.le_ediv_of_mul_le hP0 (by omega)
  have q2 : x / 2 ^ (64 * k) < 1 := Int.ediv_lt_of_lt_mul hP0 (by omega)
  have q3 : x / 2 ^ (64 * k) < 0 ↔ x < 0 := by
    rw [Int.ediv_lt_iff_lt_mul hP0]; omega
  by_cases hx : x < 0
  · have hq : x / 2 ^ (64 * k) = -1 := by have := q3.mpr hx; omega
    simp only [lmb, hq, hx, decide_true, Runner.IR.bool, ite_true]
    rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from ofInt_minus_one]
    decide
  · have hq : x / 2 ^ (64 * k) = 0 := by have := fun h => hx (q3.mp h); omega
    simp only [lmb, hq, hx, decide_false, Runner.IR.bool]
    simp

theorem aluStep_mov (a b : Nat) (s : Nat → Runner.W) :
    aluStep (ci 2 (a : Nat) (b : Nat) 0) s = slotUpd s a (s b) := by
  simp only [aluStep, aluVal, ci, Int.toNat_natCast]
  simp

theorem wideLtC_frame (n a : Nat) (s : Nat → Runner.W) (i : Nat) (h : i < a ∨ a + 2 * (n + 1) + 7 ≤ i) :
    aluRun (wideLtC n a) s i = s i := by
  have hA := wideLtC_aluIns (K := a + 2 * (n + 1) + 7) (n := n) (a := a) (Nat.le_refl _)
  rcases h with h | h
  · exact aluRun_low hA s h
  · exact aluRun_high hA s h

theorem bool_or (p q : Prop) [Decidable p] [Decidable q] :
    Runner.IR.bool (decide p) ||| Runner.IR.bool (decide q) = Runner.IR.bool (decide (p ∨ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [Runner.IR.bool, hp, hq]

theorem wideOut_value (k a : Nat) (lo hi x : Int) (hk : 1 ≤ k) (s : Nat → Runner.W)
    (hx1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x) (hx2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hl1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ lo) (hl2 : lo < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hh1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ hi) (hh2 : hi < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hX : ∀ j, j < k → s (a + j) = lmb x j) :
    aluRun (wideOutC k a lo hi) s (a + k + 3) = Runner.IR.bool (decide (x < lo ∨ hi < x)) ∧
    ∀ j, j < k → aluRun (wideOutC k a lo hi) s (a + j) = lmb x j := by
  have hP : (2 : Int) ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * (k - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hP0 : (0 : Int) < 2 ^ (64 * (k - 1)) := by positivity
  have hP1 : (0 : Int) < 2 ^ (64 * k) := by positivity
  -- the sign extension word
  have h63 : (BitVec.ofInt 64 63).toNat % 64 = 63 := by decide
  have sl := sign_limb (k - 1) x hx1 hx2
  rw [h63] at sl
  have ex := ext_word x k hk hx1 hx2
  have f1 : a + (k - 1) ≠ a + k := by omega
  have f2 : a + (k - 1) ≠ a + k + 1 := by omega
  have f3 : a + (k - 1) ≠ a + k + 2 := by omega
  have g1 : k - 1 ≠ k := by omega
  have g2 : k - 1 ≠ k + 1 := by omega
  have g3 : k - 1 ≠ k + 2 := by omega
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = aluRun [ci 1 (a + k : Nat) 0 0, ci 1 (a + k + 1 : Nat) 63 0,
      cn 12 (a + k + 2) (a + (k - 1)) (a + k + 1), cn 4 (a + k + 2) (a + k) (a + k + 2)] s := ⟨_, rfl⟩
  have s1E : s1 (a + k + 2) = lmb x k := by
    rw [hs1]
    simp only [aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_sub, slotUpd]
    simp [f2, g1, hX (k - 1) (by omega)]
    rw [sl, ex]
    simp
  have s1o : ∀ i, i ≠ a + k + 2 → i ≠ a + k + 1 → i ≠ a + k → s1 i = s i := fun i h1 h2 h3 => by
    rw [hs1]
    simp only [aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_sub, slotUpd]
    simp [h1, h2, h3]
  have hX1 : ∀ j, j < k → s1 (a + j) = lmb x j := fun j hj => by
    rw [s1o _ (by omega) (by omega) (by omega)]; exact hX j hj
  -- first comparison: x < lo
  obtain ⟨c1, c2⟩ := copyUp_value k (a + k + 4) a s1 (by omega)
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = aluRun (copyWords k (a + k + 4) a) s1 := ⟨_, rfl⟩
  rw [← hs2] at c1 c2
  have e3 : ∀ i, aluRun [ci 2 (a + k + 4 + k : Nat) (a + k + 2 : Nat) 0] s2 i =
      if i = a + k + 4 + k then s2 (a + k + 2) else s2 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_mov, slotUpd]
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = aluRun [ci 2 (a + k + 4 + k : Nat) (a + k + 2 : Nat) 0] s2 := ⟨_, rfl⟩
  have s3o : ∀ i, i ≠ a + k + 4 + k → s3 i = s2 i := fun i hi => by rw [hs3, e3]; simp [hi]
  have s3x : ∀ j, j < k + 1 → s3 (a + k + 4 + j) = lmb x j := fun j hj => by
    by_cases hjk : j < k
    · rw [s3o _ (by omega), c1 j hjk, hX1 j hjk]
    · have : j = k := by omega
      subst this
      rw [hs3, e3]; simp only [↓reduceIte]
      rw [c2 _ (Or.inl (by omega))]; exact s1E
  obtain ⟨l1, l2⟩ := wideLitFrom_value (a + k + 4 + (k + 1)) lo (k + 1) 0 s3
  obtain ⟨s4, hs4⟩ : ∃ s4, s4 = aluRun (wideLitC (k + 1) (a + k + 4 + (k + 1)) lo) s3 := ⟨_, rfl⟩
  have l1' : ∀ j, j < k + 1 → s4 (a + k + 4 + (k + 1) + j) = lmb lo j := fun j hj => by
    rw [hs4]; exact l1 j (by omega) (by omega)
  have l2' : ∀ i, (i < a + k + 4 + (k + 1) ∨ a + k + 4 + (k + 1) + (k + 1) + 1 ≤ i) → s4 i = s3 i := fun i hi => by
    rw [hs4]; exact l2 i (by omega)
  obtain ⟨w1⟩ : Nonempty (aluRun (wideLtC k (a + k + 4)) s4 (a + k + 4) = Runner.IR.bool (decide (x < lo))) :=
    ⟨wideLt_value k (a + k + 4) s4 x lo
      (fun j hj => by rw [l2' _ (Or.inl (by omega)), s3x j hj])
      (fun j hj => l1' j hj) (by omega) (by omega)⟩
  obtain ⟨s5, hs5⟩ : ∃ s5, s5 = aluRun (wideLtC k (a + k + 4)) s4 := ⟨_, rfl⟩
  rw [← hs5] at w1
  have s5o : ∀ i, (i < a + k + 4 ∨ a + k + 4 + 2 * (k + 1) + 7 ≤ i) → s5 i = s4 i := fun i hi => by
    rw [hs5]; exact wideLtC_frame k (a + k + 4) s4 i hi
  -- second comparison: hi < x
  obtain ⟨m1, m2⟩ := wideLitFrom_value (a + k + 4 + (2 * (k + 1) + 7)) hi (k + 1) 0 s5
  obtain ⟨s6, hs6⟩ : ∃ s6, s6 = aluRun (wideLitC (k + 1) (a + k + 4 + (2 * (k + 1) + 7)) hi) s5 := ⟨_, rfl⟩
  have m1' : ∀ j, j < k + 1 → s6 (a + k + 4 + (2 * (k + 1) + 7) + j) = lmb hi j := fun j hj => by
    rw [hs6]; exact m1 j (by omega) (by omega)
  have m2' : ∀ i, (i < a + k + 4 + (2 * (k + 1) + 7) ∨ a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + 1 ≤ i) →
      s6 i = s5 i := fun i hi => by
    rw [hs6]; exact m2 i (by omega)
  have s6x : ∀ j, j < k + 1 → s6 (a + j) = lmb x j ∨ j = k := fun j hj => by
    by_cases hjk : j < k
    · left
      rw [m2' _ (Or.inl (by omega)), s5o _ (Or.inl (by omega)), l2' _ (Or.inl (by omega)),
        s3o _ (by omega), c2 _ (Or.inl (by omega)), hX1 j hjk]
    · right; omega
  obtain ⟨d1, d2⟩ := copyUp_value k (a + k + 4 + (2 * (k + 1) + 7) + (k + 1)) a s6 (by omega)
  obtain ⟨s7, hs7⟩ : ∃ s7, s7 = aluRun (copyWords k (a + k + 4 + (2 * (k + 1) + 7) + (k + 1)) a) s6 := ⟨_, rfl⟩
  rw [← hs7] at d1 d2
  have e8 : ∀ i, aluRun [ci 2 (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k : Nat) (a + k + 2 : Nat) 0] s7 i =
      if i = a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k then s7 (a + k + 2) else s7 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_mov, slotUpd]
  obtain ⟨s8, hs8⟩ : ∃ s8, s8 = aluRun [ci 2 (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k : Nat) (a + k + 2 : Nat) 0] s7 :=
    ⟨_, rfl⟩
  have s8o : ∀ i, i ≠ a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k → s8 i = s7 i := fun i hi => by
    rw [hs8, e8]; simp [hi]
  have s7E : s7 (a + k + 2) = lmb x k := by
    rw [d2 _ (Or.inl (by omega)), m2' _ (Or.inl (by omega)), s5o _ (Or.inl (by omega)),
      l2' _ (Or.inl (by omega)), s3o _ (by omega), c2 _ (Or.inl (by omega))]
    exact s1E
  have s8x : ∀ j, j < k + 1 → s8 (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + j) = lmb x j := fun j hj => by
    by_cases hjk : j < k
    · rw [s8o _ (by omega), d1 j hjk]
      rcases s6x j hj with h | h
      · exact h
      · omega
    · have : j = k := by omega
      subst this
      rw [hs8, e8]; simp only [↓reduceIte]; exact s7E
  have s8h : ∀ j, j < k + 1 → s8 (a + k + 4 + (2 * (k + 1) + 7) + j) = lmb hi j := fun j hj => by
    rw [s8o _ (by omega), d2 _ (Or.inl (by omega)), m1' j hj]
  obtain ⟨w2⟩ : Nonempty (aluRun (wideLtC k (a + k + 4 + (2 * (k + 1) + 7))) s8
      (a + k + 4 + (2 * (k + 1) + 7)) = Runner.IR.bool (decide (hi < x))) :=
    ⟨wideLt_value k (a + k + 4 + (2 * (k + 1) + 7)) s8 hi x (fun j hj => s8h j hj)
      (fun j hj => by rw [show a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + j =
        a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + j from rfl]; exact s8x j hj) (by omega) (by omega)⟩
  obtain ⟨s9, hs9⟩ : ∃ s9, s9 = aluRun (wideLtC k (a + k + 4 + (2 * (k + 1) + 7))) s8 := ⟨_, rfl⟩
  rw [← hs9] at w2
  have s9o : ∀ i, (i < a + k + 4 + (2 * (k + 1) + 7) ∨ a + k + 4 + (2 * (k + 1) + 7) + 2 * (k + 1) + 7 ≤ i) →
      s9 i = s8 i := fun i hi => by
    rw [hs9]; exact wideLtC_frame k _ s8 i hi
  have e10 : ∀ i, aluRun [cn 9 (a + k + 3) (a + k + 4) (a + k + 4 + (2 * (k + 1) + 7))] s9 i =
      if i = a + k + 3 then s9 (a + k + 4) ||| s9 (a + k + 4 + (2 * (k + 1) + 7)) else s9 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_or, slotUpd]
  have run : aluRun (wideOutC k a lo hi) s =
      aluRun [cn 9 (a + k + 3) (a + k + 4) (a + k + 4 + (2 * (k + 1) + 7))] s9 := by
    simp only [wideOutC, aluRun_append]
    rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  have f1v : s9 (a + k + 4) = Runner.IR.bool (decide (x < lo)) := by
    rw [s9o _ (Or.inl (by omega)), s8o _ (by omega), d2 _ (Or.inl (by omega)), m2' _ (Or.inl (by omega))]
    rw [show s5 (a + k + 4) = _ from w1]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [run, e10]; simp only [↓reduceIte]
    rw [f1v, w2, bool_or]
  · rw [run, e10]
    simp only [show a + j ≠ a + k + 3 by omega, ↓reduceIte]
    rw [s9o _ (Or.inl (by omega)), s8o _ (by omega), d2 _ (Or.inl (by omega)), m2' _ (Or.inl (by omega)),
      s5o _ (Or.inl (by omega)), l2' _ (Or.inl (by omega)), s3o _ (by omega), c2 _ (Or.inl (by omega))]
    exact hX1 j hj

theorem wideOutC_aluIns {K : Nat} (k a : Nat) (lo hi : Int) (hk : 1 ≤ k) (hK : a + 5 * k + 22 ≤ K) :
    ∀ i ∈ wideOutC k a lo hi, AluIns K a i := by
  intro i hi'
  simp only [wideOutC, List.mem_append, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | hi'
  · exact AluIns.const (a + k) 0 (by omega) (by omega) (by decide)
  · exact AluIns.const (a + k + 1) 63 (by omega) (by omega) (by decide)
  · exact AluIns.bin 12 (a + k + 2) (a + (k - 1)) (a + k + 1) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 4 (a + k + 2) (a + k) (a + k + 2) _ rfl (by omega) (by omega) (by omega) (by omega)
  rcases hi' with (((((((hi' | rfl) | hi') | hi') | hi') | hi') | rfl) | hi') | rfl
  · exact copyWords_aluIns k (a + k + 4) a (by omega) (by omega) (by omega) i hi'
  · exact AluIns.mov (a + k + 4 + k) (a + k + 2) (by omega) (by omega) (by omega)
  · exact wideLitFrom_aluIns (K := K) (dl := a) (a := a + k + 4 + (k + 1)) lo (by omega) (k + 1) 0 (by omega) i hi'
  · exact (wideLtC_aluIns (K := K) (n := k) (a := a + k + 4) (by omega) i hi').mono (by omega)
  · exact wideLitFrom_aluIns (K := K) (dl := a) (a := a + k + 4 + (2 * (k + 1) + 7)) hi (by omega) (k + 1) 0 (by omega) i hi'
  · exact copyWords_aluIns k (a + k + 4 + (2 * (k + 1) + 7) + (k + 1)) a (by omega) (by omega) (by omega) i hi'
  · exact AluIns.mov (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k) (a + k + 2) (by omega) (by omega) (by omega)
  · exact (wideLtC_aluIns (K := K) (n := k) (a := a + k + 4 + (2 * (k + 1) + 7)) (by omega) i hi').mono (by omega)
  · exact AluIns.bin 9 (a + k + 3) (a + k + 4) (a + k + 4 + (2 * (k + 1) + 7)) _ rfl (by omega) (by omega)
      (by omega) (by omega)

variable [Kern]

/-- The multiword narrowing test: the flag word of `x ∉ [lo, hi]` replaces slot `a+k+3`; the operand is kept. -/
theorem wideOut_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat} (lo hi x : Int)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 5 * k + 22 ≤ K) (hk : 1 ≤ k)
    (hc : CodeAt m pc (wideOutC k a lo hi)) (hfar : CodeFar pc (wideOutC k a lo hi).length fp K)
    (hx1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x) (hx2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hl1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ lo) (hl2 : lo < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hh1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ hi) (hh2 : hi < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hxm : WordsAt m fp a (integerEncoding k x)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideOutC k a lo hi).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k x) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (a + k + 3))) = some (Runner.IR.bool (decide (x < lo ∨ hi < x))) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideOutC_aluIns k a lo hi hk hKa) (slotVal m fp) hv
  obtain ⟨v1, v2⟩ := wideOut_value k a lo hi x hk (slotVal m fp) hx1 hx2 hl1 hl2 hh1 hh2
    (fun j hj => slotVal_words hF (by omega) x hxm j hj)
  exact ⟨m', st, ag, words_of_slotVal (base := a) (k := k) x (by omega) _ rd v2, by rw [rd (a + k + 3) (by omega), v1]⟩

end Gabbro.Stage0.Senke
