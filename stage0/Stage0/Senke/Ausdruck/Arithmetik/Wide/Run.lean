/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Run.lean
  Subject:   Execution of the multiword add/subtract chain on actual memory.

  Layout for `k` limbs at slot `a`: operand one (and the result) in `a .. a+k-1`, operand two in
  `a+k .. a+2k-1`, then mask, carry and five scratch slots (`wideAddC`). The first operand is
  replaced by `x + y` resp. `x - y` modulo `2^(64k)`, exactly the canonical `integerEncoding k`;
  the second operand survives; only frame slots from `a` on change.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Add
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

variable [Kern]

/-- The word of slot `j`, as memory reads it. -/
def slotVal (m : Runner.Mem) (fp : Runner.W) (j : Nat) : Runner.W :=
  BitVec.ofNat 64 (le m (slot fp (BitVec.ofNat 64 j)) 8)

theorem slotVal_rd {m : Runner.Mem} {fp : Runner.W} {K j : Nat} (hF : FrameOK m fp K) (hj : j < K) :
    m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) := by
  simp only [Runner.Mem.rd64, slotVal, hF.rd j hj, ite_true]

/-- Canonical limbs in memory are the limbs the valuation reads. -/
theorem slotVal_words {m : Runner.Mem} {fp : Runner.W} {K k base : Nat} (hF : FrameOK m fp K)
    (hb : base + k ≤ K) (v : Int) (h : WordsAt m fp base (integerEncoding k v)) :
    ∀ j, j < k → slotVal m fp (base + j) = lmb v j := by
  intro j hj
  have h1 := h j (by simpa using hj)
  rw [slotVal_rd hF (by omega : base + j < K)] at h1
  rw [Option.some.inj h1, integerEncoding_get]

/-- The limbs a run leaves in memory, read back as canonical words. -/
theorem words_of_slotVal {m' : Runner.Mem} {fp : Runner.W} {K k base : Nat} (v : Int)
    (hb : base + k ≤ K) (s : Nat → Runner.W)
    (rd : ∀ j, j < K → m'.rd64 (slot fp (BitVec.ofNat 64 j)) = some (s j))
    (h : ∀ j, j < k → s (base + j) = lmb v j) : WordsAt m' fp base (integerEncoding k v) := by
  intro i hi
  have hi' : i < k := by simpa using hi
  rw [rd (base + i) (by omega), h i hi', integerEncoding_get]

theorem wideChain_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat} {mask carry : Int}
    (hcar : carry = 0 ∨ carry = 1) (hm : lit32 mask = true) (hcl : lit32 carry = true)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k + 7 ≤ K)
    (hc : CodeAt m pc (wideAddC k a mask carry))
    (hfar : CodeFar pc (wideAddC k a mask carry).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding k x)) (hy : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideAddC k a mask carry).length), fp⟩ m' ∧
      Agree fp a K m m' ∧
      (∀ j, j < k → m'.rd64 (slot fp (BitVec.ofNat 64 (a + j))) =
        some (BitVec.ofNat 64 (chainDig x y mask carry j))) ∧
      WordsAt m' fp (a + k) (integerEncoding k y) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideAddC_aluIns hm hcl hKa) (slotVal m fp) hv
  have hxs : ∀ j, j < k → slotVal m fp (a + j) = lmb x j := by
    intro j hj
    have h1 := hx j (by simpa using hj)
    rw [hv (a + j) (by omega)] at h1
    rw [Option.some.inj h1, integerEncoding_get]
  have hys : ∀ j, j < k → slotVal m fp (a + k + j) = lmb y j := by
    intro j hj
    have h1 := hy j (by simpa using hj)
    rw [hv (a + k + j) (by omega)] at h1
    rw [Option.some.inj h1, integerEncoding_get]
  obtain ⟨v1, v2⟩ := wideAddC_value k a mask carry hcar (slotVal m fp) x y hxs hys
  refine ⟨m', st, ag, fun j hj => ?_, fun i hi => ?_⟩
  · rw [rd (a + j) (by omega), v1 j hj]
  · have hi' : i < k := by simpa using hi
    rw [rd (a + k + i) (by omega), v2 (a + k + i) (Or.inr (Or.inr ⟨by omega, by omega⟩)), hys i hi',
      integerEncoding_get]

theorem wideAdd_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k + 7 ≤ K)
    (hc : CodeAt m pc (wideAddC k a 0 0))
    (hfar : CodeFar pc (wideAddC k a 0 0).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding k x)) (hy : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideAddC k a 0 0).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k (x + y)) ∧
      WordsAt m' fp (a + k) (integerEncoding k y) := by
  obtain ⟨m', st, ag, res, keep⟩ := wideChain_run (Or.inl rfl) (by decide) (by decide) hF hK hKa hc hfar x y hx hy
  refine ⟨m', st, ag, fun i hi => ?_, keep⟩
  have hi' : i < k := by simpa using hi
  rw [res i hi', integerEncoding_get, lmb_of_dval (chainDig_lt x y 0 0) (x + y) k (chainDig_add x y k) i hi']

theorem wideSub_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k + 7 ≤ K)
    (hc : CodeAt m pc (wideAddC k a (-1) 1))
    (hfar : CodeFar pc (wideAddC k a (-1) 1).length fp K) (x y : Int)
    (hx : WordsAt m fp a (integerEncoding k x)) (hy : WordsAt m fp (a + k) (integerEncoding k y)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideAddC k a (-1) 1).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k (x - y)) ∧
      WordsAt m' fp (a + k) (integerEncoding k y) := by
  obtain ⟨m', st, ag, res, keep⟩ := wideChain_run (Or.inr rfl) (by decide) (by decide) hF hK hKa hc hfar x y hx hy
  refine ⟨m', st, ag, fun i hi => ?_, keep⟩
  have hi' : i < k := by simpa using hi
  rw [res i hi', integerEncoding_get, lmb_of_dval (chainDig_lt x y (-1) 1) (x - y) k (chainDig_sub x y k) i hi']

end Gabbro.Stage0.Senke
