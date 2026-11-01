/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/ComparePrep.lean
  Subject:   Copy and extend two operands to a common extra-limb comparison frame.

  Sources stay below r. The first extended operand occupies r .. r+k, the second r+k+1 .. r+2k+1.
  Extension temporaries may overlap the not yet copied second operand; no live limb is overwritten.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Extend
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

def wideComparePrep (sx sy : Bool) (k r p q : Nat) : List II :=
  copyWords k r p ++ wideExtendC sx k (k + 1) r ++
  copyWords k (r + (k + 1)) q ++ wideExtendC sy k (k + 1) (r + (k + 1))

theorem wideComparePrep_value (sx sy : Bool) (k r p q : Nat) (x y : Int) (hk : 1 ≤ k)
    (hp : p + k ≤ r) (hq : q + k ≤ r) (hx : WideFits sx k x) (hy : WideFits sy k y)
    (s : Nat → Runner.W) (hX : ∀ j, j < k → s (p + j) = lmb x j)
    (hY : ∀ j, j < k → s (q + j) = lmb y j) :
    (∀ j, j < k + 1 → aluRun (wideComparePrep sx sy k r p q) s (r + j) = lmb x j) ∧
    (∀ j, j < k + 1 → aluRun (wideComparePrep sx sy k r p q) s (r + (k + 1) + j) = lmb y j) ∧
    (∀ i, i < r ∨ r + 2 * (k + 1) + 3 ≤ i → aluRun (wideComparePrep sx sy k r p q) s i = s i) := by
  obtain ⟨c1, c2⟩ := copyUp_value k r p s hp
  let s1 := aluRun (copyWords k r p) s
  change ∀ j, j < k → s1 (r + j) = s (p + j) at c1
  change ∀ i, i < r ∨ r + k ≤ i → s1 i = s i at c2
  obtain ⟨e1, e2⟩ := wideExtend_value sx k (k + 1) r x hk (by omega) hx s1
    (fun j hj => (c1 j hj).trans (hX j hj))
  let s2 := aluRun (wideExtendC sx k (k + 1) r) s1
  change ∀ j, j < k + 1 → s2 (r + j) = lmb x j at e1
  change ∀ i, i < r ∨ r + (k + 1) + 3 ≤ i → s2 i = s1 i at e2
  obtain ⟨d1, d2⟩ := copyUp_value k (r + (k + 1)) q s2 (by omega)
  let s3 := aluRun (copyWords k (r + (k + 1)) q) s2
  change ∀ j, j < k → s3 (r + (k + 1) + j) = s2 (q + j) at d1
  change ∀ i, i < r + (k + 1) ∨ r + (k + 1) + k ≤ i → s3 i = s2 i at d2
  have hY3 : ∀ j, j < k → s3 (r + (k + 1) + j) = lmb y j := by
    intro j hj
    rw [d1 j hj, e2 _ (Or.inl (by omega)), c2 _ (Or.inl (by omega)), hY j hj]
  obtain ⟨f1, f2⟩ := wideExtend_value sy k (k + 1) (r + (k + 1)) y hk (by omega) hy s3 hY3
  have run : aluRun (wideComparePrep sx sy k r p q) s =
      aluRun (wideExtendC sy k (k + 1) (r + (k + 1))) s3 := by
    simp only [wideComparePrep, aluRun_append, s3, s2, s1]
  rw [run]
  refine ⟨fun j hj => ?_, f1, fun i hi => ?_⟩
  · rw [f2 _ (Or.inl (by omega)), d2 _ (Or.inl (by omega)), e1 j hj]
  · rw [f2 i (by omega), d2 i (by omega), e2 i (by omega), c2 i (by omega)]

theorem wideComparePrep_aluIns {K d k r p q : Nat} (sx sy : Bool) (hk : 1 ≤ k)
    (hd : d ≤ r) (hp : p + k ≤ r) (hq : q + k ≤ r) (hK : r + 2 * (k + 1) + 3 ≤ K) :
    ∀ i ∈ wideComparePrep sx sy k r p q, AluIns K d i := by
  intro i hi
  simp only [wideComparePrep, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · exact copyWords_aluIns k r p hd (by omega) (by omega) i hi
  · exact wideExtendC_aluIns sx hk (by omega) hd (by omega) i hi
  · exact copyWords_aluIns k (r + (k + 1)) q (by omega) (by omega) (by omega) i hi
  · exact wideExtendC_aluIns sy hk (by omega) (by omega) (by omega) i hi

/-- Full signed and unsigned domains both lie strictly inside the next limb's signed range. -/
theorem wideFits_bounds (signed : Bool) (k : Nat) (x : Int) (hk : 1 ≤ k) (hx : WideFits signed k x) :
    -(2 ^ (64 * k)) ≤ x ∧ x < 2 ^ (64 * k) := by
  have hp : (2 : Int) ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * (k - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hpos : (0 : Int) < 2 ^ (64 * (k - 1)) := by positivity
  cases signed <;> simp only [WideFits, Bool.false_eq_true, ↓reduceIte] at hx
  · have : (0 : Int) < 2 ^ (64 * k) := by positivity
    omega
  · rw [hp]
    constructor <;> omega

theorem wideCompare_difference (sx sy : Bool) (k : Nat) (x y : Int) (hk : 1 ≤ k)
    (hx : WideFits sx k x) (hy : WideFits sy k y) :
    -(2 ^ 63 * 2 ^ (64 * k)) ≤ x - y ∧ x - y < 2 ^ 63 * 2 ^ (64 * k) := by
  have xb := wideFits_bounds sx k x hk hx
  have yb := wideFits_bounds sy k y hk hy
  have hp : (0 : Int) < 2 ^ (64 * k) := by positivity
  constructor <;> omega

end Gabbro.Stage0.Senke
