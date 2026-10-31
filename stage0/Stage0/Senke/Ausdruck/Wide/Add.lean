/-
  File:      stage0/Stage0/Senke/Ausdruck/Wide/Add.lean
  Subject:   Multiword addition and subtraction over the canonical integer encoding.

  `wideAdd_run` and `wideSub_run`: from two canonical `k`-limb operands (`WordsAt` of
  `integerEncoding k x` and `integerEncoding k y`) the actual IR execution of the carry chain reaches
  memory holding `integerEncoding k (x + y)` resp. `integerEncoding k (x - y)` in the first operand's
  limbs, changing only frame slots from `a` on.
-/
import Stage0.Senke.Ausdruck.Wide.Link
import Stage0.Senke.Ausdruck.Wide.AddChain

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem dval_inj {x y : Nat → Nat} (hx : ∀ j, x j < 2 ^ 64) (hy : ∀ j, y j < 2 ^ 64) :
    ∀ k, dval x k = dval y k → ∀ j, j < k → x j = y j
  | 0, _, j, hj => absurd hj (by omega)
  | k + 1, h, j, hj => by
    have lx := dval_lt hx k
    have ly := dval_lt hy k
    have hp : 0 < 2 ^ (64 * k) := by positivity
    rw [dval_succ, dval_succ] at h
    have hd : (dval x k + x k * 2 ^ (64 * k)) / 2 ^ (64 * k) =
        (dval y k + y k * 2 ^ (64 * k)) / 2 ^ (64 * k) := by rw [h]
    have hm : (dval x k + x k * 2 ^ (64 * k)) % 2 ^ (64 * k) =
        (dval y k + y k * 2 ^ (64 * k)) % 2 ^ (64 * k) := by rw [h]
    rw [Nat.add_mul_div_right _ _ hp, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt lx,
      Nat.div_eq_of_lt ly] at hd
    rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt lx,
      Nat.mod_eq_of_lt ly] at hm
    by_cases e : j = k
    · subst e; omega
    · exact dval_inj hx hy k hm j (by omega)

theorem lmb_lt (v : Int) (j : Nat) : (lmb v j).toNat < 2 ^ 64 := (lmb v j).isLt

/-- A digit sequence with the value of `v mod 2^(64k)` carries exactly the limbs of `v`. -/
theorem lmb_of_dval {d : Nat → Nat} (hd : ∀ j, d j < 2 ^ 64) (v : Int) (k : Nat)
    (h : dval d k = (v % 2 ^ (64 * k)).toNat) : ∀ j, j < k → BitVec.ofNat 64 (d j) = lmb v j := by
  intro j hj
  have e := dval_inj hd (lmb_lt v) k (h.trans (dval_lmb v k).symm) j hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt (lmb_lt v j)]

theorem add_mod_toNat (x y M : Int) (hM : 0 < M) :
    ((x % M).toNat + (y % M).toNat) % M.toNat = ((x + y) % M).toNat := by
  have hx := Int.emod_nonneg x hM.ne'
  have hy := Int.emod_nonneg y hM.ne'
  have hs := Int.emod_nonneg (x + y) hM.ne'
  have hMt : ((M.toNat : Nat) : Int) = M := Int.toNat_of_nonneg hM.le
  have hxt : (((x % M).toNat : Nat) : Int) = x % M := Int.toNat_of_nonneg hx
  have hyt : (((y % M).toNat : Nat) : Int) = y % M := Int.toNat_of_nonneg hy
  have hst : ((((x + y) % M).toNat : Nat) : Int) = (x + y) % M := Int.toNat_of_nonneg hs
  have : ((((x % M).toNat + (y % M).toNat) % M.toNat : Nat) : Int) = (((x + y) % M).toNat : Nat) := by
    rw [Int.natCast_mod, Int.natCast_add, hMt, hxt, hyt, hst, Int.add_emod x y M]
  exact_mod_cast this

/-! ## Admitted instructions -/

theorem addLimbC_aluIns {K d A B m c t : Nat} (hA : d ≤ A) (hAK : A < K) (hB : B < K) (hm : m < K)
    (hc : c < K) (hdc : d ≤ c) (hdt : d ≤ t) (ht : t + 4 < K) :
    ∀ i ∈ addLimbC A B m c t, AluIns K d i := by
  intro i hi
  simp only [addLimbC, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AluIns.bin 10 t B m _ rfl hdt (by omega) hB hm
  · exact AluIns.bin 3 (t + 1) A t _ rfl (by omega) (by omega) hAK (by omega)
  · exact AluIns.bin 27 (t + 2) (t + 1) A _ rfl (by omega) (by omega) (by omega) hAK
  · exact AluIns.bin 3 (t + 3) (t + 1) c _ rfl (by omega) (by omega) (by omega) hc
  · exact AluIns.bin 27 (t + 4) (t + 3) (t + 1) _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.mov A (t + 3) hA hAK (by omega)
  · exact AluIns.bin 9 c (t + 2) (t + 4) _ rfl hdc hc (by omega) (by omega)

theorem addChain_aluIns {K d m c t : Nat} (hm : m < K) (hc : c < K) (hdc : d ≤ c) (hdt : d ≤ t)
    (ht : t + 4 < K) : ∀ (n a b : Nat), d ≤ a → a + n ≤ K → b + n ≤ K →
      ∀ i ∈ addChain n a b m c t, AluIns K d i
  | 0, _, _, _, _, _, i, hi => by simp [addChain] at hi
  | n + 1, a, b, hda, ha, hb, i, hi => by
    simp only [addChain, List.mem_append] at hi
    rcases hi with hi | hi
    · exact addLimbC_aluIns hda (by omega) (by omega) hm hc hdc hdt ht i hi
    · exact addChain_aluIns hm hc hdc hdt ht n (a + 1) (b + 1) (by omega) (by omega) (by omega) i hi

theorem wideAddC_aluIns {K k a : Nat} {mask carry : Int} (hm : lit32 mask = true)
    (hc : lit32 carry = true) (hK : a + 2 * k + 7 ≤ K) :
    ∀ i ∈ wideAddC k a mask carry, AluIns K a i := by
  intro i hi
  simp only [wideAddC, List.cons_append, List.nil_append, List.mem_cons] at hi
  rcases hi with rfl | rfl | hi
  · exact AluIns.const (a + 2 * k) mask (by omega) (by omega) hm
  · exact AluIns.const (a + 2 * k + 1) carry (by omega) (by omega) hc
  · exact addChain_aluIns (K := K) (d := a) (by omega) (by omega) (by omega) (by omega) (by omega)
      k a (a + k) (by omega) (by omega) (by omega) i hi

/-! ## The chain on a valuation -/

/-- The digits an add (`mask = 0`, `carry = 0`) or subtract (`mask = -1`, `carry = 1`) chain
    produces from the canonical limbs of `x` and `y`. -/
def chainDig (x y mask carry : Int) : Nat → Nat :=
  sumDig (fun i => (lmb x i).toNat) (fun i => (lmb y i ^^^ BitVec.ofInt 64 mask).toNat)
    (BitVec.ofInt 64 carry).toNat

theorem chainDig_lt (x y mask carry : Int) (j : Nat) : chainDig x y mask carry j < 2 ^ 64 :=
  sumDig_lt _ _ _ _

theorem wideAddC_value (k a : Nat) (mask carry : Int) (hcar : carry = 0 ∨ carry = 1)
    (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < k → s (a + j) = lmb x j) (hy : ∀ j, j < k → s (a + k + j) = lmb y j) :
    (∀ j, j < k → aluRun (wideAddC k a mask carry) s (a + j) =
      BitVec.ofNat 64 (chainDig x y mask carry j)) ∧
    (∀ j, (j < a ∨ a + 2 * k + 7 ≤ j ∨ (a + k ≤ j ∧ j < a + 2 * k)) →
      aluRun (wideAddC k a mask carry) s j = s j) := by
  set s0 := aluRun [ci 1 (a + 2 * k : Nat) mask 0, ci 1 (a + 2 * k + 1 : Nat) carry 0] s with hs0
  have run : aluRun (wideAddC k a mask carry) s =
      aluRun (addChain k a (a + k) (a + 2 * k) (a + 2 * k + 1) (a + 2 * k + 2)) s0 := by
    simp only [wideAddC, aluRun_append, hs0]
  have vm : s0 (a + 2 * k) = BitVec.ofInt 64 mask := by
    simp (disch := omega) only [hs0, aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
      slotUpd_same, slotUpd_other, ite_true]
  have vc : s0 (a + 2 * k + 1) = BitVec.ofInt 64 carry := by
    simp (disch := omega) only [hs0, aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
      slotUpd_same, slotUpd_other, ite_true]
  have vo : ∀ j, j ≠ a + 2 * k → j ≠ a + 2 * k + 1 → s0 j = s j := by
    intro j h1 h2
    simp (disch := omega) only [hs0, aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
      slotUpd_same, slotUpd_other]
  have c1 : (s0 (a + 2 * k + 1)).toNat ≤ 1 := by
    rw [vc]; rcases hcar with rfl | rfl <;> decide
  obtain ⟨r1, r2, r3, r4⟩ := addChain_run k a (a + k) (a + 2 * k) (a + 2 * k + 1) (a + 2 * k + 2) s0
    (by omega) (by omega) (by omega) (by omega) c1
  rw [run]
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [r1 j hj, vc]
    congr 1
    apply sumDig_congr
    · intro i hi
      simp only [xd]
      rw [vo (a + i) (by omega) (by omega), hx i (by omega)]
    · intro i hi
      simp only [yd]
      rw [vo (a + k + i) (by omega) (by omega), vm, hy i (by omega)]
  · intro j hj
    rw [r4 j (by omega) (by omega) (by omega), vo j (by omega) (by omega)]

/-! ## Values of the produced digits -/

theorem two_pow_toNat (k : Nat) : ((2 : Int) ^ (64 * k)).toNat = 2 ^ (64 * k) := by
  rw [Int.toNat_pow_of_nonneg (by norm_num)]; rfl

theorem dval_compl {d : Nat → Nat} (hd : ∀ j, d j < 2 ^ 64) :
    ∀ k, dval (fun j => 2 ^ 64 - 1 - d j) k + dval d k + 1 = 2 ^ (64 * k)
  | 0 => by simp [dval]
  | k + 1 => by
    have ih := dval_compl hd k
    have h := hd k
    have e : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    simp only [dval_succ]
    rw [e]
    generalize 2 ^ (64 * k) = P at *
    generalize 2 ^ 64 = N at *
    obtain ⟨q, hq⟩ : ∃ q, q = N - 1 - d k := ⟨_, rfl⟩
    have hq2 : q + d k + 1 = N := by omega
    rw [← hq]
    have : (q + d k + 1) * P = N * P := by rw [hq2]
    nlinarith

theorem chainDig_add (x y : Int) (k : Nat) :
    dval (chainDig x y 0 0) k = ((x + y) % 2 ^ (64 * k)).toNat := by
  have h0 : BitVec.ofInt 64 0 = 0 := BitVec.eq_of_toNat_eq (by simp)
  have hx : ∀ j, (fun i => (lmb x i).toNat) j < 2 ^ 64 := lmb_lt x
  have hy : ∀ j, (fun i => (lmb y i ^^^ BitVec.ofInt 64 0).toNat) j < 2 ^ 64 := fun j => BitVec.isLt _
  simp only [chainDig]
  rw [dval_sum hx hy, dval_lmb, h0]
  have hy0 : (fun i => (lmb y i ^^^ (0 : BitVec 64)).toNat) = fun i => (lmb y i).toNat := by
    funext i; simp
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [hy0, dval_lmb, hz, Nat.add_zero, ← two_pow_toNat k]
  exact add_mod_toNat x y _ (by positivity)

theorem sub_mod_toNat (x y M : Int) (hM : 0 < M) :
    ((x % M).toNat + (M.toNat - 1 - (y % M).toNat) + 1) % M.toNat = ((x - y) % M).toNat := by
  have hx := Int.emod_nonneg x hM.ne'
  have hy := Int.emod_nonneg y hM.ne'
  have hs := Int.emod_nonneg (x - y) hM.ne'
  have hyl := Int.emod_lt_of_pos y hM
  have hMt : ((M.toNat : Nat) : Int) = M := Int.toNat_of_nonneg hM.le
  have hxt : (((x % M).toNat : Nat) : Int) = x % M := Int.toNat_of_nonneg hx
  have hyt : (((y % M).toNat : Nat) : Int) = y % M := Int.toNat_of_nonneg hy
  have hst : ((((x - y) % M).toNat : Nat) : Int) = (x - y) % M := Int.toNat_of_nonneg hs
  have hlt : (y % M).toNat < M.toNat := by omega
  have e : (x % M).toNat + (M.toNat - 1 - (y % M).toNat) + 1 = ((x % M).toNat + M.toNat) - (y % M).toNat := by
    omega
  rw [e]
  have : ((((x % M).toNat + M.toNat - (y % M).toNat) % M.toNat : Nat) : Int) =
      (((x - y) % M).toNat : Nat) := by
    rw [Int.natCast_mod, Int.natCast_sub (by omega), Int.natCast_add, hMt, hxt, hyt, hst]
    calc (x % M + M - y % M) % M = ((x % M - y % M) + M) % M := by congr 1; omega
      _ = (x % M - y % M) % M := by simp
      _ = (x - y) % M := (Int.sub_emod x y M).symm
  exact_mod_cast this

theorem ofInt_minus_one : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem chainDig_sub (x y : Int) (k : Nat) :
    dval (chainDig x y (-1) 1) k = ((x - y) % 2 ^ (64 * k)).toNat := by
  have h1 : (BitVec.ofInt 64 1).toNat = 1 := by simp
  have hc : (fun i => (lmb y i ^^^ BitVec.ofInt 64 (-1)).toNat) =
      fun i => 2 ^ 64 - 1 - (lmb y i).toNat := by
    funext i
    rw [ofInt_minus_one, BitVec.xor_allOnes, BitVec.toNat_not]
  have hx : ∀ j, (fun i => (lmb x i).toNat) j < 2 ^ 64 := lmb_lt x
  have hy : ∀ j, (fun i => 2 ^ 64 - 1 - (lmb y i).toNat) j < 2 ^ 64 := fun j => by
    have := lmb_lt y j; simp only; omega
  simp only [chainDig]
  rw [hc, h1, dval_sum hx hy, dval_lmb]
  have hcomp := dval_compl (lmb_lt y) k
  rw [dval_lmb] at hcomp
  have e : dval (fun j => 2 ^ 64 - 1 - (lmb y j).toNat) k = 2 ^ (64 * k) - 1 - (y % 2 ^ (64 * k)).toNat := by
    omega
  rw [e, ← two_pow_toNat k]
  exact sub_mod_toNat x y _ (by positivity)

end Gabbro.Stage0.Senke
