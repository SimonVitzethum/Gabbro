/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/MulRows.lean
  Subject:   Schoolbook multiplication modulo `2^(64k)` as `k` accumulating rows.

  Layout for `k` limbs at slot `a`: multiplier digits `a .. a+k-1`, multiplicand digits
  `a+k .. a+2k-1`, accumulator `a+2k .. a+3k-1`, carry `a+3k`, scratch from `a+3k+1` (16 slots).
  Row `i` adds `x_i * Y * B^i` into the accumulator digits `i ..`; every row drops the carry out of
  digit `k-1`. The accumulator then holds `X * Y mod 2^(64k)`.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.MulChain
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Compare

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem dval_split (x : Nat → Nat) (i : Nat) : ∀ m, dval x (i + m) = dval x i + 2 ^ (64 * i) * dval (fun t => x (i + t)) m
  | 0 => by simp [dval]
  | m + 1 => by
    rw [← Nat.add_assoc, dval_succ, dval_split x i m, dval_succ, Nat.add_assoc]
    congr 1
    rw [show 64 * (i + m) = 64 * i + 64 * m by omega, Nat.pow_add]
    ring

theorem dval_smul (c : Nat) (y : Nat → Nat) : ∀ m, dval (fun j => c * y j) m = c * dval y m
  | 0 => by simp [dval]
  | m + 1 => by rw [dval_succ, dval_succ, dval_smul c y m, Nat.mul_add, Nat.mul_assoc]

theorem mod_bridge (A A' Z B c : Nat) (h : A' + B * c = A + Z) (hlt : A' < B) : A' = (A + Z) % B := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- One row: digits and the carry satisfy the multiply-accumulate identity. -/
theorem mulRowC_value (n X Y R c t : Nat) (s : Nat → Runner.W)
    (h1 : X < Y) (h2 : Y + n ≤ R) (h3 : R + n ≤ c) (h4 : c < t) :
    (∀ u, u < n → aluRun (mulRowC n X Y R c t) s (R + u) =
      BitVec.ofNat 64 (sumDig (xd s R) (ymd s X Y) 0 u)) ∧
    (∃ carry, dval (sumDig (xd s R) (ymd s X Y) 0) n + 2 ^ (64 * n) * carry =
      dval (xd s R) n + (s X).toNat * dval (fun u => (s (Y + u)).toNat) n) ∧
    (∀ j, (j < R ∨ R + n ≤ j) → j ≠ c → (j < t ∨ t + 15 < j) → aluRun (mulRowC n X Y R c t) s j = s j) := by
  set s0 := aluRun [ci 1 (c : Nat) 0 0] s with hs0
  have run : aluRun (mulRowC n X Y R c t) s = aluRun (mulRow n X Y R c t) s0 := by
    simp only [mulRowC, aluRun_cons, aluRun_nil, hs0]
  have vc : s0 c = 0 := by
    simp (disch := omega) only [hs0, aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
      slotUpd_same, slotUpd_other, ite_true]
    decide
  have vo : ∀ j, j ≠ c → s0 j = s j := by
    intro j hj
    simp (disch := omega) only [hs0, aluRun_cons, aluRun_nil, aluStep, aluVal, ci, Int.toNat_natCast,
      slotUpd_same, slotUpd_other]
  obtain ⟨r1, r2, r3⟩ := mulChain_run n X Y R c t s0 h1 h2 h3 h4
  have hx : ∀ u, u < n → xd s0 R u = xd s R u := fun u hu => by simp only [xd]; rw [vo _ (by omega)]
  have hy : ∀ u, u < n → ymd s0 X Y u = ymd s X Y u := fun u hu => by
    simp only [ymd]; rw [vo X (by omega), vo _ (by omega)]
  have hc0 : (s0 c).toNat = 0 := by rw [vc]; rfl
  rw [run]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [r1 u hu, hc0]
    congr 1
    apply sumDig_congr
    · intro i hi; exact hx i (by omega)
    · intro i hi; exact hy i (by omega)
  · refine ⟨carryAt (xd s R) (ymd s X Y) 0 n, ?_⟩
    have id := sum_identity (xd s R) (ymd s X Y) 0 n
    have e : dval (ymd s X Y) n = (s X).toNat * dval (fun u => (s (Y + u)).toNat) n := by
      exact dval_smul (s X).toNat (fun u => (s (Y + u)).toNat) n
    rw [e, Nat.add_zero] at id
    exact id
  · intro j h5 h6 h7
    rw [r3 j h5 h6 h7, vo j h6]

/-- The arithmetic of one row, on digit sequences alone. -/
theorem row_nat (k i n : Nat) (hk : i + n = k) (dR dR' xg yy : Nat → Nat) (xi carry : Nat)
    (hd : ∀ j, dR' j < 2 ^ 64) (hlow : ∀ j, j < i → dR' j = dR j)
    (hrow : dval (fun u => dR' (i + u)) n + 2 ^ (64 * n) * carry =
      dval (fun u => dR (i + u)) n + xi * dval yy n)
    (hI : dval dR k = (dval xg i * dval yy k) % 2 ^ (64 * k)) :
    dval dR' k = ((dval xg i + xi * 2 ^ (64 * i)) * dval yy k) % 2 ^ (64 * k) := by
  subst hk
  have lt : dval dR' (i + n) < 2 ^ (64 * (i + n)) := dval_lt hd _
  have e1 := dval_split dR' i n
  have e2 := dval_split dR i n
  have e3 := dval_split yy n i
  rw [Nat.add_comm n i] at e3
  have lowEq : dval dR' i = dval dR i := dval_congr (fun j hj => hlow j hj)
  rw [lowEq] at e1
  have hM : 2 ^ (64 * (i + n)) = 2 ^ (64 * i) * 2 ^ (64 * n) := by
    rw [Nat.mul_add, Nat.pow_add]
  have key : dval dR' (i + n) + 2 ^ (64 * (i + n)) * carry =
      dval dR (i + n) + 2 ^ (64 * i) * (xi * dval yy n) := by
    rw [e1, e2, hM]
    have := congrArg (fun z => 2 ^ (64 * i) * z) hrow
    nlinarith [this]
  have br := mod_bridge _ _ _ _ _ key lt
  rw [br, hI]
  -- (A + Z) % M = ((X + xi B^i) * Y) % M
  have split : dval yy (i + n) = dval yy n + 2 ^ (64 * n) * dval (fun u => yy (n + u)) i := by
    have := dval_split yy n i
    rw [Nat.add_comm n i] at this
    exact this
  rw [split]
  generalize dval yy n = Y1 at *
  generalize dval (fun u => yy (n + u)) i = Y2 at *
  generalize dval xg i = X0 at *
  generalize 2 ^ (64 * i) = Bi at *
  generalize 2 ^ (64 * n) = Bn at *
  rw [hM, Nat.mod_add_mod]
  have : (X0 + xi * Bi) * (Y1 + Bn * Y2) =
      (X0 * (Y1 + Bn * Y2) + Bi * (xi * Y1)) + (Bi * Bn) * (xi * Y2) := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-- The accumulator digits. -/
def accD (s : Nat → Runner.W) (k a : Nat) : Nat → Nat := fun u => (s (a + 2 * k + u)).toNat
/-- The multiplicand digits. -/
def mcD (s : Nat → Runner.W) (k a : Nat) : Nat → Nat := fun u => (s (a + k + u)).toNat

theorem mulRows_value (k a : Nat) : ∀ (m i : Nat) (s : Nat → Runner.W), m + i = k →
    dval (accD s k a) k = (dval (xd s a) i * dval (mcD s k a) k) % 2 ^ (64 * k) →
    dval (accD (aluRun (mulRows k a m i) s) k a) k =
      (dval (xd s a) k * dval (mcD s k a) k) % 2 ^ (64 * k) ∧
    ∀ j, j < a + 2 * k → aluRun (mulRows k a m i) s j = s j
  | 0, i, s, hmi, hI => by
    have : i = k := by omega
    subst this
    exact ⟨hI, fun j _ => rfl⟩
  | m + 1, i, s, hmi, hI => by
    obtain ⟨v1, ⟨carry, v2⟩, v3⟩ := mulRowC_value (m + 1) (a + i) (a + k) (a + 2 * k + i) (a + 3 * k)
      (a + 3 * k + 1) s (by omega) (by omega) (by omega) (by omega)
    set s1 := aluRun (mulRowC (m + 1) (a + i) (a + k) (a + 2 * k + i) (a + 3 * k) (a + 3 * k + 1)) s with hs1
    have fr : ∀ j, j < a + 2 * k + i → s1 j = s j := fun j hj => v3 j (by omega) (by omega) (by omega)
    have hd : ∀ j, accD s1 k a j < 2 ^ 64 := fun j => (s1 _).isLt
    have hlow : ∀ j, j < i → accD s1 k a j = accD s k a j := fun j hj => by
      simp only [accD]; rw [fr _ (by omega)]
    have dig : ∀ u, u < m + 1 → accD s1 k a (i + u) = sumDig (xd s (a + 2 * k + i)) (ymd s (a + i) (a + k)) 0 u := by
      intro u hu
      simp only [accD]
      rw [show a + 2 * k + (i + u) = a + 2 * k + i + u by omega, v1 u hu, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (sumDig_lt _ _ _ _)]
    have hrow : dval (fun u => accD s1 k a (i + u)) (m + 1) + 2 ^ (64 * (m + 1)) * carry =
        dval (fun u => accD s k a (i + u)) (m + 1) + (s (a + i)).toNat * dval (fun u => mcD s k a u) (m + 1) := by
      have e1 : dval (fun u => accD s1 k a (i + u)) (m + 1) =
          dval (sumDig (xd s (a + 2 * k + i)) (ymd s (a + i) (a + k)) 0) (m + 1) :=
        dval_congr (fun u hu => dig u hu)
      have e2 : dval (fun u => accD s k a (i + u)) (m + 1) = dval (xd s (a + 2 * k + i)) (m + 1) :=
        dval_congr (fun u hu => by
          simp only [accD, xd]; rw [show a + 2 * k + (i + u) = a + 2 * k + i + u by omega])
      have e3 : dval (fun u => (s (a + k + u)).toNat) (m + 1) = dval (fun u => mcD s k a u) (m + 1) := rfl
      rw [e1, e2, ← e3]
      exact v2
    have step := row_nat k i (m + 1) (by omega) (accD s k a) (accD s1 k a) (xd s a) (mcD s k a)
      (s (a + i)).toNat carry hd hlow hrow hI
    have xr : ∀ j, j < a + 2 * k → s1 j = s j := fun j hj => fr j (by omega)
    have c1 : dval (xd s1 a) (i + 1) = dval (xd s a) i + (s (a + i)).toNat * 2 ^ (64 * i) := by
      rw [dval_congr (y := xd s a) (fun j hj => by simp only [xd]; rw [xr _ (by omega)]), dval_succ]
      simp only [xd, Nat.add_zero]
    have c2 : dval (mcD s1 k a) k = dval (mcD s k a) k :=
      dval_congr (fun j hj => by simp only [mcD]; rw [xr _ (by omega)])
    have hI' : dval (accD s1 k a) k = (dval (xd s1 a) (i + 1) * dval (mcD s1 k a) k) % 2 ^ (64 * k) := by
      rw [c1, c2]; exact step
    have hs : aluRun (mulRows k a (m + 1) i) s = aluRun (mulRows k a m (i + 1)) s1 := by
      simp only [mulRows, aluRun_append, hs1]
    obtain ⟨r1, r2⟩ := mulRows_value k a m (i + 1) s1 (by omega) hI'
    rw [hs]
    refine ⟨?_, fun j hj => by rw [r2 j hj, xr j hj]⟩
    rw [r1, dval_congr (y := xd s a) (fun j hj => by simp only [xd]; rw [xr _ (by omega)]), c2]

/-! ## Zeroing, copying and the whole product -/

theorem zeroSlots_value : ∀ (n r : Nat) (s : Nat → Runner.W),
    (∀ j, j < n → aluRun (zeroSlotsC n r) s (r + j) = 0) ∧
    (∀ j, (j < r ∨ r + n ≤ j) → aluRun (zeroSlotsC n r) s j = s j)
  | 0, r, s => ⟨fun j hj => absurd hj (by omega), fun j _ => rfl⟩
  | n + 1, r, s => by
    obtain ⟨i1, i2⟩ := zeroSlots_value n (r + 1) (aluStep (ci 1 (r : Nat) 0 0) s)
    have st : ∀ j, j ≠ r → aluStep (ci 1 (r : Nat) 0 0) s j = s j := fun j hj =>
      slotUpd_other _ _ hj
    have sr : aluStep (ci 1 (r : Nat) 0 0) s r = 0 := by
      show slotUpd s r (BitVec.ofInt 64 0) r = 0
      rw [slotUpd_same]; exact BitVec.eq_of_toNat_eq (by simp)
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp only [zeroSlotsC, aluRun_cons]
      cases j with
      | zero =>
        show aluRun (zeroSlotsC n (r + 1)) (aluStep (ci 1 (r : Nat) 0 0) s) r = 0
        rw [i2 r (by omega), sr]
      | succ j => rw [show r + (j + 1) = r + 1 + j by omega]; exact i1 j (by omega)
    · simp only [zeroSlotsC, aluRun_cons]
      rw [i2 j (by omega), st j (by omega)]

theorem copyWords_value : ∀ (n dst src : Nat) (s : Nat → Runner.W), dst + n ≤ src →
    (∀ j, j < n → aluRun (copyWords n dst src) s (dst + j) = s (src + j)) ∧
    (∀ j, (j < dst ∨ dst + n ≤ j) → aluRun (copyWords n dst src) s j = s j)
  | 0, dst, src, s, _ => ⟨fun j hj => absurd hj (by omega), fun j _ => rfl⟩
  | n + 1, dst, src, s, h => by
    obtain ⟨i1, i2⟩ := copyWords_value n (dst + 1) (src + 1) (aluStep ⟨2, dst, src, 0⟩ s) (by omega)
    have st : ∀ j, j ≠ dst → aluStep ⟨2, dst, src, 0⟩ s j = s j := fun j hj => slotUpd_other _ _ hj
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp only [copyWords, aluRun_cons]
      cases j with
      | zero =>
        show aluRun (copyWords n (dst + 1) (src + 1)) (aluStep ⟨2, dst, src, 0⟩ s) dst = s src
        rw [i2 dst (by omega)]
        show slotUpd s dst (s src) dst = s src
        rw [slotUpd_same]
      | succ j =>
        rw [show dst + (j + 1) = dst + 1 + j by omega, i1 j (by omega), st _ (by omega)]
        rw [show src + (j + 1) = src + 1 + j by omega]
    · simp only [copyWords, aluRun_cons]
      rw [i2 j (by omega), st j (by omega)]

theorem mul_mod_toNat (x y M : Int) (hM : 0 < M) :
    ((x % M).toNat * (y % M).toNat) % M.toNat = ((x * y) % M).toNat := by
  have hx := Int.emod_nonneg x hM.ne'
  have hy := Int.emod_nonneg y hM.ne'
  have hs := Int.emod_nonneg (x * y) hM.ne'
  have hMt : ((M.toNat : Nat) : Int) = M := Int.toNat_of_nonneg hM.le
  have hxt : (((x % M).toNat : Nat) : Int) = x % M := Int.toNat_of_nonneg hx
  have hyt : (((y % M).toNat : Nat) : Int) = y % M := Int.toNat_of_nonneg hy
  have hst : ((((x * y) % M).toNat : Nat) : Int) = (x * y) % M := Int.toNat_of_nonneg hs
  have : ((((x % M).toNat * (y % M).toNat) % M.toNat : Nat) : Int) = (((x * y) % M).toNat : Nat) := by
    rw [Int.natCast_mod, Int.natCast_mul, hMt, hxt, hyt, hst, ← Int.mul_emod]
  exact_mod_cast this

theorem wideMul_value (k a : Nat) (s : Nat → Runner.W) (x y : Int)
    (hx : ∀ j, j < k → s (a + j) = lmb x j) (hy : ∀ j, j < k → s (a + k + j) = lmb y j) :
    (∀ j, j < k → aluRun (wideMulC k a) s (a + j) = lmb (x * y) j) ∧
    (∀ j, (a + k ≤ j ∧ j < a + 2 * k) → aluRun (wideMulC k a) s j = s j) := by
  obtain ⟨z1, z2⟩ := zeroSlots_value k (a + 2 * k) s
  generalize hs0 : aluRun (zeroSlotsC k (a + 2 * k)) s = s0 at z1 z2
  have xs : ∀ j, j < a + 2 * k → s0 j = s j := fun j hj => z2 j (Or.inl hj)
  have hI : dval (accD s0 k a) k = (dval (xd s0 a) 0 * dval (mcD s0 k a) k) % 2 ^ (64 * k) := by
    have : dval (accD s0 k a) k = 0 := by
      rw [dval_congr (y := fun _ => 0) (fun j hj => by simp only [accD]; rw [z1 j hj]; rfl)]
      exact dval_zero_seq k
    rw [this]; simp [dval]
  obtain ⟨m1, m2⟩ := mulRows_value k a k 0 s0 (by omega) hI
  generalize hs1 : aluRun (mulRows k a k 0) s0 = s1 at m1 m2
  have hxd : dval (xd s0 a) k = (x % 2 ^ (64 * k)).toNat := by
    rw [← dval_lmb x k]
    exact dval_congr (fun j hj => by simp only [xd]; rw [xs _ (by omega), hx j hj])
  have hmc : dval (mcD s0 k a) k = (y % 2 ^ (64 * k)).toNat := by
    rw [← dval_lmb y k]
    exact dval_congr (fun j hj => by simp only [mcD]; rw [xs _ (by omega), hy j hj])
  rw [hxd, hmc, ← two_pow_toNat k, mul_mod_toNat x y _ (by positivity)] at m1
  obtain ⟨c1, c2⟩ := copyWords_value k a (a + 2 * k) s1 (by omega)
  have run : aluRun (wideMulC k a) s = aluRun (copyWords k a (a + 2 * k)) s1 := by
    simp only [wideMulC, aluRun_append, hs0, hs1]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  swap
  · rw [run, c2 j (Or.inr (by omega)), m2 j (by omega), xs j (by omega)]
  rw [run, c1 j hj]
  have := lmb_of_dval (fun u => (s1 (a + 2 * k + u)).isLt) (x * y) k m1 j hj
  rw [← this]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s1 (a + 2 * k + j)).isLt]

end Gabbro.Stage0.Senke
