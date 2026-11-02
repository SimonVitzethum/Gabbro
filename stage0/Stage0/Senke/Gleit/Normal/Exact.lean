/- Lossless left normalization, capped at the binary64 subnormal floor. -/
module
public import Stage0.Senke.Gleit.Normal.Search
public import Stage0.Senke.Gleit.Round
public import Mathlib.Tactic.Linarith
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- Three guard bits put the hidden bit at position 55. The effective
    exponent index cannot decrease below one (the subnormal scale). -/
def routineLeftCount (magnitude index : Nat) : Nat :=
  min (56 - bitlen magnitude) (index - 1)

theorem routineLeftCount_bounds (n e : Nat) (low : 4 ≤ n) (high : n < 2 ^ 56)
    (ep : 1 ≤ e) :
    3 ≤ bitlen n ∧ bitlen n ≤ 56 ∧ routineLeftCount n e ≤ 53 ∧
      routineLeftCount n e < 64 ∧ routineLeftCount n e < e := by
  have upper := bitlen_obere n
  have lower := bitlen_untere n (by omega : n ≠ 0)
  have bl : 3 ≤ bitlen n := by
    by_contra h
    have p := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bitlen n ≤ 2 by omega)
    omega
  have bh : bitlen n ≤ 56 := by
    by_contra h
    have p := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 57 ≤ bitlen n by omega)
    omega
  have c₁ := Nat.min_le_left (56 - bitlen n) (e - 1)
  have c₂ := Nat.min_le_right (56 - bitlen n) (e - 1)
  exact ⟨bl, bh, by unfold routineLeftCount; omega,
    by unfold routineLeftCount; omega, by unfold routineLeftCount; omega⟩

/-- No leading bit is shifted past bit 55. If the hidden-bit target is not
    reached, the exponent has reached the subnormal floor instead. -/
theorem routineLeftCount_normalizes (n e : Nat) (low : 4 ≤ n)
    (high : n < 2 ^ 56) (ep : 1 ≤ e) :
    n * 2 ^ routineLeftCount n e < 2 ^ 56 ∧
      (2 ^ 55 ≤ n * 2 ^ routineLeftCount n e ∨ e - routineLeftCount n e = 1) := by
  obtain ⟨bl, bh, _, _, _⟩ := routineLeftCount_bounds n e low high ep
  have upper := bitlen_obere n
  have lower := bitlen_untere n (by omega : n ≠ 0)
  have predecessor : 2 ^ (bitlen n - 1) ≤ n := by
    rw [show bitlen n = bitlen n - 1 + 1 by omega, Nat.pow_succ] at lower
    omega
  have ck : routineLeftCount n e ≤ 56 - bitlen n := Nat.min_le_left _ _
  have product := Nat.mul_lt_mul_of_pos_right upper (Nat.two_pow_pos (routineLeftCount n e))
  have powers : 2 ^ bitlen n * 2 ^ routineLeftCount n e ≤ 2 ^ 56 := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨by omega, ?_⟩
  by_cases target : 56 - bitlen n ≤ e - 1
  · left
    have count : routineLeftCount n e = 56 - bitlen n := Nat.min_eq_left target
    have product := Nat.mul_le_mul_right (2 ^ routineLeftCount n e) predecessor
    have power : 2 ^ (bitlen n - 1) * 2 ^ routineLeftCount n e = 2 ^ 55 := by
      rw [← Nat.pow_add, count]
      congr 1
      omega
    rwa [power] at product
  · right
    have count : routineLeftCount n e = e - 1 := Nat.min_eq_right (by omega)
    omega

/-- Exact value preservation at a common nonnegative scale; the count bound
    prevents exponent subtraction from saturating. -/
theorem routineLeftCount_exact (n e : Nat) (ep : 1 ≤ e) :
    (n * 2 ^ routineLeftCount n e) * 2 ^ (e - routineLeftCount n e) = n * 2 ^ e := by
  have bound : routineLeftCount n e ≤ e := by
    have := Nat.min_le_right (56 - bitlen n) (e - 1)
    unfold routineLeftCount
    omega
  rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' bound]

/-- Exact cancellation arithmetic has zero guard tail. Left normalization
    preserves that tail, so rounding introduces no increment or lost bits. -/
theorem routineLeftCount_round_exact (n e : Nat) (tail : n % 8 = 0) :
    let normalized := n * 2 ^ routineLeftCount n e
    rundeInt (normalized / 8) (normalized % 8) 8 =
      (n / 8) * 2 ^ routineLeftCount n e := by
  dsimp only
  have zero : (n * 2 ^ routineLeftCount n e) % 8 = 0 := by
    rw [Nat.mul_mod, tail]
    simp
  rw [zero, rundeInt_fall _ 0 8 (by decide)]
  have initial := Nat.div_add_mod' n 8
  have shifted := Nat.div_add_mod' (n * 2 ^ routineLeftCount n e) 8
  rw [tail] at initial
  rw [zero] at shifted
  nlinarith

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The binary search supplies the exact shift count; one comparison caps
    it at the remaining exponent budget. -/
def routineLeftCountWord (a index : Runner.W) : Runner.W :=
  let count := routineLeadingZerosWord a - 8
  let budget := index - 1
  if count.ult budget then count else budget

def routineLeftCountL (d : Nat) (a index : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let count := fun j => wordK 4 j (routineLeadingZerosL j a) 8
  let budget := fun j => wordK 4 j (index j) 1
  routineChooseL d (fun j => routineLessL j count budget) count budget

theorem routineLeftCountL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a index : Nat → Option (List II × Nat)} {av ev : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (he : WordCode (L := L) ρ W index ev) :
    WordCode (L := L) ρ W (fun d => routineLeftCountL d a index) (routineLeftCountWord av ev) := by
  have count := WordCode.bin (routineLeadingZerosL_word ha) (WordCode.const 8 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have budget := WordCode.bin he (WordCode.const 1 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  exact routineChooseL_ok (routineLessL_ok count budget) (fun _ => count) (fun _ => budget)

theorem routineLeftCountL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a index : Nat → Option (List II × Nat)} {n e : Nat}
    (ha : WordCode (L := L) ρ W a (BitVec.ofNat 64 n))
    (he : WordCode (L := L) ρ W index (BitVec.ofNat 64 e))
    (low : 4 ≤ n) (high : n < 2 ^ 56) (ep : 1 ≤ e) (eb : e < 2 ^ 64) :
    WordCode (L := L) ρ W (fun d => routineLeftCountL d a index)
      (BitVec.ofNat 64 (routineLeftCount n e)) := by
  obtain ⟨bl, bh, _, _, _⟩ := routineLeftCount_bounds n e low high ep
  have nb : n < 2 ^ 64 := by omega
  have leading := routineLeadingZerosL_ok ha
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nb] at leading
  have count := WordCode.bin leading (WordCode.const 8 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have budget := WordCode.bin he (WordCode.const 1 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have countEq : BitVec.ofNat 64 (64 - bitlen n) - 8 = BitVec.ofNat 64 (56 - bitlen n) := by
    rw [show (8 : Runner.W) = BitVec.ofNat 64 8 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
    omega
  have budgetEq : BitVec.ofNat 64 e - 1 = BitVec.ofNat 64 (e - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) ep
  rw [countEq] at count
  rw [budgetEq] at budget
  have choose := routineChooseL_ok (routineLessL_ok count budget) (fun _ => count) (fun _ => budget)
  have compare : (BitVec.ofNat 64 (56 - bitlen n)).ult (BitVec.ofNat 64 (e - 1)) =
      decide (56 - bitlen n < e - 1) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 56 - bitlen n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : e - 1 < 2 ^ 64)]
  rw [compare] at choose
  by_cases small : 56 - bitlen n < e - 1
  · simpa only [small, decide_true, ite_true, routineLeftCount, Nat.min_eq_left (by omega)] using choose
  · simpa only [small, decide_false, Bool.false_eq_true, ite_false,
      routineLeftCount, Nat.min_eq_right (by omega)] using choose

/-- The actual IR left shift agrees with unbounded multiplication before
    rounding. Its denominator is never used to justify a modular wrap. -/
theorem routineLeftShiftL_exact {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a index : Nat → Option (List II × Nat)} {n e : Nat}
    (ha : WordCode (L := L) ρ W a (BitVec.ofNat 64 n))
    (he : WordCode (L := L) ρ W index (BitVec.ofNat 64 e))
    (low : 4 ≤ n) (high : n < 2 ^ 56) (ep : 1 ≤ e) (eb : e < 2 ^ 64) :
    WordCode (L := L) ρ W
      (fun d => wordL 11 d (a d) (routineLeftCountL (d + 1) a index))
      (BitVec.ofNat 64 (n * 2 ^ routineLeftCount n e)) ∧
    n * 2 ^ routineLeftCount n e < 2 ^ 56 := by
  have count := routineLeftCountL_ok ha he low high ep eb
  have bounds := routineLeftCount_bounds n e low high ep
  have shift := WordCode.bin ha count
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have exactShift : (BitVec.ofNat 64 n) <<< ((BitVec.ofNat 64 (routineLeftCount n e)).toNat % 64) =
      BitVec.ofNat 64 (n * 2 ^ routineLeftCount n e) := by
    have nb : n < 2 ^ 64 := by omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : routineLeftCount n e < 2 ^ 64),
      Nat.mod_eq_of_lt bounds.2.2.2.1, Nat.mod_eq_of_lt nb, Nat.shiftLeft_eq]
  rw [exactShift] at shift
  exact ⟨shift, (routineLeftCount_normalizes n e low high ep).1⟩

theorem routineLeftCount_zeuge :
    routineLeftCount 8 1023 = 52 ∧
    routineLeftCount 8 1 = 0 ∧
    routineLeftCount 8 3 = 2 ∧
    (8 * 2 ^ routineLeftCount 8 1023) = 2 ^ 55 ∧
    rundeInt ((8 * 2 ^ routineLeftCount 8 1023) / 8) 0 8 = 2 ^ 52 := by
  decide +kernel

#print axioms routineLeftCount_normalizes
#print axioms routineLeftCount_exact
#print axioms routineLeftCount_round_exact
#print axioms routineLeftCountL_ok
#print axioms routineLeftCountL_word
#print axioms routineLeftShiftL_exact
#print axioms routineLeftCount_zeuge
end Gabbro.Stage0.Senke
