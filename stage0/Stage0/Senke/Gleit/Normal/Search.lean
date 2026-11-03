/- Six-step binary search for the leading bit of a binary64 magnitude. -/
module
public import Stage0.Senke.Gleit.Routine.RoutineBranch
public import Stage0.Senke.Gleit.BitLength
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- Each step halves the remaining exponent interval. Zero is handled by
    the caller; the search itself returns zero for both zero and one. -/
def routineTopNat : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, a =>
    if a < 2 ^ (2 ^ fuel) then routineTopNat fuel a
    else 2 ^ fuel + routineTopNat fuel (a / 2 ^ (2 ^ fuel))

/-- The search locates the leading bit, with no floating-point assumptions. -/
theorem routineTopNat_bounds (fuel a : Nat) (ha : 0 < a)
    (bound : a < 2 ^ (2 ^ fuel)) :
    routineTopNat fuel a < 2 ^ fuel ∧
      2 ^ routineTopNat fuel a ≤ a ∧ a < 2 ^ (routineTopNat fuel a + 1) := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.pow_zero] at bound
    simp only [routineTopNat, Nat.pow_zero]
    omega
  | succ fuel ih =>
    by_cases small : a < 2 ^ (2 ^ fuel)
    · rw [routineTopNat, if_pos small]
      obtain ⟨hi, lo, up⟩ := ih a ha small
      have step : 2 ^ fuel ≤ 2 ^ (fuel + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact ⟨by omega, lo, up⟩
    · rw [routineTopNat, if_neg small]
      have dp : 0 < 2 ^ (2 ^ fuel) := Nat.two_pow_pos _
      have qp : 0 < a / 2 ^ (2 ^ fuel) := by
        have h := (Nat.le_div_iff_mul_le dp).mpr (show 1 * 2 ^ (2 ^ fuel) ≤ a by omega)
        omega
      have square : 2 ^ (2 ^ (fuel + 1)) =
          2 ^ (2 ^ fuel) * 2 ^ (2 ^ fuel) := by
        rw [Nat.pow_succ, show 2 ^ fuel * 2 = 2 ^ fuel + 2 ^ fuel by omega,
          Nat.pow_add]
      have qb : a / 2 ^ (2 ^ fuel) < 2 ^ (2 ^ fuel) :=
        (Nat.div_lt_iff_lt_mul dp).mpr (by simpa only [square] using bound)
      obtain ⟨hi, lo, up⟩ := ih _ qp qb
      have low := (Nat.le_div_iff_mul_le dp).mp lo
      have high := (Nat.div_lt_iff_lt_mul dp).mp up
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.pow_succ]
        omega
      · simpa only [Nat.pow_add, Nat.mul_comm] using low
      · simpa only [show 2 ^ fuel + routineTopNat fuel (a / 2 ^ (2 ^ fuel)) + 1 =
            2 ^ fuel + (routineTopNat fuel (a / 2 ^ (2 ^ fuel)) + 1) by omega,
          Nat.pow_add, Nat.mul_comm] using high

def routineTopWordAux : Nat → Runner.W → Runner.W
  | 0, _ => 0
  | fuel + 1, a =>
    if (a >>> (2 ^ fuel)) == 0 then routineTopWordAux fuel a
    else BitVec.ofNat 64 (2 ^ fuel) + routineTopWordAux fuel (a >>> (2 ^ fuel))

theorem routineTopWordAux_model (fuel : Nat) (a : Runner.W) :
    routineTopWordAux fuel a = BitVec.ofNat 64 (routineTopNat fuel a.toNat) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    have zero : ((a >>> (2 ^ fuel)) == 0) = decide (a.toNat < 2 ^ (2 ^ fuel)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, BitVec.toNat_eq,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decide_eq_true_eq]
      change a.toNat / 2 ^ (2 ^ fuel) = 0 ↔ a.toNat < 2 ^ (2 ^ fuel)
      rw [Nat.div_eq_zero_iff, or_iff_right (Nat.ne_of_gt (Nat.two_pow_pos _))]
    simp only [routineTopWordAux, routineTopNat, zero]
    by_cases small : a.toNat < 2 ^ (2 ^ fuel)
    · simp only [small, decide_true, ite_true, ih]
    · simp only [small, decide_false, Bool.false_eq_true, ite_false, ih,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.ofNat_add]

/-- Six comparisons cover every 64-bit word. In particular this does not
    inspect 63 separate shifted prefixes as `floatExponentL` does. -/
theorem routineTopWordAux_canonical (a : Runner.W) (ha : a.toNat ≠ 0) :
    routineTopWordAux 6 a = BitVec.ofNat 64 (bitlen a.toNat - 1) := by
  obtain ⟨_, lo, hi⟩ := routineTopNat_bounds 6 a.toNat (by omega) a.isLt
  have bits := bitlen_unique a.toNat (routineTopNat 6 a.toNat + 1)
    (by simpa only [Nat.add_sub_cancel] using lo) hi (by omega)
  rw [routineTopWordAux_model, bits, Nat.add_sub_cancel]

variable [Kern] {D : Deklaration} {L : Lay D}

/-- A binary search branch uses the existing checked `wennL` combinator.
    The six recursion levels are static; the emitted routine has no loop. -/
def routineTopAuxL (a : Nat → Option (List II × Nat)) :
    Nat → Nat → Option (List II × Nat)
  | 0, d => some ([ci 1 d 0 0], d + 1)
  | fuel + 1, d =>
    let shifted := fun j => wordK 12 j (a j) (Int.ofNat (2 ^ fuel))
    let zero := fun j => wordK 14 j (shifted j) 0
    let high := fun j => wordL 3 j
      (some ([ci 1 j (Int.ofNat (2 ^ fuel)) 0], j + 1)) (routineTopAuxL shifted fuel (j + 1))
    routineChooseL d zero (routineTopAuxL a fuel) high

theorem routineTopAuxL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (fuel : Nat) (hf : fuel ≤ 6) :
    WordCode (L := L) ρ W (routineTopAuxL a fuel) (routineTopWordAux fuel av) := by
  induction fuel generalizing a av with
  | zero => exact WordCode.const 0 (by decide)
  | succ fuel ih =>
    have shiftBound : (2 : Nat) ^ fuel ≤ 32 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show fuel ≤ 5 by omega)
      exact this
    have literal : lit32 (Int.ofNat (2 ^ fuel)) = true := by
      have hn : (0 : Int) ≤ Int.ofNat (2 ^ fuel) := Int.ofNat_nonneg _
      have hu : Int.ofNat (2 ^ fuel) ≤ (32 : Int) := Int.ofNat_le.mpr shiftBound
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
      omega
    have count : (BitVec.ofInt 64 (Int.ofNat (2 ^ fuel))).toNat % 64 = 2 ^ fuel := by
      have below64 : (2 : Nat) ^ fuel < 64 := by omega
      have belowWord : (2 : Nat) ^ fuel < 2 ^ 64 := by omega
      have hc : Int.ofNat (2 ^ fuel) = ((2 ^ fuel : Nat) : Int) := rfl
      rw [hc, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt belowWord,
        Nat.mod_eq_of_lt below64]
    have shifted : WordCode (L := L) ρ W _ _ := WordCode.bin ha (WordCode.const _ literal)
      (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
    rw [count] at shifted
    have zero : WordCode (L := L) ρ W _ _ := WordCode.bin shifted (WordCode.const 0 (by decide))
      (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
    have high : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const _ literal) (ih shifted (by omega))
      (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
    have result : WordCode (L := L) ρ W _ _ :=
      routineChooseL_ok zero (fun _ => ih ha (by omega)) (fun _ => high)
    intro fp K d c top h hK m pc hp
    have h0 : (BitVec.ofInt 64 0 : Runner.W) = 0 := by decide
    have hc : Int.ofNat (2 ^ fuel) = ((2 ^ fuel : Nat) : Int) := rfl
    simpa only [routineTopAuxL, routineTopWordAux, hc, BitVec.ofInt_natCast, h0] using
      result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Count the zeros before the leading bit. Zero's result is 64. -/
def routineLeadingZerosWord (a : Runner.W) : Runner.W :=
  if a == 0 then 64 else 63 - routineTopWordAux 6 a

theorem routineLeadingZerosWord_model (av : Runner.W) :
    routineLeadingZerosWord av = BitVec.ofNat 64 (64 - bitlen av.toNat) := by
  by_cases hz : av = 0
  · subst av
    rfl
  · have nonzero : av.toNat ≠ 0 := by
      intro h
      exact hz (BitVec.eq_of_toNat_eq h)
    have bounds := routineTopNat_bounds 6 av.toNat (by omega) av.isLt
    have bits := bitlen_unique av.toNat (routineTopNat 6 av.toNat + 1)
      (by simpa using bounds.2.1) bounds.2.2 (by omega)
    have positive : 0 < bitlen av.toNat := by omega
    have topBound : bitlen av.toNat - 1 ≤ 63 := by omega
    simp only [routineLeadingZerosWord, beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true,
      ite_false, routineTopWordAux_canonical av nonzero,
      show (63 : Runner.W) = BitVec.ofNat 64 63 from rfl]
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) 63 (bitlen av.toNat - 1)
      (by omega) topBound]
    congr 1
    omega

def routineLeadingZerosL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  routineChooseL d (fun j => wordK 14 j (a j) 0)
    (fun j => some ([ci 1 j 64 0], j + 1))
    (fun j => wordL 4 j (some ([ci 1 j 63 0], j + 1)) (routineTopAuxL a 6 (j + 1)))

theorem routineLeadingZerosL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => routineLeadingZerosL d a) (routineLeadingZerosWord av) :=
  routineChooseL_ok (WordCode.bin ha (WordCode.const 0 (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256))
    (fun _ => WordCode.const 64 (by decide))
    (fun _ => WordCode.bin (WordCode.const 63 (by decide)) (routineTopAuxL_ok ha 6 (by decide))
      (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256))

theorem routineLeadingZerosL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => routineLeadingZerosL d a)
      (BitVec.ofNat 64 (64 - bitlen av.toNat)) := by
  rw [← routineLeadingZerosWord_model av]
  exact routineLeadingZerosL_word ha

theorem routineLeadingZeros_zeuge :
    routineTopWordAux 6 8 = 3 ∧
    routineTopWordAux 6 (BitVec.ofNat 64 (2 ^ 55)) = 55 ∧
    routineTopWordAux 6 (BitVec.ofNat 64 (2 ^ 64 - 1)) = 63 := by
  decide +kernel

theorem routineTopAuxL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W
      (routineTopAuxL (fun d => some ([ci 1 d 8 0], d + 1)) 6) 3 := by
  have search : WordCode (L := L) ρ W _ _ := routineTopAuxL_ok (L := L) (ρ := ρ) (W := W)
    (WordCode.const 8 (by decide)) 6 (by decide)
  intro fp K d c top h hK m pc hp
  simpa only [show routineTopWordAux 6 (BitVec.ofInt 64 8) = 3 from by decide +kernel] using
    search (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

#print axioms routineTopNat_bounds
#print axioms routineTopWordAux_canonical
#print axioms routineTopAuxL_ok
#print axioms routineLeadingZerosL_word
#print axioms routineLeadingZerosWord_model
#print axioms routineLeadingZerosL_ok
#print axioms routineLeadingZeros_zeuge
#print axioms routineTopAuxL_ok_zeuge
end Gabbro.Stage0.Senke
