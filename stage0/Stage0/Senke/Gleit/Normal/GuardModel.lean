/- Connect a normalized guard word to the general exact rounding replay. -/
module
public import Stage0.Senke.Gleit.Normal.PackModel
public import Stage0.Senke.Gleit.Normal.Replay
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Once normalization has reached bit 55 or the subnormal floor, the
    integer continuation is exactly the canonical dyadic rounding. Three
    guard bits account for the scale offset 1078 rather than 1075. -/
theorem routineRoundPackWord_exact (s : Bool) (e n : Nat)
    (ep : 1 ≤ e) (eb : e ≤ 2047) (np : 4 ≤ n) (nb : n < 2 ^ 56)
    (normalized : 2 ^ 55 ≤ n ∨ e = 1) :
    routineRoundPackWord (Runner.IR.bool s) (BitVec.ofNat 64 e) (BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (zuBits f64
        (rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), (e : Int) - 1078⟩)) := by
  let q := rundeInt (n / 8) (n % 8) 8
  have qRange : n / 8 ≤ q ∧ q ≤ n / 8 + 1 := by
    dsimp only [q]
    unfold rundeInt
    split
    · omega
    · split
      · omega
      · split <;> omega
  have qb : q ≤ 2 ^ 53 := by omega
  have qScale : softRoundDyadic n (-3) = q := by
    simp only [softRoundDyadic]
    change rundeInt ((n * 1) / 8) ((n * 1) % 8) 8 = q
    simp only [Nat.mul_one, q]
  have signedNonzero : (if s then -(n : Int) else (n : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have magnitude : (if s then -(n : Int) else (n : Int)).natAbs = n := by
    cases s <;> simp
  have sign : decide ((if s then -(n : Int) else (n : Int)) < 0) = s := by
    cases s <;> simp [show (0 : Nat) < n by omega]
  have replay := softRound_replay_all (if s then -(n : Int) else (n : Int))
    ((e : Int) - 1078) signedNonzero
  dsimp only at replay
  rw [magnitude, sign] at replay
  have kernel : rundeExakt f64
      ⟨if s then -(n : Int) else (n : Int), (e : Int) - 1078⟩ =
      if softCarryExp e q < 2047 then
        if softCarry q < 2 ^ 52 then ⟨s, 0, softCarry q⟩
        else ⟨s, softCarryExp e q, softCarry q - 2 ^ 52⟩
      else ⟨s, 2047, 0⟩ := by
    by_cases normal : 2 ^ 55 ≤ n
    · have bits : bitlen n = 56 := bitlen_unique n 56 normal nb (by omega)
      rw [bits] at replay
      have position : (e : Int) - 1078 + (56 : Nat) - 1 = (e : Int) - 1023 := by omega
      rw [position] at replay
      have quant : softRoundDyadic n (53 - ((56 : Nat) : Int)) = q := qScale
      rw [quant] at replay
      have qlow : 2 ^ 52 ≤ q := by
        omega
      by_cases overflow : e = 2047
      · have above : (f64.emax : Int) < (e : Int) - 1023 := by
          change (1023 : Int) < (e : Int) - 1023
          omega
        rw [if_pos above] at replay
        have notFinite : ¬ softCarryExp e q < 2047 := by
          unfold softCarryExp
          split <;> omega
        simpa only [if_neg notFinite, show f64.bexpMax = 2047 from rfl] using replay
      · have below : ¬ (f64.emax : Int) < (e : Int) - 1023 := by
          change ¬ (1023 : Int) < (e : Int) - 1023
          omega
        have noUnderflow : ¬ (e : Int) - 1023 < f64.emin - (f64.p : Int) := by
          change ¬ (e : Int) - 1023 < -1075
          omega
        have normalExp : f64.emin ≤ (e : Int) - 1023 := by
          change (-1022 : Int) ≤ (e : Int) - 1023
          omega
        rw [if_neg below, if_neg noUnderflow, if_pos normalExp] at replay
        by_cases carry : q = 2 ^ 53
        · have noSmall : ¬ q < 2 ^ f64.p := by change ¬ q < 2 ^ 53; omega
          rw [if_neg noSmall] at replay
          by_cases last : e = 2046
          · have noRoom : ¬ (e : Int) - 1023 < (f64.emax : Int) := by
              change ¬ (e : Int) - 1023 < 1023
              omega
            rw [if_neg noRoom] at replay
            simpa only [softCarryExp, if_pos carry, last,
              show ¬ (2046 + 1 : Nat) < 2047 by decide, ite_false,
              show f64.bexpMax = 2047 from rfl] using replay
          · have room : (e : Int) - 1023 < (f64.emax : Int) := by
              change (e : Int) - 1023 < 1023
              omega
            have index : ((e : Int) - 1023 - f64.emin + 2).toNat = e + 1 := by
              change ((e : Int) - 1023 - (-1022) + 2).toNat = e + 1
              omega
            rw [if_pos room, index] at replay
            simpa only [softCarryExp, softCarry, if_pos carry,
              show e + 1 < 2047 by omega, ite_true,
              show ¬ (2 ^ 52 : Nat) < 2 ^ 52 by omega, ite_false, Nat.sub_self] using replay
        · have small : q < 2 ^ f64.p := by change q < 2 ^ 53; omega
          have index : ((e : Int) - 1023 - f64.emin + 1).toNat = e := by
            change ((e : Int) - 1023 - (-1022) + 1).toNat = e
            omega
          rw [if_pos small, index] at replay
          simpa only [softCarryExp, softCarry, if_neg carry,
            show e < 2047 by omega, ite_true,
            show ¬ q < 2 ^ 52 by omega, ite_false,
            show f64.p - 1 = 52 from rfl] using replay
    · have floor : e = 1 := normalized.resolve_left normal
      have upper : bitlen n ≤ 55 := by
        have lower := bitlen_untere n (by omega : n ≠ 0)
        by_contra h
        have power := Nat.pow_le_pow_right (show 0 < 2 by decide)
          (show 56 ≤ bitlen n by omega)
        omega
      have lower : 3 ≤ bitlen n := by
        have bound := bitlen_obere n
        by_contra h
        have power := Nat.pow_le_pow_right (show 0 < 2 by decide)
          (show bitlen n ≤ 2 by omega)
        omega
      have qsmall : q ≤ 2 ^ 52 := by
        omega
      have carry : q ≠ 2 ^ 53 := by omega
      have below : ¬ (f64.emax : Int) < (e : Int) - 1078 + (bitlen n : Int) - 1 := by
        change ¬ (1023 : Int) < (e : Int) - 1078 + (bitlen n : Int) - 1
        omega
      have noUnderflow : ¬ (e : Int) - 1078 + (bitlen n : Int) - 1 <
          f64.emin - (f64.p : Int) := by
        change ¬ (e : Int) - 1078 + (bitlen n : Int) - 1 < -1075
        omega
      have subnormal : ¬ f64.emin ≤ (e : Int) - 1078 + (bitlen n : Int) - 1 := by
        change ¬ (-1022 : Int) ≤ (e : Int) - 1078 + (bitlen n : Int) - 1
        omega
      rw [if_neg below, if_neg noUnderflow, if_neg subnormal] at replay
      have scale : (e : Int) - 1078 + 1074 = -3 := by omega
      rw [scale, qScale] at replay
      have exponent : softCarryExp e q = 1 := by
        simp only [softCarryExp, if_neg carry, floor]
      have significand : softCarry q = q := by
        simp only [softCarry, if_neg carry]
      rw [exponent, significand, if_pos (by decide : (1 : Nat) < 2047)]
      by_cases sub : q < 2 ^ 52
      · simpa only [show f64.p - 1 = 52 from rfl, if_pos sub] using replay
      · have fractionZero : q - 2 ^ 52 = 0 := by omega
        simpa only [show f64.p - 1 = 52 from rfl, if_neg sub, fractionZero] using replay
  rw [routineRoundPackWord_model s e n eb nb]
  exact congrArg (fun a : GFloat => BitVec.ofNat 64 (zuBits f64 a)) kernel.symm

/-- Both signs, the subnormal floor and an overflowing carry satisfy the
    exact-rounding theorem's premises together. -/
theorem routineRoundPackWord_exact_zeuge :
    ∀ p ∈ [(false, 1023, 2 ^ 55 + 4), (true, 1, 16), (false, 2046, 2 ^ 56 - 1)],
      1 ≤ p.2.1 ∧ p.2.1 ≤ 2047 ∧ 4 ≤ p.2.2 ∧ p.2.2 < 2 ^ 56 ∧
      (2 ^ 55 ≤ p.2.2 ∨ p.2.1 = 1) ∧
      routineRoundPackWord (Runner.IR.bool p.1) (BitVec.ofNat 64 p.2.1)
        (BitVec.ofNat 64 p.2.2) = BitVec.ofNat 64 (zuBits f64
          (rundeExakt f64 ⟨if p.1 then -(p.2.2 : Int) else (p.2.2 : Int),
            (p.2.1 : Int) - 1078⟩)) := by
  intro p member
  have bounds : 1 ≤ p.2.1 ∧ p.2.1 ≤ 2047 ∧ 4 ≤ p.2.2 ∧ p.2.2 < 2 ^ 56 ∧
      (2 ^ 55 ≤ p.2.2 ∨ p.2.1 = 1) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2,
    routineRoundPackWord_exact p.1 p.2.1 p.2.2 bounds.1 bounds.2.1 bounds.2.2.1
      bounds.2.2.2.1 bounds.2.2.2.2⟩

#print axioms routineRoundPackWord_exact
#print axioms routineRoundPackWord_exact_zeuge
end Gabbro.Stage0.Senke
