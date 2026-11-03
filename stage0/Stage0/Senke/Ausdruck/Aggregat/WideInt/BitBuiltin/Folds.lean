/- Bounded bit folds agree with the canonical Nat functions behind Zahl. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Composition
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltin
open Gabbro.Grammatik Runner.IR
set_option linter.unusedSectionVars false

/-- Division is used only in this proof-level value; emitted code uses wideShr. -/
def half {hi : Int} (x : Zahl 0 hi) : Zahl 0 hi :=
  natural hi (x.n.toNat / 2) (by
    have := Nat.div_le_self x.n.toNat 2
    have := Int.toNat_of_nonneg x.lo_le
    have := x.le_hi
    omega)

def digit {hi : Int} (x : Zahl 0 hi) : Zahl 0 1 :=
  natural 1 (x.n.toNat % 2) (by have := Nat.mod_lt x.n.toNat (by decide : 0 < 2); omega)

theorem ctzAux_bound (fuel x : Nat) : ctzAux fuel x ≤ fuel := by
  induction fuel generalizing x with
  | zero => simp only [ctzAux, Nat.le_refl]
  | succ fuel ih =>
    rw [ctzAux]
    split
    · omega
    · split
      · omega
      · have := ih (x / 2); omega

def trailingValue {hi : Int} (fuel : Nat) (x : Zahl 0 hi) : Zahl 0 (fuel : Int) :=
  natural (fuel : Int) (ctzAux fuel x.n.toNat) (by exact_mod_cast ctzAux_bound fuel x.n.toNat)

def populationValue {hi : Int} (fuel : Nat) (x : Zahl 0 hi) : Zahl 0 (fuel : Int) :=
  natural (fuel : Int) (popAux fuel x.n.toNat) (by exact_mod_cast popAux_le fuel x.n.toNat)

theorem log_bound (fuel x : Nat) (bound : x < 2 ^ (fuel + 1)) : x.log2 ≤ fuel := by
  by_cases zero : x = 0
  · simp only [zero, Nat.log2_zero, Nat.zero_le]
  · exact log2n_le_of_bounds fuel x (by omega) bound

def logarithmValue {hi : Int} (fuel : Nat) (x : Zahl 0 hi)
    (bound : x.n.toNat < 2 ^ (fuel + 1)) : Zahl 0 (fuel : Int) :=
  natural (fuel : Int) x.n.toNat.log2 (by exact_mod_cast log_bound fuel x.n.toNat bound)

variable [Kern] {D : Deklaration} {L : Lay D} {fp : Runner.W} {K reserved : Nat}
  {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
local notation "Runs" => Produces L fp K ρ W reserved

/-- Internal shift-by-one uses width >=2 even for a one-bit source field. -/
theorem half_ok {hi : Int} (width : Nat) (bound : hi < (2 : Int) ^ width)
    (room : 1 < width) (x : Zahl 0 hi) {fa : Emitter} (ia : Runs fa (.int 0 hi) x) :
    Runs (shr hi 1 fa (constant 1 1)) (.int 0 hi) (half x) := by
  exact shr_ok width 1 bound room x (⟨1, by decide, by decide⟩ : Zahl 0 1) (half x)
    (by simp only [half, natural, Nat.pow_one]; rfl) ia
      (constant_ok (⟨1, by decide, by decide⟩ : Zahl 0 1))

theorem digit_ok {hi : Int} (x : Zahl 0 hi) {fa : Emitter} (ia : Runs fa (.int 0 hi) x) :
    Runs (mask hi 1 fa) (.int 0 1) (digit x) :=
  mask_ok 1 x (digit x) rfl ia

theorem population_ok {hi : Int} (width : Nat) (bound : hi < (2 : Int) ^ width)
    (room : 1 < width) (fuel : Nat) (x : Zahl 0 hi) {fa : Emitter}
    (ia : Runs fa (.int 0 hi) x) :
    Runs (population hi fuel fa) (.int 0 (fuel : Int)) (populationValue fuel x) := by
  induction fuel generalizing x fa with
  | zero =>
    change Runs (constant 0 0) (.int 0 0) (⟨0, by decide, by decide⟩ : Zahl 0 0)
    exact constant_ok (⟨0, by decide, by decide⟩ : Zahl 0 0)
  | succ fuel ih =>
    exact add_ok (digit x) (populationValue fuel (half x)) (populationValue (fuel + 1) x)
      (by simp only [populationValue, natural, digit, half, popAux, Int.natCast_add, Int.toNat_natCast])
      (digit_ok x ia) (ih (half x) (half_ok width bound room x ia))

theorem trailing_ok {hi : Int} (width : Nat) (bound : hi < (2 : Int) ^ width)
    (room : 1 < width) (fuel : Nat) (x : Zahl 0 hi) {fa : Emitter}
    (ia : Runs fa (.int 0 hi) x) :
    Runs (trailing hi fuel fa) (.int 0 (fuel : Int)) (trailingValue fuel x) := by
  induction fuel generalizing x fa with
  | zero =>
    change Runs (constant 0 0) (.int 0 0) (⟨0, by decide, by decide⟩ : Zahl 0 0)
    exact constant_ok (⟨0, by decide, by decide⟩ : Zahl 0 0)
  | succ fuel ih =>
    let zero : Zahl 0 (fuel + 1 : Nat) := ⟨0, by omega, by omega⟩
    let one : Zahl 0 1 := ⟨1, by decide, by decide⟩
    let sum : Zahl 0 (fuel + 1 : Nat) :=
      natural (fuel + 1 : Nat) (1 + ctzAux fuel (x.n.toNat / 2)) (by
        have := ctzAux_bound fuel (x.n.toNat / 2); omega)
    have sumCode := add_ok one (trailingValue fuel (half x)) sum
      (by simp only [sum, one, trailingValue, natural, half, Int.toNat_natCast, Int.natCast_add]; rfl)
      (constant_ok one) (ih (half x) (half_ok width bound room x ia))
    have value : trailingValue (fuel + 1) x =
        if decide (x.n = 0) then zero else if decide ((digit x).n = 1) then zero else sum := by
      have zx : x.n = 0 ↔ x.n.toNat = 0 := by
        have := Int.toNat_of_nonneg x.lo_le; omega
      apply Zahl.ext_n
      have parity : ((x.n.toNat % 2 : Nat) : Int) = 1 ↔ x.n.toNat % 2 = 1 := by omega
      by_cases hz : x.n = 0
      · simp [trailingValue, natural, ctzAux, digit, zero, hz]
      · have hn : x.n.toNat ≠ 0 := by omega
        by_cases hd : x.n.toNat % 2 = 1 <;>
          simp only [trailingValue, natural, ctzAux, digit, zero, sum, hz, hn,
            parity, hd, decide_true, decide_false, Bool.false_eq_true,
            ite_true, ite_false, Int.natCast_add]
    rw [value]
    exact choose_ok (τ := .int 0 (fuel + 1 : Nat)) _ zero _
      (eq_ok x (⟨0, by omega, by omega⟩ : Zahl 0 0) ia
        (constant_ok (⟨0, by omega, by omega⟩ : Zahl 0 0)))
      (constant_ok zero)
      (choose_ok (τ := .int 0 (fuel + 1 : Nat)) _ zero sum
        (eq_ok (digit x) one (digit_ok x ia) (constant_ok one))
        (constant_ok zero) sumCode)

theorem logarithm_ok {hi : Int} (width : Nat) (bound : hi < (2 : Int) ^ width)
    (room : 1 < width) (fuel : Nat) (x : Zahl 0 hi)
    (fits : x.n.toNat < 2 ^ (fuel + 1)) {fa : Emitter} (ia : Runs fa (.int 0 hi) x) :
    Runs (logarithm hi fuel fa) (.int 0 (fuel : Int)) (logarithmValue fuel x fits) := by
  induction fuel generalizing x fa with
  | zero =>
    have value : logarithmValue 0 x fits = (⟨0, by omega, by omega⟩ : Zahl 0 0) := by
      apply Zahl.ext_n
      have := log_bound 0 x.n.toNat fits
      change (x.n.toNat.log2 : Int) = 0
      omega
    rw [value]
    change Runs (constant 0 0) (.int 0 0) (⟨0, by omega, by omega⟩ : Zahl 0 0)
    exact constant_ok (⟨0, by omega, by omega⟩ : Zahl 0 0)
  | succ fuel ih =>
    have halfFits : (half x).n.toNat < 2 ^ (fuel + 1) := by
      change x.n.toNat / 2 < 2 ^ (fuel + 1)
      rw [Nat.pow_succ] at fits
      omega
    let zero : Zahl 0 (fuel + 1 : Nat) := ⟨0, by omega, by omega⟩
    let one : Zahl 0 1 := ⟨1, by decide, by decide⟩
    let two : Zahl 0 2 := ⟨2, by decide, by decide⟩
    let sum : Zahl 0 (fuel + 1 : Nat) :=
      natural (fuel + 1 : Nat) (1 + (x.n.toNat / 2).log2) (by
        have := log_bound fuel (x.n.toNat / 2) halfFits; omega)
    have value : logarithmValue (fuel + 1) x fits = if decide (x.n < 2) then zero else sum := by
      have small : x.n < 2 ↔ ¬ 2 ≤ x.n.toNat := by
        have := Int.toNat_of_nonneg x.lo_le; omega
      apply Zahl.ext_n
      change (x.n.toNat.log2 : Int) = _
      rw [Nat.log2_def]
      by_cases hx : x.n < 2
      · have hn : ¬ 2 ≤ x.n.toNat := small.mp hx
        simp only [hx, hn, decide_true, ite_true, ite_false, zero]
      · have hn : 2 ≤ x.n.toNat := by omega
        simp only [hx, hn, decide_false, Bool.false_eq_true, ite_false, ite_true,
          sum, natural, Int.natCast_add]
        omega
    rw [value]
    exact choose_ok (τ := .int 0 (fuel + 1 : Nat)) _ zero sum
      (lt_ok x two ia (constant_ok two)) (constant_ok zero)
      (add_ok one (logarithmValue fuel (half x) halfFits) sum
        (by simp only [one, logarithmValue, natural, half, sum, Int.toNat_natCast, Int.natCast_add]; rfl)
        (constant_ok one) (ih (half x) halfFits (half_ok width bound room x ia)))

end Gabbro.Stage0.Senke.BitBuiltin
