/-
  File:      stage0/Stage0/Senke/Ausdruck/Wide/Limbs.lean
  Subject:   Digit sequences base `2^64`: values, carry chains and the canonical integer encoding.

  `dval x i` is the value of the low `i` digits. A carry chain adds two digit sequences; the identity
  `sum_identity` ties the produced digits and the carry to the sums of values, so the chain code is
  proved against numbers and never against single bits. `integerEncoding k v` is exactly the digit
  sequence of `v mod 2^(64k)`.
-/
import Mathlib.Tactic.Linarith
import Stage0.Senke.Ausdruck.Wide.Alu

namespace Gabbro.Stage0.Senke

/-- The value of the low `i` digits. -/
def dval (x : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => dval x i + x i * 2 ^ (64 * i)

@[simp] theorem dval_zero (x : Nat → Nat) : dval x 0 = 0 := rfl
theorem dval_succ (x : Nat → Nat) (i : Nat) : dval x (i + 1) = dval x i + x i * 2 ^ (64 * i) := rfl

theorem dval_congr {x y : Nat → Nat} {k : Nat} (h : ∀ j, j < k → x j = y j) : dval x k = dval y k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dval_succ, dval_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

theorem dval_lt {x : Nat → Nat} (hx : ∀ j, x j < 2 ^ 64) : ∀ i, dval x i < 2 ^ (64 * i)
  | 0 => by simp [dval]
  | i + 1 => by
    have h1 := dval_lt hx i
    have h2 := hx i
    have h3 : x i * 2 ^ (64 * i) ≤ (2 ^ 64 - 1) * 2 ^ (64 * i) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 ^ 64 - 1) * 2 ^ (64 * i) + 2 ^ (64 * i) = 2 ^ (64 * (i + 1)) := by
      have e : 2 ^ (64 * (i + 1)) = 2 ^ 64 * 2 ^ (64 * i) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      rw [e, ← Nat.succ_mul]
      congr 1
    rw [dval_succ]
    omega

/-- The carry into digit `i` of `x + y + c0`. -/
def carryAt (x y : Nat → Nat) (c0 : Nat) : Nat → Nat
  | 0 => c0
  | i + 1 => (x i + y i + carryAt x y c0 i) / 2 ^ 64

/-- The digit `i` of `x + y + c0`. -/
def sumDig (x y : Nat → Nat) (c0 i : Nat) : Nat := (x i + y i + carryAt x y c0 i) % 2 ^ 64

@[simp] theorem carryAt_zero (x y : Nat → Nat) (c0 : Nat) : carryAt x y c0 0 = c0 := rfl
theorem carryAt_succ (x y : Nat → Nat) (c0 i : Nat) :
    carryAt x y c0 (i + 1) = (x i + y i + carryAt x y c0 i) / 2 ^ 64 := rfl

/-- The produced digits and the outgoing carry account for the whole sum. -/
theorem sum_identity (x y : Nat → Nat) (c0 : Nat) (i : Nat) :
    dval (sumDig x y c0) i + 2 ^ (64 * i) * carryAt x y c0 i = dval x i + dval y i + c0 := by
  induction i with
  | zero => simp [dval]
  | succ i ih =>
    rw [dval_succ, dval_succ, dval_succ, carryAt_succ]
    have hd := Nat.div_add_mod (x i + y i + carryAt x y c0 i) (2 ^ 64)
    have hp : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    simp only [sumDig]
    rw [hp]
    generalize 2 ^ (64 * i) = P at *
    generalize (x i + y i + carryAt x y c0 i) / 2 ^ 64 = q at *
    generalize (x i + y i + carryAt x y c0 i) % 2 ^ 64 = r at *
    generalize 2 ^ 64 = N at *
    nlinarith

theorem carryAt_le {x y : Nat → Nat} (hx : ∀ j, x j < 2 ^ 64) (hy : ∀ j, y j < 2 ^ 64)
    {c0 : Nat} (hc : c0 ≤ 1) : ∀ i, carryAt x y c0 i ≤ 1
  | 0 => hc
  | i + 1 => by
    have := carryAt_le hx hy hc i
    have := hx i
    have := hy i
    rw [carryAt_succ]
    have : (x i + y i + carryAt x y c0 i) / 2 ^ 64 < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega

/-- Adding two `k`-digit numbers modulo `2^(64k)`. -/
theorem dval_sum {x y : Nat → Nat} (hx : ∀ j, x j < 2 ^ 64) (hy : ∀ j, y j < 2 ^ 64)
    (c0 k : Nat) : dval (sumDig x y c0) k = (dval x k + dval y k + c0) % 2 ^ (64 * k) := by
  have id := sum_identity x y c0 k
  have lt : dval (sumDig x y c0) k < 2 ^ (64 * k) := by
    apply dval_lt
    intro j
    exact Nat.mod_lt _ (by positivity)
  rw [← id, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

theorem sumDig_lt (x y : Nat → Nat) (c0 i : Nat) : sumDig x y c0 i < 2 ^ 64 :=
  Nat.mod_lt _ (by positivity)

/-- Shifting both sequences and the carry shifts the chain. -/
theorem carryAt_shift (x y : Nat → Nat) (c0 n : Nat) :
    carryAt (fun j => x (j + 1)) (fun j => y (j + 1)) (carryAt x y c0 1) n = carryAt x y c0 (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [carryAt_succ, ih, carryAt_succ _ _ _ (n + 1)]

theorem sumDig_shift (x y : Nat → Nat) (c0 n : Nat) :
    sumDig (fun j => x (j + 1)) (fun j => y (j + 1)) (carryAt x y c0 1) n = sumDig x y c0 (n + 1) := by
  simp only [sumDig, carryAt_shift]

theorem carryAt_congr {x x' y y' : Nat → Nat} {c0 : Nat} :
    ∀ {n : Nat}, (∀ j, j < n → x j = x' j) → (∀ j, j < n → y j = y' j) →
      carryAt x y c0 n = carryAt x' y' c0 n
  | 0, _, _ => rfl
  | n + 1, hx, hy => by
    rw [carryAt_succ, carryAt_succ, carryAt_congr (fun j hj => hx j (by omega)) (fun j hj => hy j (by omega)),
      hx n (by omega), hy n (by omega)]

theorem sumDig_congr {x x' y y' : Nat → Nat} {c0 j : Nat} (hx : ∀ i, i ≤ j → x i = x' i)
    (hy : ∀ i, i ≤ j → y i = y' i) : sumDig x y c0 j = sumDig x' y' c0 j := by
  simp only [sumDig]
  rw [carryAt_congr (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega)), hx j (Nat.le_refl _),
    hy j (Nat.le_refl _)]

end Gabbro.Stage0.Senke
