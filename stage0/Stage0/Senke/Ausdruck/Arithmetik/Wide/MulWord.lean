/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/MulWord.lean
  Subject:   The 64 x 64 -> 128 bit product on words, from 32-bit halves.

  The IR has no high multiplication. `mulHiW` computes the high word from the four 32-bit partial
  products exactly as the emitted code does; `mulStepW` is one multiply-accumulate limb step
  `r + x*y + c` with its carry word. Both are proved against natural-number division.
-/
import Mathlib.Tactic.Ring
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Limbs

namespace Gabbro.Stage0.Senke

/-- The low 32 bits. -/
def m32 : Runner.W := BitVec.ofNat 64 (2 ^ 32 - 1)

/-- The high word of the product, from 32-bit halves. -/
def mulHiW (p q : Runner.W) : Runner.W :=
  let ph := p >>> 32
  let pl := p &&& m32
  let qh := q >>> 32
  let ql := q &&& m32
  let a0 := pl * ql
  let a1 := ph * ql
  let a2 := pl * qh
  let a3 := ph * qh
  let mid := (a0 >>> 32) + (a1 &&& m32) + (a2 &&& m32)
  a3 + (a1 >>> 32) + (a2 >>> 32) + (mid >>> 32)

theorem m32_toNat : m32.toNat = 2 ^ 32 - 1 := by
  simp [m32, BitVec.toNat_ofNat]

theorem and_m32_toNat (x : Runner.W) : (x &&& m32).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, m32_toNat]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

theorem shr32_toNat (x : Runner.W) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The natural-number identity behind the four partial products. -/
theorem mulHi_nat (p q : Nat) :
    (p / 2 ^ 32) * (q / 2 ^ 32) + (p / 2 ^ 32) * (q % 2 ^ 32) / 2 ^ 32 +
      (p % 2 ^ 32) * (q / 2 ^ 32) / 2 ^ 32 +
      (((p % 2 ^ 32) * (q % 2 ^ 32) / 2 ^ 32 + (p / 2 ^ 32) * (q % 2 ^ 32) % 2 ^ 32 +
        (p % 2 ^ 32) * (q / 2 ^ 32) % 2 ^ 32) / 2 ^ 32) = p * q / 2 ^ 64 := by
  have e : p * q = (p / 2 ^ 32) * (q / 2 ^ 32) * 2 ^ 64 +
      ((p / 2 ^ 32) * (q % 2 ^ 32) + (p % 2 ^ 32) * (q / 2 ^ 32)) * 2 ^ 32 +
      (p % 2 ^ 32) * (q % 2 ^ 32) := by
    have h1 := Nat.div_add_mod p (2 ^ 32)
    have h2 := Nat.div_add_mod q (2 ^ 32)
    calc p * q = (2 ^ 32 * (p / 2 ^ 32) + p % 2 ^ 32) * (2 ^ 32 * (q / 2 ^ 32) + q % 2 ^ 32) := by
          rw [h1, h2]
      _ = _ := by ring
  generalize hA : (p % 2 ^ 32) * (q % 2 ^ 32) = A at e ⊢
  generalize hB : (p / 2 ^ 32) * (q % 2 ^ 32) = B at e ⊢
  generalize hC : (p % 2 ^ 32) * (q / 2 ^ 32) = C at e ⊢
  generalize hD : (p / 2 ^ 32) * (q / 2 ^ 32) = D at e ⊢
  omega

theorem mulHiW_toNat (p q : Runner.W) : (mulHiW p q).toNat = p.toNat * q.toNat / 2 ^ 64 := by
  have hp := p.isLt
  have hq := q.isLt
  have pl : p.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
  have ql : q.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
  have ph : p.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have qh : q.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have b : ∀ x y : Nat, x < 2 ^ 32 → y < 2 ^ 32 → x * y < 2 ^ 64 := fun x y hx hy => by
    calc x * y < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 64 := by norm_num
  have e := mulHi_nat p.toNat q.toNat
  have hH : p.toNat * q.toNat / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (by calc p.toNat * q.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hp hq
                                _ = 2 ^ 64 * 2 ^ 64 := rfl)
  have hA := b _ _ pl ql
  have hB := b _ _ ph ql
  have hC := b _ _ pl qh
  have hD := b _ _ ph qh
  simp only [mulHiW, BitVec.toNat_add, BitVec.toNat_mul, and_m32_toNat, shr32_toNat]
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hC, Nat.mod_eq_of_lt hD]
  generalize (p.toNat % 2 ^ 32) * (q.toNat % 2 ^ 32) = A at e hA ⊢
  generalize (p.toNat / 2 ^ 32) * (q.toNat % 2 ^ 32) = B at e hB ⊢
  generalize (p.toNat % 2 ^ 32) * (q.toNat / 2 ^ 32) = C at e hC ⊢
  generalize (p.toNat / 2 ^ 32) * (q.toNat / 2 ^ 32) = D at e hD ⊢
  generalize p.toNat * q.toNat / 2 ^ 64 = H at e hH ⊢
  omega

/-- One multiply-accumulate limb step: the new digit and the outgoing carry of `r + x*y + c`. -/
def mulStepW (r x y c : Runner.W) : Runner.W × Runner.W :=
  let lo := x * y
  let hi := mulHiW x y
  let s1 := r + lo
  let k1 := Runner.IR.bool (s1.ult lo)
  let s2 := s1 + c
  let k2 := Runner.IR.bool (s2.ult s1)
  (s2, hi + k1 + k2)

theorem mulStepW_spec (r x y c : Runner.W) :
    (mulStepW r x y c).1.toNat = (r.toNat + x.toNat * y.toNat + c.toNat) % 2 ^ 64 ∧
    (mulStepW r x y c).2.toNat = (r.toNat + x.toNat * y.toNat + c.toNat) / 2 ^ 64 := by
  have hr := r.isLt
  have hc := c.isLt
  have hx := x.isLt
  have hy := y.isLt
  have hP : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have key : ∀ b : Bool, (Runner.IR.bool b).toNat = if b = true then 1 else 0 := by
    intro b; cases b <;> rfl
  have hhi := mulHiW_toNat x y
  have hlo : (x * y).toNat = x.toNat * y.toNat % 2 ^ 64 := BitVec.toNat_mul x y
  have hdm := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ 64)
  simp only [mulStepW, BitVec.toNat_add, key, BitVec.ult, decide_eq_true_eq, hlo, hhi]
  generalize x.toNat * y.toNat = P at *
  refine ⟨by omega, ?_⟩
  split <;> split <;> omega

end Gabbro.Stage0.Senke

