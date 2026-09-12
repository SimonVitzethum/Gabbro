/- Skeleton for lane 69: overflow forms (PLAN-BITS section 4, model half). -/

import Grammatik.Typen

namespace Gabbro.Grammatik

/-- Storage-width helper: `2 ^ (w+1)` is positive on `Int`. -/
theorem zweiPow_pos (w : Nat) : (0 : Int) < 2 ^ (w + 1) := by
  have h0 : (0 : Nat) < 2 ^ (w + 1) := Nat.pow_pos (by decide)
  have hpos' : (0 : Int) < ((2 ^ (w + 1) : Nat) : Int) := Int.ofNat_lt.mpr h0
  have e : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  omega

/-- Wrapping addition on the exact unsigned range `0 .. 2^(w+1) - 1`
    (PLAN-BITS section 4: the `+%` form lives only on exact `uN` ranges). -/
def Zahl.addW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n + b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n + b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping subtraction on the exact unsigned range: `(a - b) mod 2^(w+1)`. -/
def Zahl.subW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n - b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n - b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping multiplication on the exact unsigned range: `(a * b) mod 2^(w+1)`. -/
def Zahl.mulW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n * b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n * b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping dynamic left shift: `(a * 2^s) mod 2^(w+1)`, with the shift
    amount typed `0 .. w` (PLAN-BITS section 2: the amount is in the type). -/
def Zahl.shlW (w : Nat) (a : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n * 2 ^ s.n.toNat) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n * 2 ^ s.n.toNat) (zweiPow_pos w)
    omega⟩

end Gabbro.Grammatik
