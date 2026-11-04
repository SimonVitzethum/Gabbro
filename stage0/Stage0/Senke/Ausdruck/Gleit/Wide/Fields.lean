/- Typed integer expressions preserve the complete native-conversion input. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Search
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloat
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

def width (lo hi : Int) : Nat := max 55 (max lo.natAbs hi.natAbs).log2
def upper (w : Nat) : Int := 2 ^ (w + 1) - 1

theorem upper_one (w : Nat) : 1 ≤ upper w := by
  have positive : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  unfold upper
  rw [Int.pow_succ]
  omega

theorem upper_bound (w : Nat) : upper w < (2 : Int) ^ (w + 2) := by
  have positive : (0 : Int) < 2 ^ (w + 1) := Int.pow_pos (by decide)
  rw [show w + 2 = (w + 1) + 1 by omega, Int.pow_succ]
  unfold upper
  omega

def zero (hi : Int) (bound : 0 ≤ hi) : Expr D Γ Λ (.int 0 hi) :=
  .widen (by omega) bound (.lit 0)

def magnitude {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 (upper w)) :=
  .wenn (.lt e (.lit 0))
    (.eng (.neg e) 0 (upper w) (zero _ (by have := upper_one w; omega)))
    (.eng e 0 (upper w) (zero _ (by have := upper_one w; omega)))

def logarithm {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 (w : Int)) := by
  simpa only [Nat.zero_add] using position (magnitude w e) 0 w

def shift {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 (w : Int)) :=
  .eng (.sub (logarithm w e) (.lit 55)) 0 (w : Int) (zero _ (by omega))

def quotient {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 (upper w)) :=
  .shr (w + 2) (upper_bound w) (by omega) (by omega) (by omega)
    (magnitude w e) (shift w e)

def denominator {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 1 ((2 : Int) ^ w)) :=
  .eng (.shl (w + 2) (by
    have positive : (0 : Int) < 2 ^ (w + 1) := Int.pow_pos (by decide)
    rw [show w + 2 = (w + 1) + 1 by omega, Int.pow_succ]
    omega)
    (by omega) (by omega) (by omega) (.lit 1) (shift w e))
    1 ((2 : Int) ^ w)
    (.widen (by omega) (by have := Int.pow_pos (n := (2 : Int)) (m := w) (by decide); omega) (.lit 1))

def sticky {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 1) :=
  .wenn (.eq (.rem (by omega) (by omega) (magnitude w e) (denominator w e)) (.lit 0))
    (zero 1 (by omega)) (.widen (by omega) (by omega) (.lit 1))

def guard {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 (2 ^ 56 - 1)) :=
  .bor 56 (by omega) (by omega) (by omega) (by decide)
    (.eng (quotient w e) 0 (2 ^ 56 - 1) (zero _ (by decide))) (sticky w e)

def index {lo hi : Int} (w : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int 0 2047) :=
  .eng (.add (logarithm w e) (.lit 1023)) 0 2047
    (.widen (by omega) (by omega) (.lit 2047))

def small {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) :
    Expr D Γ Λ (.int (-2 ^ 55) (2 ^ 55)) :=
  .eng e (-2 ^ 55) (2 ^ 55) (.widen (by decide) (by decide) (.lit 0))

theorem magnitude_bound {lo hi : Int} (x : Zahl lo hi) :
    (x.n.natAbs : Int) ≤ upper (width lo hi) := by
  let b := max lo.natAbs hi.natAbs
  have abs : x.n.natAbs ≤ b := by have := x.lo_le; have := x.le_hi; dsimp [b]; omega
  have high : b < 2 ^ (b.log2 + 1) := Nat.lt_log2_self
  have power := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show b.log2 + 1 ≤ width lo hi + 1 by dsimp only [b, width]; omega)
  have result : x.n.natAbs < 2 ^ (width lo hi + 1) := by omega
  have cast : (x.n.natAbs : Int) < (2 : Int) ^ (width lo hi + 1) := by
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using Int.ofNat_lt.mpr result
  unfold upper
  omega

variable {σ₀ σ : World D} {ρ : Env D Γ} {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
  {w : Nat}

private theorem eval_upper_cast {a b : Int} (bound : a = b)
    (types : Expr D Γ Λ (.int 0 a) = Expr D Γ Λ (.int 0 b))
    (input : Expr D Γ Λ (.int 0 a)) :
    (eval σ₀ (cast types input) σ ρ).n = (eval σ₀ input σ ρ).n := by
  cases bound
  rfl

theorem magnitude_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w) :
    (eval σ₀ (magnitude w e) σ ρ).n = ((eval σ₀ e σ ρ).n.natAbs : Int) := by
  by_cases negative : (eval σ₀ e σ ρ).n < 0
  · have lower : 0 ≤ -(eval σ₀ e σ ρ).n := by omega
    have absolute := Int.ofNat_natAbs_of_nonpos (show (eval σ₀ e σ ρ).n ≤ 0 by omega)
    have upper : -(eval σ₀ e σ ρ).n ≤ upper w := by rwa [absolute] at bound
    rw [absolute]
    simp [magnitude, eval, wahr?, Zahl.neg, negative, lower, upper]
    exact congrArg Zahl.n (dif_pos ⟨lower, upper⟩)
  · have lower : 0 ≤ (eval σ₀ e σ ρ).n := by omega
    have absolute := Int.natAbs_of_nonneg lower
    have upper : (eval σ₀ e σ ρ).n ≤ upper w := by rwa [absolute] at bound
    rw [absolute]
    simp [magnitude, eval, wahr?, negative, lower, upper]

theorem logarithm_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (logarithm w e) σ ρ).n = ((eval σ₀ e σ ρ).n.natAbs.log2 : Int) := by
  have high : (eval σ₀ e σ ρ).n.natAbs < 2 ^ (w + 1) := by
    have cast : ((eval σ₀ e σ ρ).n.natAbs : Int) < (2 : Int) ^ (w + 1) := by
      unfold upper at bound
      omega
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using cast
  have transport : (eval σ₀ (logarithm w e) σ ρ).n =
      (eval σ₀ (position (magnitude w e) 0 w) σ ρ).n := by
    unfold logarithm
    exact eval_upper_cast (a := ((0 + w : Nat) : Int)) (b := (w : Int))
      (by simp only [Nat.zero_add]) (by simp only [Nat.zero_add])
      (position (magnitude w e) 0 w)
  exact transport.trans (position_root (magnitude w e) σ₀ σ ρ _ w
    (magnitude_value bound) positive high)

theorem shift_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (shift w e) σ ρ).n = (integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Int) := by
  let value : Zahl 0 (w : Int) := eval σ₀ (logarithm w e) σ ρ
  have number : value.n = ((eval σ₀ e σ ρ).n.natAbs.log2 : Int) :=
    logarithm_value bound positive
  have limit := value.le_hi
  by_cases inside : 0 ≤ value.n - 55 ∧ value.n - 55 ≤ (w : Int)
  · have whole : eval σ₀ (shift w e) σ ρ =
        (⟨value.n - 55, inside.1, inside.2⟩ : Zahl 0 (w : Int)) := by
      simp only [shift, eval, Zahl.sub]
      exact dif_pos inside
    rw [whole]
    change value.n - 55 = _
    unfold integerFloatShift
    omega
  · have whole : eval σ₀ (shift w e) σ ρ =
        eval σ₀ (zero (Λ := Λ) (w : Int) (by omega)) σ ρ := by
      simp only [shift, eval, Zahl.sub]
      exact dif_neg inside
    rw [whole]
    change (0 : Int) = _
    unfold integerFloatShift
    omega

theorem small_value (bound : (eval σ₀ e σ ρ).n.natAbs < 2 ^ 55) :
    (eval σ₀ (small e) σ ρ).n = (eval σ₀ e σ ρ).n := by
  have inside : -(2 ^ 55) ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ 2 ^ 55 := by omega
  have whole : eval σ₀ (small e) σ ρ =
      (⟨(eval σ₀ e σ ρ).n, inside.1, inside.2⟩ : Zahl (-2 ^ 55) (2 ^ 55)) := by
    simp only [small, eval]
    exact dif_pos inside
  exact congrArg Zahl.n whole

end Gabbro.Stage0.Senke.WideFloat
