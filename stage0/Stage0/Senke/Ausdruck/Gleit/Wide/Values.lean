/- Identify the synthesized normalization fields without a source interpreter. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Fields
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloat
open Gabbro.Grammatik Gleitkomma Runner.IR
variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
  {σ₀ σ : World D} {ρ : Env D Γ} {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
  {w : Nat}

theorem quotient_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (quotient w e) σ ρ).n =
      ((eval σ₀ e σ ρ).n.natAbs / 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) := by
  simp only [quotient, eval, Zahl.shr]
  dsimp only
  rw [magnitude_value bound, shift_value bound positive, Int.toNat_natCast]
  simp only [Int.natCast_div, Int.natCast_pow, Int.cast_ofNat_Int]

theorem denominator_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (denominator w e) σ ρ).n =
      (2 : Int) ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs := by
  have shift := shift_value bound positive
  have limit := (eval σ₀ (shift w e) σ ρ).le_hi
  have count : integerFloatShift (eval σ₀ e σ ρ).n.natAbs ≤ w := by omega
  have lower : (1 : Int) ≤ 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs := by
    have := Int.pow_pos (a := (2 : Int)) (n := integerFloatShift (eval σ₀ e σ ρ).n.natAbs) (by decide)
    omega
  have upper : (2 : Int) ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs ≤ 2 ^ w := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) count
  simp [denominator, eval, Zahl.shl, shift, lower, upper]

theorem sticky_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (sticky w e) σ ρ).n =
      (if (eval σ₀ e σ ρ).n.natAbs % 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs = 0
        then 0 else 1 : Nat) := by
  have remainder : (eval σ₀ (Expr.rem (by omega) (by omega)
      (magnitude w e) (denominator w e)) σ ρ).n =
      ((eval σ₀ e σ ρ).n.natAbs % 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) := by
    simp only [eval, Zahl.rem]
    dsimp only
    rw [magnitude_value bound, denominator_value bound positive]
    simp only [Int.natCast_mod, Int.natCast_pow, Int.cast_ofNat_Int]
  simp only [sticky, eval]
  change (if decide (_ = 0) then _ else _) = _
  rw [remainder]
  split <;> simp_all [zero, eval, Zahl.weiter]

theorem guard_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (guard w e) σ ρ).n =
      (softShiftJamNat (eval σ₀ e σ ρ).n.natAbs
        (integerFloatShift (eval σ₀ e σ ρ).n.natAbs) : Int) := by
  have quotient := quotient_value bound positive
  have bounded := (integerFloat_bounds (eval σ₀ e σ ρ).n.natAbs).1
  have inside : 0 ≤ (eval σ₀ (WideFloat.quotient w e) σ ρ).n ∧
      (eval σ₀ (WideFloat.quotient w e) σ ρ).n ≤ 2 ^ 56 - 1 := by rw [quotient]; omega
  simp only [guard, eval, dif_pos inside, Zahl.bor]
  dsimp only
  rw [quotient, sticky_value bound positive]
  simp only [Int.toNat_natCast, softShiftJamNat, Nat.shiftRight_eq_div_pow]

theorem index_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (large : 2 ^ 55 ≤ (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (index w e) σ ρ).n = (integerFloatIndex (eval σ₀ e σ ρ).n.natAbs : Int) := by
  have positive : 0 < (eval σ₀ e σ ρ).n.natAbs := by omega
  have logarithm := logarithm_value bound positive
  have log := (integerFloat_normalized (eval σ₀ e σ ρ).n.natAbs large).2
  simp only [index, eval, Zahl.add]
  dsimp only
  rw [logarithm]
  split <;> rename_i h
  · unfold integerFloatIndex integerFloatShift
    rw [Nat.min_eq_right (by omega)]
    omega
  · simp only [eval, Zahl.weiter]
    unfold integerFloatIndex integerFloatShift
    rw [Nat.min_eq_left (by omega)]

variable [Kern] {L : Lay D}

/-- Typed source expressions use the existing full expression theorem. The
    narrowing fields are proved total above, including their actual fallbacks. -/
theorem word {a b : Int} (t : Expr D Γ Λ (.int a b)) (word : valueWords (.int a b) = 1)
    (lay : LayIn L) (same : σ₀ = σ) {W : Runner.Mem → Prop}
    (world : ∀ m, W m → WeltAt m L σ) (reserved : Nat) :
    WordCode (L := L) ρ W (fun d => lowE L t d reserved)
      (BitVec.ofInt 64 (eval σ₀ t σ ρ).n) reserved := by
  intro fp K d c top emitted fits m pc pre
  exact (lowE_ok (same := fun _ => same) σ₀ σ world lay t d c top
    emitted fits m pc ρ pre).word (by trivial)

theorem boolean (t : Expr D Γ Λ .bool) (lay : LayIn L) (same : σ₀ = σ)
    {W : Runner.Mem → Prop} (world : ∀ m, W m → WeltAt m L σ) (reserved : Nat) :
    WordCode (L := L) ρ W (fun d => lowE L t d reserved)
      (Runner.IR.bool (wahr? (eval σ₀ t σ ρ))) reserved := by
  intro fp K d c top emitted fits m pc pre
  exact (lowE_ok (same := fun _ => same) σ₀ σ world lay t d c top
    emitted fits m pc ρ pre).word (by trivial)

#print axioms guard_value
#print axioms index_value
end Gabbro.Stage0.Senke.WideFloat
