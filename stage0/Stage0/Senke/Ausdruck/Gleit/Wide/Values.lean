/- Identify the synthesized normalization fields without a source interpreter. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Fields
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloat
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
  {σ₀ σ : World D} {ρ : Env D Γ} {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
  {w : Nat}

theorem quotient_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (quotient w e) σ ρ).n =
      ((eval σ₀ e σ ρ).n.natAbs / 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) := by
  let magnitudeResult : Zahl 0 (upper w) := eval σ₀ (magnitude w e) σ ρ
  let shiftResult : Zahl 0 (w : Int) := eval σ₀ (shift w e) σ ρ
  have magnitudeNumber : magnitudeResult.n = ((eval σ₀ e σ ρ).n.natAbs : Int) :=
    magnitude_value bound
  have shiftNumber : shiftResult.n = (integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Int) :=
    shift_value bound positive
  change magnitudeResult.n / (2 : Int) ^ shiftResult.n.toNat = _
  rw [magnitudeNumber, shiftNumber, Int.toNat_natCast]
  simp only [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int]

theorem denominator_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (denominator w e) σ ρ).n =
      (2 : Int) ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs := by
  let shiftResult : Zahl 0 (w : Int) := eval σ₀ (shift w e) σ ρ
  have shiftNumber : shiftResult.n = (integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Int) :=
    shift_value bound positive
  have limit := shiftResult.le_hi
  have count : integerFloatShift (eval σ₀ e σ ρ).n.natAbs ≤ w := by omega
  have lower : (1 : Int) ≤ 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs := by
    have := Int.pow_pos (n := (2 : Int)) (m := integerFloatShift (eval σ₀ e σ ρ).n.natAbs) (by decide)
    omega
  have powerUpper : (2 : Int) ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs ≤ 2 ^ w := by
    have power := Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 2) count)
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using power
  have inside : 1 ≤ (1 : Int) * 2 ^ shiftResult.n.toNat ∧
      (1 : Int) * 2 ^ shiftResult.n.toNat ≤ 2 ^ w := by
    rw [shiftNumber, Int.toNat_natCast, Int.one_mul]
    exact ⟨lower, powerUpper⟩
  have whole : eval σ₀ (denominator w e) σ ρ =
      (⟨(1 : Int) * 2 ^ shiftResult.n.toNat, inside.1, inside.2⟩ : Zahl 1 ((2 : Int) ^ w)) := by
    simp only [denominator, eval, Zahl.shl]
    exact dif_pos inside
  rw [whole]
  change (1 : Int) * 2 ^ shiftResult.n.toNat = _
  rw [shiftNumber, Int.toNat_natCast, Int.one_mul]

theorem sticky_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (sticky w e) σ ρ).n =
      (if (eval σ₀ e σ ρ).n.natAbs % 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs = 0
        then 0 else 1 : Nat) := by
  let magnitudeResult : Zahl 0 (upper w) := eval σ₀ (magnitude w e) σ ρ
  let denominatorResult : Zahl 1 ((2 : Int) ^ w) := eval σ₀ (denominator w e) σ ρ
  have magnitudeNumber : magnitudeResult.n = ((eval σ₀ e σ ρ).n.natAbs : Int) :=
    magnitude_value bound
  have denominatorNumber : denominatorResult.n =
      (2 : Int) ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs := denominator_value bound positive
  have remainder : (eval σ₀ (Expr.rem (by omega) (by omega)
      (magnitude w e) (denominator w e)) σ ρ).n =
      ((eval σ₀ e σ ρ).n.natAbs % 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) := by
    change magnitudeResult.n.tmod denominatorResult.n = _
    rw [Int.tmod_eq_emod_of_nonneg magnitudeResult.lo_le, magnitudeNumber, denominatorNumber]
    simp only [Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int]
  change (if decide (magnitudeResult.n.tmod denominatorResult.n = 0) then
      (⟨0, by decide, by decide⟩ : Zahl 0 1) else ⟨1, by decide, by decide⟩).n = _
  change magnitudeResult.n.tmod denominatorResult.n = _ at remainder
  rw [remainder]
  by_cases exactDivision : (eval σ₀ e σ ρ).n.natAbs %
      2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs = 0 <;>
    simp only [Int.ofNat_eq_zero, exactDivision, decide_true, decide_false,
      Bool.false_eq_true, ite_true, ite_false, Int.natCast_zero, Int.natCast_one]

theorem guard_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (positive : 0 < (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (guard w e) σ ρ).n =
      (integerFloatJam (eval σ₀ e σ ρ).n.natAbs
        (integerFloatShift (eval σ₀ e σ ρ).n.natAbs) : Int) := by
  let quotientResult : Zahl 0 (upper w) := eval σ₀ (quotient w e) σ ρ
  let stickyResult : Zahl 0 1 := eval σ₀ (sticky w e) σ ρ
  have quotientNumber : quotientResult.n =
      ((eval σ₀ e σ ρ).n.natAbs / 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) :=
    quotient_value bound positive
  have stickyNumber : stickyResult.n =
      (if (eval σ₀ e σ ρ).n.natAbs % 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs = 0
        then 0 else 1 : Nat) := sticky_value bound positive
  have bounded := (integerFloat_bounds (eval σ₀ e σ ρ).n.natAbs).1
  have castBound :
      (((eval σ₀ e σ ρ).n.natAbs / 2 ^ integerFloatShift (eval σ₀ e σ ρ).n.natAbs : Nat) : Int) <
        (2 : Int) ^ 56 := by
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using Int.ofNat_lt.mpr bounded
  have inside : 0 ≤ quotientResult.n ∧ quotientResult.n ≤ 2 ^ 56 - 1 :=
    ⟨quotientResult.lo_le, by omega⟩
  let narrowed : Zahl 0 (2 ^ 56 - 1) := eval σ₀
    (Expr.eng (quotient w e) 0 (2 ^ 56 - 1) (zero _ (by decide))) σ ρ
  have whole : narrowed = (⟨quotientResult.n, inside.1, inside.2⟩ : Zahl 0 (2 ^ 56 - 1)) := by
    dsimp only [narrowed]
    simp only [eval]
    exact dif_pos inside
  have narrowedNumber : narrowed.n = quotientResult.n := congrArg Zahl.n whole
  change ((narrowed.n.toNat ||| stickyResult.n.toNat : Nat) : Int) = _
  rw [narrowedNumber, quotientNumber, stickyNumber]
  simp only [Int.toNat_natCast, integerFloatJam, Nat.shiftRight_eq_div_pow]

theorem index_value (bound : ((eval σ₀ e σ ρ).n.natAbs : Int) ≤ upper w)
    (large : 2 ^ 55 ≤ (eval σ₀ e σ ρ).n.natAbs) :
    (eval σ₀ (index w e) σ ρ).n = (integerFloatIndex (eval σ₀ e σ ρ).n.natAbs : Int) := by
  have positive : 0 < (eval σ₀ e σ ρ).n.natAbs := by omega
  let logarithmResult : Zahl 0 (w : Int) := eval σ₀ (logarithm w e) σ ρ
  have logarithmNumber : logarithmResult.n = ((eval σ₀ e σ ρ).n.natAbs.log2 : Int) :=
    logarithm_value bound positive
  have log := (integerFloat_normalized (eval σ₀ e σ ρ).n.natAbs large).2
  by_cases inside : 0 ≤ logarithmResult.n + 1023 ∧ logarithmResult.n + 1023 ≤ 2047
  · have whole : eval σ₀ (index w e) σ ρ =
        (⟨logarithmResult.n + 1023, inside.1, inside.2⟩ : Zahl 0 2047) := by
      simp only [index, eval, Zahl.add]
      exact dif_pos inside
    rw [whole]
    change logarithmResult.n + 1023 = _
    unfold integerFloatIndex integerFloatShift
    rw [Nat.min_eq_right (by omega)]
    omega
  · have whole : eval σ₀ (index w e) σ ρ =
        (⟨2047, by decide, by decide⟩ : Zahl 0 2047) := by
      simp only [index, eval, Zahl.add, Zahl.weiter]
      exact dif_neg inside
    rw [whole]
    change (2047 : Int) = _
    unfold integerFloatIndex integerFloatShift
    rw [Nat.min_eq_left (by omega)]
    rfl

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
