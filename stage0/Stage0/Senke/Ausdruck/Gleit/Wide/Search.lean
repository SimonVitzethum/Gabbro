/- Balanced leading-position search avoids a linear nest of wide shifts. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Model
public import Stage0.Senke.Ausdruck.Satz
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloat
open Gabbro.Grammatik Gleitkomma
variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Search the closed exponent interval. Each leaf is a literal position;
    every internal node compares the complete original magnitude against a
    power of two. There are `fuel + 1` leaves and logarithmic tree depth.
    In particular no chain of `fuel` nested multiword shift kernels is built. -/
def position {lo hi : Int} (input : Expr D Γ Λ (.int lo hi))
    (start fuel : Nat) : Expr D Γ Λ (.int 0 (start + fuel : Nat)) :=
  match fuel with
  | 0 => .widen (by omega) (by omega) (.lit (start : Int))
  | fuel + 1 =>
      let half := fuel / 2
      let pivot := start + half + 1
      .wenn (.lt input (.lit ((2 : Int) ^ pivot)))
        (.widen (by omega) (by omega) (position input start half))
        (.widen (by omega) (by omega) (position input pivot (fuel - half)))
termination_by fuel
decreasing_by all_goals dsimp only; omega

/-- The comparison used by the emitted search decides exactly whether the
    leading position precedes the pivot, including equality to a power of two. -/
theorem position_compare (n pivot : Nat) (positive : 0 < n) :
    ((n : Int) < (2 : Int) ^ pivot) ↔ n.log2 < pivot := by
  have cast : ((n : Int) < (2 : Int) ^ pivot) ↔ n < 2 ^ pivot := by
    rw [← Int.natCast_pow, Int.ofNat_lt]
  rw [cast]
  exact (Nat.log2_lt (by omega : n ≠ 0)).symm

/-- Every recursive interval is justified by the actual comparison. This
    proof covers all nonzero magnitudes, not a per-program scan certificate. -/
theorem position_value {lo hi : Int} (input : Expr D Γ Λ (.int lo hi))
    (σ₀ σ : World D) (ρ : Env D Γ) (n start fuel : Nat)
    (value : (eval σ₀ input σ ρ).n = (n : Int)) (positive : 0 < n)
    (lower : start ≤ n.log2) (upper : n.log2 ≤ start + fuel) :
    (eval σ₀ (position input start fuel) σ ρ).n = (n.log2 : Int) := by
  cases fuel with
  | zero =>
    rw [position.eq_def]
    simp only [eval, Zahl.weiter]
    omega
  | succ fuel =>
    rw [position.eq_def]
    simp only [eval]
    change (if decide ((eval σ₀ input σ ρ).n < (2 : Int) ^ (start + fuel / 2 + 1))
      then Zahl.weiter _ _ (eval σ₀ (position input start (fuel / 2)) σ ρ)
      else Zahl.weiter _ _ (eval σ₀ (position input (start + fuel / 2 + 1) (fuel - fuel / 2)) σ ρ)).n = _
    rw [value]
    by_cases left : n.log2 < start + fuel / 2 + 1
    · rw [if_pos (by simpa only [decide_eq_true_eq] using
        (position_compare n _ positive).mpr left)]
      exact position_value input σ₀ σ ρ n start (fuel / 2) value positive lower (by omega)
    · rw [if_neg (by simpa only [decide_eq_true_eq] using
        (not_congr (position_compare n _ positive)).mpr left)]
      exact position_value input σ₀ σ ρ n (start + fuel / 2 + 1) (fuel - fuel / 2)
        value positive (by omega) (by omega)
termination_by fuel
decreasing_by all_goals omega

/-- The root of a search covers a complete bounded unsigned magnitude. -/
theorem position_root {lo hi : Int} (input : Expr D Γ Λ (.int lo hi))
    (σ₀ σ : World D) (ρ : Env D Γ) (n fuel : Nat)
    (value : (eval σ₀ input σ ρ).n = (n : Int))
    (positive : 0 < n) (bound : n < 2 ^ (fuel + 1)) :
    (eval σ₀ (position input 0 fuel) σ ρ).n = (n.log2 : Int) := by
  have log := (Nat.log2_lt (by omega : n ≠ 0)).mpr bound
  exact position_value input σ₀ σ ρ n 0 fuel value positive (by omega) (by omega)

/-- Nonzero values at and around each pivot jointly inhabit the recursive
    search's value premises. The checked source exporter is not involved. -/
theorem position_value_zeuge (σ₀ σ : World D) (ρ : Env D Γ) :
    ∀ n ∈ [1, 2 ^ 55, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 1],
      0 < n ∧ n < 2 ^ 81 ∧
      (eval σ₀ (position (Expr.lit (Λ := Λ) (n : Int)) 0 80) σ ρ).n = (n.log2 : Int) := by
  intro n member
  have bound : 0 < n ∧ n < 2 ^ 81 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨bound.1, bound.2, position_root _ σ₀ σ ρ n 80 rfl bound.1 bound.2⟩

#print axioms position_value
#print axioms position_value_zeuge
end Gabbro.Stage0.Senke.WideFloat
