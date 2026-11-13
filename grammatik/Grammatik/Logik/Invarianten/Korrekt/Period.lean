module

public import Grammatik.Logik.Invarianten.Korrekt.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

theorem period_pos [DecidableEq α] (name : α) (body : QF α) : 0 < period name body := by
  induction body with
  | tru => change 0 < (1 : Nat); decide
  | fls => change 0 < (1 : Nat); decide
  | atom relation term =>
      cases relation with
      | lt => change 0 < (1 : Nat); decide
      | dvd k | ndvd k => simp only [period]; split <;> omega
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      exact Int.lcm_pos (by omega) (by omega)

/-- Divisibility respects congruent values. No modular arithmetic tactic is used. -/
theorem dvd_congr {d a b : Int} (h : d ∣ a - b) : (d ∣ a ↔ d ∣ b) := by
  constructor
  · intro ha
    have := Int.dvd_sub ha h
    convert this using 1 <;> ring
  · intro hb
    have := Int.dvd_add h hb
    convert this using 1 <;> ring

theorem term_difference_dvd [DecidableEq α] (name : α) (term : LTerm α)
    (values : Assignment α) {d x y : Int} (h : d ∣ x - y) :
    d ∣ term.denote (values.bind name x) - term.denote (values.bind name y) := by
  rw [term_bind, term_bind]
  convert Int.dvd_mul_of_dvd_right (b := (splitVar name term).1) h using 1 <;> ring

/-- Divisibility atoms have any multiple of their declared modulus as a period.
    A zero coefficient needs no divisibility premise at all. -/
theorem divisibility_periodic [DecidableEq α] (name : α) (term : LTerm α)
    (values : Assignment α) (k delta : Nat) (x y : Int)
    (covered : (if (splitVar name term).1 = 0 then 1 else k + 1) ∣ delta)
    (congruent : (delta : Int) ∣ x - y) :
    ((((k + 1 : Nat) : Int) ∣ term.denote (values.bind name x)) ↔
      (((k + 1 : Nat) : Int) ∣ term.denote (values.bind name y))) := by
  by_cases hz : (splitVar name term).1 = 0
  · simp only [term_bind, hz, zero_mul, zero_add]
  · have hd : k + 1 ∣ delta := by simpa [hz] using covered
    have hd' : ((k + 1 : Nat) : Int) ∣ (delta : Int) := Int.natCast_dvd_natCast.mpr hd
    exact dvd_congr (term_difference_dvd name term values (hd'.trans congruent))

/-- The negative-infinity formula is periodic, with the LCM computed by P14.
    The statement permits any larger common period, which makes induction local. -/
theorem minusInfinity_periodic [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) (delta : Nat) (covered : period name body ∣ delta)
    (x y : Int) (congruent : (delta : Int) ∣ x - y) :
    (minusInfinity name body).denote (values.bind name x) ↔
      (minusInfinity name body).denote (values.bind name y) := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term =>
      cases relation with
      | lt =>
          simp only [minusInfinity]
          split
          · simp only [atom_denote, remainder_bind]
          · simp only [truth_denote]
      | dvd k =>
          simp only [minusInfinity, atom_denote, Relation.denote]
          exact divisibility_periodic name term values k delta x y covered congruent
      | ndvd k =>
          simp only [minusInfinity, atom_denote, Relation.denote]
          exact not_congr (divisibility_periodic name term values k delta x y covered congruent)
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      have hl : period name left ∣ delta :=
        (Int.natAbs_dvd_lcm_left (period name left : Int) (period name right : Int)).trans covered
      have hr : period name right ∣ delta :=
        (Int.natAbs_dvd_lcm_right (period name left : Int) (period name right : Int)).trans covered
      simp only [minusInfinity, conj_denote, disj_denote, ihLeft hl, ihRight hr]

/-- Far enough to the left, every inequality has stabilized. The threshold may
    depend on the remaining free variables; the algorithm need not compute it. -/
theorem minusInfinity_eventually [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α) :
    ∃ threshold : Int, ∀ x ≤ threshold,
      body.denote (values.bind name x) ↔
        (minusInfinity name body).denote (values.bind name x) := by
  induction body with
  | tru => exact ⟨0, fun _ _ => Iff.rfl⟩
  | fls => exact ⟨0, fun _ _ => Iff.rfl⟩
  | atom relation term =>
      cases relation with
      | lt =>
          rcases unit with hz | hp | hn
          · refine ⟨0, ?_⟩
            intro x hx
            simp only [minusInfinity, hz, ↓reduceIte, QF.denote, atom_denote,
              remainder_bind]
            rw [term_bind name term values x, hz, zero_mul, zero_add]
          · refine ⟨-(splitVar name term).2.denote values - 1, ?_⟩
            intro x hx
            simp only [minusInfinity, hp, show (1 : Int) ≠ 0 by decide, ↓reduceIte,
              truth_denote, decide_eq_true_eq, QF.denote, Relation.denote, term_bind, hp]
            omega
          · refine ⟨(splitVar name term).2.denote values, ?_⟩
            intro x hx
            simp only [minusInfinity, hn, show (-1 : Int) ≠ 0 by decide, ↓reduceIte,
              truth_denote, decide_eq_true_eq, QF.denote, Relation.denote, term_bind, hn]
            omega
      | dvd k | ndvd k =>
          exact ⟨0, fun x _ => (atom_denote _ term (values.bind name x)).symm⟩
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      obtain ⟨a, ha⟩ := ihLeft unit.1
      obtain ⟨b, hb⟩ := ihRight unit.2
      refine ⟨min a b, ?_⟩
      intro x hx
      have hxa : x ≤ a := le_trans hx (min_le_left _ _)
      have hxb : x ≤ b := le_trans hx (min_le_right _ _)
      simp only [QF.denote, minusInfinity, conj_denote, disj_denote, ← ha x hxa, ← hb x hxb]

/-- The 1-based representative used by `project`, including residue zero. -/
theorem residue_exists (delta : Nat) (positive : 0 < delta) (x : Int) :
    ∃ j : Nat, j < delta ∧ (delta : Int) ∣ ((j + 1 : Nat) : Int) - x := by
  let r := (x - 1) % (delta : Int)
  have hp : (0 : Int) < (delta : Int) := by omega
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr1 : r < (delta : Int) := Int.emod_lt_of_pos _ hp
  refine ⟨r.toNat, by omega, ?_⟩
  have hc : (r.toNat : Int) = r := Int.toNat_of_nonneg hr0
  have hd := Int.dvd_sub_self_of_emod_eq (a := x - 1) (b := (delta : Int)) (c := r) rfl
  convert hd using 1 <;> push_cast <;> rw [hc] <;> ring

/-- Every residue class has representatives below every integer threshold. -/
theorem residue_below (delta : Nat) (positive : 0 < delta) (z threshold : Int) :
    ∃ x : Int, x ≤ threshold ∧ (delta : Int) ∣ x - z := by
  let k := max (z - threshold) 0 + 1
  have hd : (1 : Int) ≤ (delta : Int) := by omega
  have hk : 0 < k := by dsimp [k]; omega
  refine ⟨z - (delta : Int) * k, ?_, ?_⟩
  · have hmax := le_max_left (z - threshold) 0
    have hprod := mul_nonneg (show 0 ≤ (delta : Int) - 1 by omega) (le_of_lt hk)
    dsimp [k] at hk hprod ⊢
    nlinarith
  · refine ⟨-k, ?_⟩
    ring

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
