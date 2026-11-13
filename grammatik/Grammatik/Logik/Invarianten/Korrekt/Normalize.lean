module

public import Grammatik.Logik.Invarianten.Korrekt.Terms
public import Grammatik.Logik.Invarianten.Elim.Cooper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

theorem coefficientLcm_pos [DecidableEq α] (name : α) (body : QF α) :
    0 < coefficientLcm name body := by
  induction body with
  | tru => decide
  | fls => decide
  | atom relation term =>
      simp only [coefficientLcm]
      split
      · omega
      · exact Int.natAbs_pos.mpr ‹_›
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      exact Int.lcm_pos (by omega) (by omega)

/-- Scaling a divisibility test by a strictly positive factor is reversible. -/
theorem scaled_divisibility (k factor : Nat) (positive : 0 < factor) (value : Int) :
    (((((k + 1) * factor - 1) + 1 : Nat) : Int) ∣ (factor : Int) * value) ↔
      ((k + 1 : Nat) : Int) ∣ value := by
  have hp : 0 < (k + 1) * factor := Nat.mul_pos (by omega) positive
  have he : (k + 1) * factor - 1 + 1 = (k + 1) * factor := by omega
  rw [he, Int.natCast_mul, mul_comm (((k + 1 : Nat) : Int))]
  exact Int.mul_dvd_mul_iff_left (by omega)

/-- Coefficients are normalized at the actual change of variable `y = m*x`.
    The premise is arithmetic coverage by m, not a semantic certificate. -/
theorem normalizeAtom_denote [DecidableEq α] (name : α) (multiple : Nat)
    (relation : Relation) (term : LTerm α) (positive : 0 < multiple)
    (covered : (splitVar name term).1 = 0 ∨ (splitVar name term).1.natAbs ∣ multiple)
    (values : Assignment α) (x : Int) :
    (normalizeAtom name multiple relation term).denote
        (values.bind name ((multiple : Int) * x)) ↔
      relation.denote (term.denote (values.bind name x)) := by
  by_cases hz : (splitVar name term).1 = 0
  · simp [normalizeAtom, hz, atom_denote, remainder_bind, term_bind]
  · have hd : (splitVar name term).1.natAbs ∣ multiple := covered.resolve_left hz
    have ha : 0 < (splitVar name term).1.natAbs := Int.natAbs_pos.mpr hz
    have hf : 0 < multiple / (splitVar name term).1.natAbs :=
      Nat.div_pos (Nat.le_of_dvd positive hd) ha
    have hm : ((multiple / (splitVar name term).1.natAbs : Nat) : Int) *
        ((splitVar name term).1.natAbs : Int) = (multiple : Int) := by
      exact_mod_cast Nat.div_mul_cancel hd
    have hs : (if (splitVar name term).1 < 0 then (-1 : Int) else 1) *
        ((multiple : Int) * x) =
        ((multiple / (splitVar name term).1.natAbs : Nat) : Int) * ((splitVar name term).1 * x) := by
      by_cases hn : (splitVar name term).1 < 0
      · have habs := Int.ofNat_natAbs_of_nonpos (by omega : (splitVar name term).1 ≤ 0)
        simp only [hn, ↓reduceIte]
        rw [habs] at hm
        have hmul : ((multiple / (splitVar name term).1.natAbs : Nat) : Int) *
            (splitVar name term).1 = -(multiple : Int) := by nlinarith [hm]
        calc
          -1 * ((multiple : Int) * x) = -(multiple : Int) * x := by ring
          _ = (((multiple / (splitVar name term).1.natAbs : Nat) : Int) *
              (splitVar name term).1) * x := by rw [hmul]
          _ = _ := by ring
      · have habs := Int.natAbs_of_nonneg (by omega : 0 ≤ (splitVar name term).1)
        simp only [hn, ↓reduceIte]
        rw [habs] at hm
        calc
          1 * ((multiple : Int) * x) = (multiple : Int) * x := by ring
          _ = (((multiple / (splitVar name term).1.natAbs : Nat) : Int) *
              (splitVar name term).1) * x := by rw [hm]
          _ = _ := by ring
    have ht : (addTerm
          (scaleTerm (if (splitVar name term).1 < 0 then -1 else 1) (.var name))
          (scaleTerm ((multiple / (splitVar name term).1.natAbs : Nat) : Int) (splitVar name term).2)).denote
          (values.bind name ((multiple : Int) * x)) =
        ((multiple / (splitVar name term).1.natAbs : Nat) : Int) * term.denote (values.bind name x) := by
      simp only [addTerm_denote, scaleTerm_denote, LTerm.denote, bind_same, remainder_bind]
      rw [hs, term_bind]
      ring
    cases relation with
    | lt =>
        simp only [normalizeAtom, hz, ↓reduceIte, atom_denote, ht, Relation.denote]
        have hf' : (0 : Int) < ((multiple / (splitVar name term).1.natAbs : Nat) : Int) := by omega
        simpa only [mul_zero] using (Int.mul_lt_mul_left
          (a := ((multiple / (splitVar name term).1.natAbs : Nat) : Int))
          (b := term.denote (values.bind name x)) (c := 0) hf')
    | dvd k =>
        simp only [normalizeAtom, hz, ↓reduceIte, atom_denote, ht, Relation.denote]
        exact scaled_divisibility k _ hf _
    | ndvd k =>
        simp only [normalizeAtom, hz, ↓reduceIte, atom_denote, ht, Relation.denote]
        exact not_congr (scaled_divisibility k _ hf _)

theorem normalizeCoefficients_denote [DecidableEq α] (name : α) (multiple : Nat)
    (body : QF α) (positive : 0 < multiple) (covered : coefficientLcm name body ∣ multiple)
    (values : Assignment α) (x : Int) :
    (normalizeCoefficients name multiple body).denote
        (values.bind name ((multiple : Int) * x)) ↔ body.denote (values.bind name x) := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term =>
      apply normalizeAtom_denote name multiple relation term positive _ values x
      by_cases hz : (splitVar name term).1 = 0
      · exact Or.inl hz
      · exact Or.inr (by simpa [coefficientLcm, hz] using covered)
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      have hl : coefficientLcm name left ∣ multiple :=
        (Int.natAbs_dvd_lcm_left (coefficientLcm name left : Int)
          (coefficientLcm name right : Int)).trans covered
      have hr : coefficientLcm name right ∣ multiple :=
        (Int.natAbs_dvd_lcm_right (coefficientLcm name left : Int)
          (coefficientLcm name right : Int)).trans covered
      simp only [normalizeCoefficients, conj_denote, disj_denote, QF.denote,
        ihLeft hl, ihRight hr]

theorem normalizeCoefficients_unit [DecidableEq α] (name : α) (multiple : Nat)
    (body : QF α) : UnitCoefficients name (normalizeCoefficients name multiple body) := by
  induction body with
  | tru => trivial
  | fls => trivial
  | atom relation term =>
      unfold normalizeCoefficients normalizeAtom
      split
      · apply unit_atom
        cases relation <;> simp [UnitCoefficients]
      · apply unit_atom
        cases relation with
        | lt =>
            simp only [UnitCoefficients, addTerm_coefficient, scaleTerm_coefficient,
              remainder_coefficient, splitVar, if_pos rfl]
            split <;> simp
        | dvd k => trivial
        | ndvd k => trivial
  | conj left right ihLeft ihRight => exact unit_conj name _ _ ihLeft ihRight
  | disj left right ihLeft ihRight => exact unit_disj name _ _ ihLeft ihRight

theorem normalize_unit [DecidableEq α] (name : α) (body : QF α) :
    UnitCoefficients name (normalize name body) :=
  unit_conj name _ _ (unit_atom name _ _ (by trivial))
    (normalizeCoefficients_unit name _ body)

/-- Multiplication by the LCM is a bijection onto its integer multiples. -/
theorem normalize_exists [DecidableEq α] (name : α) (body : QF α) (values : Assignment α) :
    (∃ x : Int, (normalize name body).denote (values.bind name x)) ↔
      ∃ x : Int, body.denote (values.bind name x) := by
  let m := coefficientLcm name body
  have hp : 0 < m := coefficientLcm_pos name body
  have hm : m - 1 + 1 = m := by omega
  have he (x : Int) := normalizeCoefficients_denote name m body hp (dvd_refl m) values x
  simp only [normalize, conj_denote, atom_denote, Relation.denote, LTerm.denote, bind_same]
  change (∃ y : Int, ((m - 1 + 1 : Nat) : Int) ∣ y ∧
    (normalizeCoefficients name m body).denote (values.bind name y)) ↔ _
  rw [hm]
  constructor
  · rintro ⟨y, ⟨x, hx⟩, hbody⟩
    exact ⟨x, (he x).mp (by simpa [hx] using hbody)⟩
  · rintro ⟨x, hbody⟩
    exact ⟨(m : Int) * x, ⟨x, rfl⟩, (he x).mpr hbody⟩

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
