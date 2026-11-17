module

public import Grammatik.Logik.Invarianten.VC.Formula
public import Grammatik.Logik.Invarianten.Korrekt.Terms

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce

open Elim Elim.Korrekt

theorem termKeys_eq_variables (term : LTerm α) : VC.termKeys term = term.variables := by
  induction term <;> simp_all only [VC.termKeys, LTerm.variables]

theorem term_bind_absent [DecidableEq α] (term : LTerm α) (key : α)
    (absent : key ∉ term.variables) (values : Assignment α) (value : Int) :
    term.denote (values.bind key value) = term.denote values := by
  apply VC.termKeys_congr
  intro other member
  rw [termKeys_eq_variables] at member
  have different : other ≠ key := by
    intro same
    subst other
    exact absent member
  simp only [Assignment.bind, different, ↓reduceIte]

theorem bind_commute [DecidableEq α] (values : Assignment α) (first last : α)
    (different : first ≠ last) (a b : Int) :
    (values.bind first a).bind last b = (values.bind last b).bind first a := by
  funext key
  by_cases left : key = first
  · subst key
    simp only [Assignment.bind, different, ↓reduceIte]
  · by_cases right : key = last
    · subst key
      simp only [Assignment.bind, Ne.symm different, ↓reduceIte]
    · simp only [Assignment.bind, left, right, ↓reduceIte]

/-- Capture-checked substitution on quantified formulas. A conflicting inner
    binder refuses this optimization; the caller retains the original formula. -/
def substitute [DecidableEq α] (key : α) (term : LTerm α) :
    (body : LProp α) → Option { result : LProp α // ∀ values,
      result.denote values ↔ body.denote (values.bind key (term.denote values)) }
  | .tru => some ⟨.tru, fun _ => Iff.rfl⟩
  | .fls => some ⟨.fls, fun _ => Iff.rfl⟩
  | .le left right => some ⟨.le (substTerm key term left) (substTerm key term right), fun values => by
      change _ ≤ _ ↔ _ ≤ _
      rw [substTerm_denote, substTerm_denote]⟩
  | .lt left right => some ⟨.lt (substTerm key term left) (substTerm key term right), fun values => by
      change _ < _ ↔ _ < _
      rw [substTerm_denote, substTerm_denote]⟩
  | .eq left right => some ⟨.eq (substTerm key term left) (substTerm key term right), fun values => by
      change _ = _ ↔ _ = _
      rw [substTerm_denote, substTerm_denote]⟩
  | .dvd divisor source => some ⟨.dvd divisor (substTerm key term source), fun values => by
      change divisor ∣ _ ↔ divisor ∣ _
      rw [substTerm_denote]⟩
  | .not body => do
      let body' ← substitute key term body
      return ⟨.not body'.val, fun values => not_congr (body'.property values)⟩
  | .and left right => do
      let a ← substitute key term left
      let b ← substitute key term right
      return ⟨.and a.val b.val, fun values => and_congr (a.property values) (b.property values)⟩
  | .or left right => do
      let a ← substitute key term left
      let b ← substitute key term right
      return ⟨.or a.val b.val, fun values => or_congr (a.property values) (b.property values)⟩
  | .imp left right => do
      let a ← substitute key term left
      let b ← substitute key term right
      return ⟨.imp a.val b.val, fun values => imp_congr (a.property values) (b.property values)⟩
  | .all name body =>
      if same : name = key then
        some ⟨.all name body, fun values => by
          subst name
          simp only [LProp.denote, bind_bind]⟩
      else if absent : name ∉ term.variables then do
        let body' ← substitute key term body
        return ⟨.all name body'.val, fun values => by
          change (∀ value, body'.val.denote (values.bind name value)) ↔ _
          simp only [body'.property, term_bind_absent term name absent,
            bind_commute values name key same, LProp.denote]⟩
      else none
  | .ex name body =>
      if same : name = key then
        some ⟨.ex name body, fun values => by
          subst name
          simp only [LProp.denote, bind_bind]⟩
      else if absent : name ∉ term.variables then do
        let body' ← substitute key term body
        return ⟨.ex name body'.val, fun values => by
          change (∃ value, body'.val.denote (values.bind name value)) ↔ _
          simp only [body'.property, term_bind_absent term name absent,
            bind_commute values name key same, LProp.denote]⟩
      else none

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce
