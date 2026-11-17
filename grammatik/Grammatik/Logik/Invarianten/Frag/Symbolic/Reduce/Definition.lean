module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Reduce.Substitution

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce

open Elim.Korrekt

structure Definition [DecidableEq α] (key : α) (guard : LProp α) where
  term : LTerm α
  absent : key ∉ term.variables
  sound : ∀ values, guard.denote values → values key = term.denote values

def equalityDefinition [DecidableEq α] (key : α) (left right : LTerm α) :
    Option (Definition key (.eq left right)) :=
  if same : left = .var key then
    if absent : key ∉ right.variables then some {
      term := right
      absent := absent
      sound := fun values valid => by
        change left.denote values = right.denote values at valid
        rw [same] at valid
        exact valid }
    else none
  else if same : right = .var key then
    if absent : key ∉ left.variables then some {
      term := left
      absent := absent
      sound := fun values valid => by
        change left.denote values = right.denote values at valid
        rw [same] at valid
        exact valid.symm }
    else none
  else none

/-- Only unconditional equality conjuncts define a binder. Conditional
    initializer arms and contradictory postconditions are never assumed. -/
def definition [DecidableEq α] (key : α) : (guard : LProp α) → Option (Definition key guard)
  | .eq left right => equalityDefinition key left right
  | .and left right =>
      match definition key left with
      | some selected => some {
          term := selected.term, absent := selected.absent
          sound := fun values valid => selected.sound values valid.1 }
      | none => do
          let selected ← definition key right
          return {
            term := selected.term, absent := selected.absent
            sound := fun values valid => selected.sound values valid.2 }
  | _ => none

/-- Universal guarded definitions are discharged by capture-checked
    substitution. This is an equivalence, including unsatisfiable guards. -/
def eliminateDefinition [DecidableEq α] (key : α) (guard body : LProp α) :
    Option { result : LProp α // ∀ values,
      result.denote values ↔ (LProp.all key (.imp guard body)).denote values } := do
  let selected ← definition key guard
  let replaced ← substitute key selected.term (.imp guard body)
  return ⟨replaced.val, fun values => by
    change replaced.val.denote values ↔
      ∀ value, guard.denote (values.bind key value) → body.denote (values.bind key value)
    constructor
    · intro valid value guarded
      have same := selected.sound (values.bind key value) guarded
      rw [bind_same, term_bind_absent selected.term key selected.absent] at same
      rw [same] at guarded ⊢
      exact (replaced.property values).mp valid guarded
    · intro valid
      exact (replaced.property values).mpr (valid (selected.term.denote values))⟩

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce
