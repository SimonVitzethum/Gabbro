module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Reduce.Normalize

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce

/-- A partial evaluation carries its proof. Sampling a universal binder can
    refute it, but can never establish it; existential sampling is dual. -/
inductive Verdict (claim : Prop) where
  | yes (valid : claim)
  | no (invalid : ¬ claim)
  | unknown

def verdict (claim : Prop) [Decidable claim] : Verdict claim :=
  if valid : claim then .yes valid else .no valid

def evaluate [DecidableEq α] : (body : LProp α) → (values : Assignment α) → Verdict (body.denote values)
  | .tru, _ => .yes trivial
  | .fls, _ => .no id
  | .eq left right, values => verdict (left.denote values = right.denote values)
  | .le left right, values => verdict (left.denote values ≤ right.denote values)
  | .lt left right, values => verdict (left.denote values < right.denote values)
  | .dvd divisor term, values => verdict (divisor ∣ term.denote values)
  | .not body, values =>
      match evaluate body values with
      | .yes valid => .no (fun rejected => rejected valid)
      | .no invalid => .yes invalid
      | .unknown => .unknown
  | .and left right, values =>
      match evaluate left values, evaluate right values with
      | .no invalid, _ => .no (fun valid => invalid valid.1)
      | _, .no invalid => .no (fun valid => invalid valid.2)
      | .yes a, .yes b => .yes ⟨a, b⟩
      | _, _ => .unknown
  | .or left right, values =>
      match evaluate left values, evaluate right values with
      | .yes valid, _ => .yes (Or.inl valid)
      | _, .yes valid => .yes (Or.inr valid)
      | .no a, .no b => .no (fun valid => valid.elim a b)
      | _, _ => .unknown
  | .imp left right, values =>
      match evaluate left values, evaluate right values with
      | .no invalid, _ => .yes (fun valid => False.elim (invalid valid))
      | _, .yes valid => .yes (fun _ => valid)
      | .yes valid, .no invalid => .no (fun implication => invalid (implication valid))
      | _, _ => .unknown
  | .all key body, values =>
      match evaluate body (values.bind key 0) with
      | .no invalid => .no (fun valid => invalid (valid 0))
      | _ => .unknown
  | .ex key body, values =>
      match evaluate body (values.bind key 0) with
      | .yes valid => .yes ⟨0, valid⟩
      | _ => .unknown

theorem evaluate_true [DecidableEq α] (body : LProp α) (values : Assignment α) (shape : body = .tru) :
    ∃ proof, evaluate body values = .yes proof := by
  subst body
  exact ⟨trivial, rfl⟩

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce
