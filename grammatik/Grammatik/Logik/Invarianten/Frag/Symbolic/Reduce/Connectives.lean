module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Reduce.Definition

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce

abbrev Equivalent [DecidableEq α] (body : LProp α) :=
  { formula : LProp α // ∀ values, formula.denote values ↔ body.denote values }

def conjunction [DecidableEq α] (left right : LProp α) : Equivalent (.and left right) :=
  match left, right with
  | .tru, right => ⟨right, fun _ => by simp only [LProp.denote, true_and]⟩
  | left, .tru => ⟨left, fun _ => by simp only [LProp.denote, and_true]⟩
  | .fls, _ => ⟨.fls, fun _ => by simp only [LProp.denote, false_and]⟩
  | _, .fls => ⟨.fls, fun _ => by simp only [LProp.denote, and_false]⟩
  | left, right => ⟨.and left right, fun _ => Iff.rfl⟩

def disjunction [DecidableEq α] (left right : LProp α) : Equivalent (.or left right) :=
  match left, right with
  | .tru, _ => ⟨.tru, fun _ => by simp only [LProp.denote, true_or]⟩
  | _, .tru => ⟨.tru, fun _ => by simp only [LProp.denote, or_true]⟩
  | .fls, right => ⟨right, fun _ => by simp only [LProp.denote, false_or]⟩
  | left, .fls => ⟨left, fun _ => by simp only [LProp.denote, or_false]⟩
  | left, right => ⟨.or left right, fun _ => Iff.rfl⟩

def negation [DecidableEq α] (body : LProp α) : Equivalent (.not body) :=
  match body with
  | .tru => ⟨.fls, fun _ => by simp only [LProp.denote, not_true_eq_false]⟩
  | .fls => ⟨.tru, fun _ => by simp only [LProp.denote, not_false_eq_true]⟩
  | .not inner => ⟨inner, fun _ =>
      ⟨fun valid rejected => rejected valid,
       fun valid => Classical.byContradiction (fun rejected => valid rejected)⟩⟩
  | body => ⟨.not body, fun _ => Iff.rfl⟩

/-- A guarded obligation that is already an unconditional conjunct needs no
    arithmetic elimination. This also preserves inconsistent guards exactly. -/
def conjunct [DecidableEq α] (guard goal : LProp α) :
    Option (PLift (∀ values, guard.denote values → goal.denote values)) :=
  if same : guard = goal then some ⟨fun _ valid => same ▸ valid⟩
  else
    match guard with
    | .and left right =>
        match conjunct left goal with
        | some found => some ⟨fun values valid => found.down values valid.1⟩
        | none => do
            let found ← conjunct right goal
            return ⟨fun values valid => found.down values valid.2⟩
    | _ => none
termination_by structural guard

def implication [DecidableEq α] (left right : LProp α) : Equivalent (.imp left right) :=
  match left, right with
  | .tru, right => ⟨right, fun _ => by simp only [LProp.denote, true_implies]⟩
  | .fls, _ => ⟨.tru, fun _ => by simp only [LProp.denote, false_implies]⟩
  | _, .tru => ⟨.tru, fun _ => ⟨fun _ _ => trivial, fun _ => trivial⟩⟩
  | left, .imp guard body => ⟨.imp (.and left guard) body, fun values => by
      change ((_ ∧ _) → _) ↔ (_ → _ → _)
      exact ⟨fun valid a b => valid ⟨a, b⟩, fun valid both => valid both.1 both.2⟩⟩
  | left, right =>
      match conjunct left right with
      | some found => ⟨.tru, fun values => ⟨fun _ => found.down values, fun _ => trivial⟩⟩
      | none => ⟨.imp left right, fun _ => Iff.rfl⟩

def truth [DecidableEq α] (value : Bool) : LProp α := if value then .tru else .fls

theorem truth_denote [DecidableEq α] (value : Bool) (values : Assignment α) :
    (truth value).denote values ↔ value = true := by cases value <;> simp [truth, LProp.denote]

def equality [DecidableEq α] (left right : LTerm α) : Equivalent (.eq left right) :=
  match a : left.constant?, b : right.constant? with
  | some x, some y => ⟨truth (decide (x = y)), fun values => by
      rw [truth_denote, decide_eq_true_eq]
      change x = y ↔ left.denote values = right.denote values
      rw [LTerm.constant?_sound a, LTerm.constant?_sound b]⟩
  | _, _ =>
      if same : left = right then ⟨.tru, fun _ => by simp only [same, LProp.denote]⟩
      else ⟨.eq left right, fun _ => Iff.rfl⟩

def lessEqual [DecidableEq α] (left right : LTerm α) : Equivalent (.le left right) :=
  match a : left.constant?, b : right.constant? with
  | some x, some y => ⟨truth (decide (x ≤ y)), fun values => by
      rw [truth_denote, decide_eq_true_eq]
      change x ≤ y ↔ left.denote values ≤ right.denote values
      rw [LTerm.constant?_sound a, LTerm.constant?_sound b]⟩
  | _, _ =>
      if same : left = right then ⟨.tru, fun _ => by simp only [same, LProp.denote, Int.le_refl]⟩
      else ⟨.le left right, fun _ => Iff.rfl⟩

def lessThan [DecidableEq α] (left right : LTerm α) : Equivalent (.lt left right) :=
  match a : left.constant?, b : right.constant? with
  | some x, some y => ⟨truth (decide (x < y)), fun values => by
      rw [truth_denote, decide_eq_true_eq]
      change x < y ↔ left.denote values < right.denote values
      rw [LTerm.constant?_sound a, LTerm.constant?_sound b]⟩
  | _, _ =>
      if same : left = right then ⟨.fls, fun _ => by
        rw [same]
        exact ⟨False.elim, Int.lt_irrefl _⟩⟩
      else ⟨.lt left right, fun _ => Iff.rfl⟩

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce
