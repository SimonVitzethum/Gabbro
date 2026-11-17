module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Reduce.Connectives

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce

def universal [DecidableEq α] (key : α) (body : LProp α) : Equivalent (.all key body) :=
  match body with
  | .tru => ⟨.tru, fun _ => ⟨fun _ _ => trivial, fun _ => trivial⟩⟩
  | .fls => ⟨.fls, fun _ => ⟨False.elim, fun invalid => invalid 0⟩⟩
  | .imp guard result =>
      match eliminateDefinition key guard result with
      | some simplified => simplified
      | none => ⟨.all key (.imp guard result), fun _ => Iff.rfl⟩
  | body => ⟨.all key body, fun _ => Iff.rfl⟩

def existential [DecidableEq α] (key : α) (body : LProp α) : Equivalent (.ex key body) :=
  match body with
  | .tru => ⟨.tru, fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩⟩
  | .fls => ⟨.fls, fun _ => ⟨False.elim, fun ⟨_, invalid⟩ => invalid⟩⟩
  | body => ⟨.ex key body, fun _ => Iff.rfl⟩

/-- Fold truth and discharge explicit equality binders. Remaining integer
    quantifiers stay in LProp for the single verified Cooper decision. -/
def normalizeOnce [DecidableEq α] : (body : LProp α) → Equivalent body
  | .tru => ⟨.tru, fun _ => Iff.rfl⟩
  | .fls => ⟨.fls, fun _ => Iff.rfl⟩
  | .eq left right => equality left right
  | .le left right => lessEqual left right
  | .lt left right => lessThan left right
  | .dvd divisor term => ⟨.dvd divisor term, fun _ => Iff.rfl⟩
  | .not body =>
      let inner := normalizeOnce body
      let result := negation inner.val
      ⟨result.val, fun values => (result.property values).trans (not_congr (inner.property values))⟩
  | .and left right =>
      let a := normalizeOnce left
      let b := normalizeOnce right
      let result := conjunction a.val b.val
      ⟨result.val, fun values => (result.property values).trans (and_congr (a.property values) (b.property values))⟩
  | .or left right =>
      let a := normalizeOnce left
      let b := normalizeOnce right
      let result := disjunction a.val b.val
      ⟨result.val, fun values => (result.property values).trans (or_congr (a.property values) (b.property values))⟩
  | .imp left right =>
      let a := normalizeOnce left
      let b := normalizeOnce right
      let result := implication a.val b.val
      ⟨result.val, fun values => (result.property values).trans (imp_congr (a.property values) (b.property values))⟩
  | .all key body =>
      let inner := normalizeOnce body
      let result := universal key inner.val
      ⟨result.val, fun values => (result.property values).trans
        ⟨fun valid value => (inner.property _).mp (valid value),
         fun valid value => (inner.property _).mpr (valid value)⟩⟩
  | .ex key body =>
      let inner := normalizeOnce body
      let result := existential key inner.val
      ⟨result.val, fun values => (result.property values).trans
        ⟨fun ⟨value, valid⟩ => ⟨value, (inner.property _).mp valid⟩,
         fun ⟨value, valid⟩ => ⟨value, (inner.property _).mpr valid⟩⟩⟩

/-- The pass allowance limits optimization work, never the semantic guarantee.
    Every intermediate result is equivalent to the full original formula. -/
def normalize [DecidableEq α] (rounds : Nat) (body : LProp α) : Equivalent body :=
  match rounds with
  | 0 => ⟨body, fun _ => Iff.rfl⟩
  | rounds + 1 =>
      let head := normalizeOnce body
      if head.val = body then head
      else
        let tail := normalize rounds head.val
        ⟨tail.val, fun values => (tail.property values).trans (head.property values)⟩

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce
