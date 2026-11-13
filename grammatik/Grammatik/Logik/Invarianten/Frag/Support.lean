module

public import Grammatik.Logik.Invarianten.Frag.Syntax

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

/-- Occurrences are retained in source order. The public observation list below
    removes duplicates only after collecting all free occurrences. -/
def LTerm.variables : LTerm α → List α
  | .var name => [name]
  | .konst _ => []
  | .add left right | .sub left right => left.variables ++ right.variables
  | .scale _ term => term.variables

/-- Exactly the free variables, including correct removal under shadowing. -/
def LProp.freeVariables [DecidableEq α] : LProp α → List α
  | .tru | .fls => []
  | .le left right | .lt left right | .eq left right => left.variables ++ right.variables
  | .dvd _ term => term.variables
  | .not body => body.freeVariables
  | .and left right | .or left right | .imp left right => left.freeVariables ++ right.freeVariables
  | .ex name body | .all name body => body.freeVariables.filter (fun key => decide (key ≠ name))

def LProp.keys [DecidableEq α] (formula : LProp α) : List α :=
  formula.freeVariables.eraseDups

theorem LProp.mem_keys [DecidableEq α] (formula : LProp α) (key : α) :
    key ∈ formula.keys ↔ key ∈ formula.freeVariables := by
  simp only [LProp.keys, List.mem_eraseDups]

end Gabbro.Grammatik.Invarianten.Frag
