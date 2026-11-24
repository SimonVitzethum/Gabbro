module

public import Core.Ast.Aggregate.Runtime

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def variantActual : (type : Option (Ty .value)) → Option Dynamisch → Option (Wert (type.getD .productEnd))
  | none, _ => some PUnit.unit
  | some type, value => value.bind (wertAls type)

def variantPayload : (type : Option (Ty .value)) → Wert (type.getD .productEnd) → Option Dynamisch
  | none, _ => none
  | some type, value => some ⟨type, value⟩

def variantCase : (types : List (Option (Ty .value))) → Wert (variantLayout types) → Nat × Option Dynamisch
  | [], value => Empty.elim value
  | head :: tail, value =>
    let sum : Sum (Wert (head.getD .productEnd)) (Wert (variantLayout tail)) := value
    match sum with
    | .inl payload => (0, variantPayload head payload)
    | .inr rest =>
      let (index, payload) := variantCase tail rest
      (index + 1, payload)

end Gabbro.Core.Ast.Semantik
