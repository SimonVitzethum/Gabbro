module

public import Core.Ast.Aggregate.Runtime

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def variantActual : (type : Option (Ty .value)) → Option Dynamisch → Option (Wert (type.getD .productEnd))
  | none, _ => some PUnit.unit
  | some type, value => value.bind (wertAls type)

def variantCase : (types : List (Option (Ty .value))) → Wert (variantLayout types) → Nat × Option Dynamisch
  | [], value => Empty.elim value
  | head :: _, .inl payload =>
    (0, match head with
      | none => none
      | some type => some ⟨type, payload⟩)
  | _ :: tail, .inr payload =>
    let (index, value) := variantCase tail payload
    (index + 1, value)

end Gabbro.Core.Ast.Semantik
